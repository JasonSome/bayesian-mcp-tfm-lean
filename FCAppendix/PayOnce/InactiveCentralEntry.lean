import FCAppendix.PayOnce.ClippedPriceCLT
import FCAppendix.PayOnce.DummyEntryTail
import FCAppendix.Probability.CorrelatedLoads

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set CommonList KernelTailEvent

theorem allocation_pos_iff_focalPrice_lt {N n c : ℕ} (hn : 2 ≤ n)
    (r : Fin N → ℝ) {b : ℝ} (hb : 0 < b) :
    0 < allocation n c hn r b ↔ focalPrice n c hn b r < b := by
  have hs := focalPrice_spec (c := c) hn b r hb
  rw [hs.2.2]
  have hnonneg := (kernel_bounds hn hs.1 b).1
  have hzero := kernel_eq_zero_iff n hn hb hs.1
  constructor
  · intro hp
    by_contra h
    have hz := hzero.mpr (le_of_not_gt h)
    linarith
  · intro hprice
    by_contra hp
    have hz := hzero.mp (le_antisymm (le_of_not_gt hp) hnonneg)
    linarith

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_entry_lower
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (R : ℝ) :
    ∃ cR : ℝ, 0 < cR ∧ ∀ᶠ t in atTop, ∀ b : ℝ,
      KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
        ((C t:ℝ)/(M t))-R/Real.sqrt (M t) ≤ b →
      0 < b ∧ cR ≤ (Measure.pi (fun _ : Fin (M t-1) =>
        (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | 0 < allocation (k+1) (C t) (by have hk := h.proposers_two; omega) r b} := by
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  let σ := GaussianParameters.sigma μW (k+1) L
  let x := -(R+1)/σ
  let bar := fun t => KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
    ((C t:ℝ)/(M t))
  have hn : 2 ≤ k+1 := by have hk := h.proposers_two; omega
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hσ : 0 < σ := GaussianParameters.sigma_pos μW hn hL hlocal
  have hΦ := CorrelatedLoads.gaussian_cdf_pos x
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hR : Tendsto (fun t => R/Real.sqrt (M t)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp h.population_grows))
  have hmin : Tendsto (fun t => bar t-R/Real.sqrt (M t)) atTop (𝓝 L) := by
    simpa only [sub_zero] using hbar.sub hR
  have hinside := (payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x).eventually
    (Ioo_mem_nhds (show L/2 < L by linarith) (show L < L+1 by linarith))
  have hCDF := payOnce_inactive_clipped_focal_price_gaussian_uniform_population Γ B F g ρ h hlocal
    (L/2) (L+1) (by linarith) (by linarith) x (cdf (gaussianReal 0 1) x/2) (by positivity)
  refine ⟨cdf (gaussianReal 0 1) x/2,by positivity,?_⟩
  filter_upwards [hCDF,hinside,hmin.eventually (eventually_gt_nhds hL),
    h.population_grows.eventually_gt_atTop 0] with t hc ht hminpos hm b hblower
  have hb : 0 < b := hminpos.trans_le hblower
  refine ⟨hb,?_⟩
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hm
  have hc' := hc b hb
  rw [cdf_standardized_clippedFocalPrice_eq hn _ b hs ht] at hc'
  have hlower : cdf (gaussianReal 0 1) x/2 ≤
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | (focalPrice (k+1) (C t) hn b r-bar t)/inactiveGaussianScale M F (k+1) g ρ t ≤ x} := by
    have hh := (abs_lt.mp hc').1
    linarith
  have hroot : 0 < Real.sqrt (M t) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have hTeq : inactiveGaussianPrice Γ F g ρ x t = bar t-(R+1)/Real.sqrt (M t) := by
    change bar t+(σ/Real.sqrt (M t))*(-(R+1)/σ) = _
    field_simp
    ring
  have hTb : inactiveGaussianPrice Γ F g ρ x t < b := by
    rw [hTeq,add_div]
    have hh : 0 < 1/Real.sqrt (M t) := one_div_pos.mpr hroot
    change bar t-R/Real.sqrt (M t) ≤ b at hblower
    linarith
  apply hlower.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro r hr
  apply (allocation_pos_iff_focalPrice_lt hn r hb).mpr
  have hp : focalPrice (k+1) (C t) hn b r ≤ inactiveGaussianPrice Γ F g ρ x t := by
    have hh := (div_le_iff₀ hs).mp hr
    change focalPrice (k+1) (C t) hn b r ≤ bar t+inactiveGaussianScale M F (k+1) g ρ t*x
    linarith
  exact hp.trans_lt hTb

theorem payOnce_inactive_central_entry_probability
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (R : ℝ) :
    ∃ cR : ℝ, 0 < cR ∧ ∀ᶠ t in atTop, ∀ b ∈ Icc
      (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
        ((C t:ℝ)/(M t))-R/Real.sqrt (M t))
      (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))),
      cR ≤ (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | 0 < allocation (k+1) (C t) (by have hk := h.proposers_two; omega) r b} := by
  obtain ⟨cR,hcR,he⟩ := payOnce_inactive_central_entry_lower Γ B F g ρ h hlocal R
  refine ⟨cR,hcR,?_⟩
  filter_upwards [he] with t ht b hb
  exact (ht b hb.1).2

end FCAppendix.Bayes
