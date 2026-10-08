import FCAppendix.Probability.GaussianPositivePart
import FCAppendix.Probability.StrictCDFConvergence
import FCAppendix.PayOnce.InactivePriceRecentering
import FCAppendix.PayOnce.InactiveClippedPriceMean
import FCAppendix.PayOnce.InactiveCentralEntry

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_gaussian_bid_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) :
    Tendsto (fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))+
        inactiveGaussianScale M F (k+1) g ρ t*y t) atTop
      (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) := by
  simpa only [zero_mul,add_zero] using (payOnce_inactive_population_price Γ B F g ρ h).2.add
    ((inactiveGaussianScale_tendsto_zero M F (k+1) g ρ h.population_grows).mul hy)

theorem payOnce_inactive_normalized_clipped_focal_secondMoment
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let X := fun t b r => (clippedFocalPrice (k+1) (C t) hn ell u b r-bar t)/
      inactiveGaussianScale M F (k+1) g ρ t
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      Measurable (X t b) ∧ MemLp (X t b) 2 (μ t) ∧ (∫ r, (X t b r)^2 ∂μ t) ≤ K := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  let σ := GaussianParameters.sigma μW (k+1) L
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hσ : 0 < σ := GaussianParameters.sigma_pos μW hn
    (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1 hlocal
  obtain ⟨K,hK,hbound⟩ := payOnce_inactive_clipped_focal_price_moments Γ B F g ρ h
    ell u hell hu (r := 2) (by norm_num)
  refine ⟨K/σ^2,by positivity,?_⟩
  filter_upwards [hbound,(payOnce_inactive_population_price Γ B F g ρ h).2.eventually
    (Ioo_mem_nhds hell hu),h.population_grows.eventually_gt_atTop 0] with t ht hbar hm b hb
  let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let a := KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ t
  have hs : 0 < s := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hm
  refine ⟨((measurable_clippedFocalPrice hn ell u b).sub_const a).div_const s,?_,?_⟩
  · have hh := (memLp_clipToInterval_sub μ (measurable_focalPrice (c := C t) hn b)
      ⟨hbar.1.le,hbar.2.le⟩ 2).const_mul s⁻¹
    simpa only [clippedFocalPrice,div_eq_mul_inv,mul_comm] using hh
  · have hh := (ht b hb).2
    norm_num only [rpow_two,sq_abs,neg_div,neg_neg,div_self,OfNat.ofNat_ne_zero,rpow_neg_one] at hh
    have he : (K/(M t:ℝ))/s^2=K/σ^2 := by
      change (K/(M t:ℝ))/(inactiveGaussianScale M F (k+1) g ρ t)^2 = _
      rw [inactiveGaussianScale_sq]
      have hmR : (M t:ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
      change (K/(M t:ℝ))/(σ^2/(M t:ℝ))=K/σ^2
      field_simp
    have hdiv := div_le_div_of_nonneg_right
      (show (∫ r, (clippedFocalPrice (k+1) (C t) hn ell u b r-a)^2 ∂μ) ≤ K/(M t:ℝ) from by
        simpa only [clippedFocalPrice,a,μ,div_eq_mul_inv] using hh) (sq_nonneg s)
    rw [he] at hdiv
    simpa only [div_pow,integral_div] using hdiv

theorem payOnce_inactive_clipped_focal_positivePart_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u)
    (b : ℕ → ℝ) (hb : ∀ᶠ t in atTop, 0 < b t)
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    Tendsto (fun t => ∫ r, max (y t-
      (clippedFocalPrice (k+1) (C t) hn ell u (b t) r-bar t)/inactiveGaussianScale M F (k+1) g ρ t) 0
      ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      atTop (𝓝 (gaussianSuccessPrimitive z)) := by
  dsimp only
  obtain ⟨K,_hK,hbound⟩ := payOnce_inactive_normalized_clipped_focal_secondMoment Γ B F g ρ h hlocal
    ell u hell hu
  apply gaussian_positivePart_moving_mean_tendsto _ _ K ?_ ?_ y hy
  · filter_upwards [hbound,hb] with t ht hbt
    exact ht (b t) hbt
  · intro x
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [payOnce_inactive_clipped_focal_price_gaussian_uniform_population
      Γ B F g ρ h hlocal ell u hell hu x ε hε,hb] with t ht hbt
    simpa only [Real.dist_eq] using ht (b t) hbt

theorem payOnce_inactive_entry_probability_gaussian
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ) (hb : ∀ᶠ t in atTop, 0 < b t) {y : ℝ}
    (hy : Tendsto (fun t => (b t-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 y)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => (Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | 0 < allocation (k+1) (C t) hn r (b t)}) atTop (𝓝 (cdf (gaussianReal 0 1) y)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let X := fun t (r : Fin (M t-1) → ℝ) => (focalPrice (k+1) (C t) hn (b t) r-bar t)/s t
  have hm t : Measurable (X t) := ((measurable_focalPrice hn (b t)).sub_const (bar t)).div_const (s t)
  letI : ∀ t, IsProbabilityMeasure ((μ t).map (X t)) :=
    fun t => Measure.isProbabilityMeasure_map (hm t).aemeasurable
  have hcdf x : Tendsto (fun t => cdf ((μ t).map (X t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [payOnce_inactive_focal_price_gaussian_uniform_population Γ B F g ρ h hlocal x ε hε,hb]
      with t ht hbt
    simpa only [Real.dist_eq] using ht (b t) hbt
  have hh := strictCDF_moving_threshold_tendsto (fun t => (μ t).map (X t))
    (fun z => cdf (gaussianReal 0 1) z) continuous_Φ hcdf _ hy
  apply hh.congr'
  filter_upwards [hb,h.population_grows.eventually_gt_atTop 0] with t hbt hmt
  rw [map_measureReal_apply (hm t) measurableSet_Iio]
  congr 1
  ext r
  change (focalPrice (k+1) (C t) hn (b t) r-bar t)/s t < (b t-bar t)/s t ↔ _
  rw [div_lt_div_iff_of_pos_right (payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt),
    sub_lt_sub_iff_right]
  exact (allocation_pos_iff_focalPrice_lt hn r hbt).symm

end FCAppendix.Bayes
