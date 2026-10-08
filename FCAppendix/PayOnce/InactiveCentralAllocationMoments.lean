import FCAppendix.PayOnce.InactiveCentralAllocationLaw
import FCAppendix.PayOnce.InactiveAllocationMoments
import FCAppendix.Probability.NormalizedMoments
import FCAppendix.Probability.GaussianPowerMoments

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelLawConvergence Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_allocation_evenMoment_bound
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) (j : ℕ) (hj : 1 ≤ j) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let s := inactiveGaussianScale M F (k+1) g ρ
    ∃ K : ℝ, ∀ᶠ t in atTop,
      (∫ r, (allocation (k+1) (C t) hn r (bar t+s t*y t)/s t)^(2*j)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) ≤ K := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  let σ := GaussianParameters.sigma μW (k+1) L
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let b := fun t => bar t+s t*y t
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let U : ℝ := ((k+1:ℕ):ℝ)/(L/2)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hσ : 0 < σ := GaussianParameters.sigma_pos μW hn hL hlocal
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hb : Tendsto b atTop (𝓝 L) := payOnce_inactive_gaussian_bid_tendsto Γ B F g ρ h y hy
  obtain ⟨K,_hK,hK⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h
    ((2*j:ℕ):ℝ) (by exact_mod_cast (show 1 ≤ 2*j by omega))
  refine ⟨2^(2*j)*(K/σ^(2*j)+(U*(|z|+1))^(2*j)),?_⟩
  filter_upwards [hK,hbar.eventually_const_lt (show L/2 < L by linarith),
    hb.eventually_const_lt (show L/2 < L by linarith),
    hy.abs.eventually (Iio_mem_nhds (show |z| < |z|+1 by linarith)),
    h.population_grows.eventually_gt_atTop 0] with t ht hbart hbt hyt hmt
  have hst : 0 < s t := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt
  have hbpos : 0 < b t := (by linarith : 0 < L/2).trans hbt
  let q := kernel (k+1) (b t) (bar t)
  have hq : |q|/s t ≤ U*(|z|+1) := by
    have hh := kernel_price_difference hn (show 0 < L/2 by linarith) hbart.le hbt.le (b t)
    have hh' : |q| ≤ U*|b t-bar t| := by
      simpa only [kernel_of_le (k+1) le_rfl,sub_zero,abs_sub_comm (bar t) (b t)] using hh
    have he : b t-bar t=s t*y t := by dsimp only [b]; ring
    rw [he,abs_mul,abs_of_pos hst] at hh'
    have hh'' : |q|/s t ≤ U*|y t| := (div_le_iff₀ hst).mpr (by nlinarith [hh'])
    exact hh''.trans (mul_le_mul_of_nonneg_left hyt.le (by dsimp only [U]; positivity))
  have hmR : (M t:ℝ) ≠ 0 := (Nat.cast_pos.mpr hmt).ne'
  have hscale : (s t)^(2*j)=σ^(2*j)/(M t:ℝ)^j := by
    rw [pow_mul,show (s t)^2=σ^2/(M t:ℝ) from inactiveGaussianScale_sq M F (k+1) g ρ t,
      div_pow,← pow_mul]
  have hid : -((2*j:ℕ):ℝ)/2=-(j:ℝ) := by push_cast; ring
  have hbound := (ht (b t) hbpos).2
  rw [hid,Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_natCast] at hbound
  simp only [Real.rpow_natCast] at hbound
  have hnormalized : (∫ r, |allocation (k+1) (C t) hn r (b t)-q|^(2*j) ∂μ t)/(s t)^(2*j)
      ≤ K/σ^(2*j) := by
    have hh := div_le_div_of_nonneg_right hbound (pow_nonneg hst.le (2*j))
    have he : (K*((M t:ℝ)^j)⁻¹)/(s t)^(2*j)=K/σ^(2*j) := by
      rw [hscale]
      field_simp [hmR,hσ.ne']
    rw [he] at hh
    exact hh
  exact integral_unitInterval_div_pow_le (μ t) _ (measurable_allocation_fixed_bid hn (b t))
    (fun r => allocation_bounds hn r (b t)) hst hq (2*j)
    (by simpa only [Real.rpow_natCast] using (ht (b t) hbpos).1) hnormalized

theorem payOnce_inactive_central_allocation_moment_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) (j : ℕ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let s := inactiveGaussianScale M F (k+1) g ρ
    Tendsto (fun t => (∫ r, (allocation (k+1) (C t) hn r (bar t+s t*y t))^j
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))/(s t)^j)
      atTop (𝓝 ((2/((((k+1:ℕ):ℝ)-1)*L))^j*(∫ Z : ℝ, (max (z-Z) 0)^j ∂gaussianReal 0 1))) := by
  dsimp only
  by_cases hj : j=0
  · subst j
    simp only [pow_zero,integral_const,probReal_univ,one_smul,div_one,mul_one]
    exact tendsto_const_nhds
  obtain ⟨K,hK⟩ := payOnce_inactive_central_allocation_evenMoment_bound Γ B F g ρ h hlocal y hy j (by omega)
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let b := fun t => bar t+s t*y t
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let α := 2/((((k+1:ℕ):ℝ)-1)*L)
  have hh := moment_tendsto_of_tendstoInDistribution μ (gaussianReal 0 1)
    (fun t r => allocation (k+1) (C t) hn r (b t)/s t) (fun Z => α*max (z-Z) 0)
    (payOnce_inactive_central_allocation_tendstoInDistribution Γ B F g ρ h hlocal y hy) j
    (fun t => memLp_unitInterval_div_pow (μ t) _ (measurable_allocation_fixed_bid hn (b t))
      (fun r => allocation_bounds hn r (b t)) (s t) j)
    (memLp_gaussian_positivePart_pow z α j) K hK
  simpa only [α,L,b,bar,s,μ,div_pow,integral_div,mul_pow,integral_const_mul] using hh

end FCAppendix.Bayes
