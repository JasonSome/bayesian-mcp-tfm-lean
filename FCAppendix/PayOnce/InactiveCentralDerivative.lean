import FCAppendix.PayOnce.CentralDerivative
import FCAppendix.PayOnce.InactiveCentralPrice
import FCAppendix.PayOnce.AllocationFirstMoment

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.RareSuccessSlope
open PayOnce.KernelTailEvent
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_entry_allocation_mean_tendsto_zero
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => ∫ r, allocation (k+1) (C t) hn r (b t)
      ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      atTop (𝓝 0) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  change Tendsto b atTop (𝓝 L) at hb
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  obtain ⟨A,_hA,herror⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h 1 (by norm_num)
  have hδ : Tendsto (fun t => (M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := (1:ℝ)/2) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp h.population_grows)
  have hlim : Tendsto (fun t => ((k+1:ℕ):ℝ)/(L/2)*|bar t-b t|+
      A*(M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,mul_zero,zero_add] using
      (((hbar.sub hb).abs).const_mul (((k+1:ℕ):ℝ)/(L/2))).add (hδ.const_mul A)
  apply squeeze_zero' (Filter.Eventually.of_forall fun t =>
    integral_nonneg (fun r => (allocation_bounds hn r (b t)).1)) ?_ hlim
  filter_upwards [herror,hbar.eventually_const_lt (show L/2<L by linarith),
    hb.eventually_const_lt (show L/2<L by linarith)] with t he hbt hbb
  have hbp : 0 < b t := (half_pos hL).trans hbb
  have hbarp : 0 < bar t := (half_pos hL).trans hbt
  have hk := KernelLawConvergence.kernel_price_difference hn (half_pos hL) hbt.le hbb.le (b t)
  rw [kernel_of_le (k+1) le_rfl,sub_zero,abs_of_nonneg (kernel_bounds hn hbarp (b t)).1] at hk
  have hmom : (∫ r, |allocation (k+1) (C t) hn r (b t)-kernel (k+1) (b t) (bar t)| ∂μ t) ≤
      A*(M t:ℝ)^(-(1:ℝ)/2) := by simpa only [rpow_one] using (he (b t) hbp).2
  exact (mean_coverage_tail_le_of_error hn (μ t) hbarp hmom).1.trans (add_le_add hk le_rfl)

theorem payOnce_inactive_entry_derivative_error_tendsto_zero
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    Tendsto (fun t => b t*deriv (coverage (k+1) (C t) hn (μ t)) (b t)-
      phi (k+1) 0*(μ t).real {r | 0<allocation (k+1) (C t) hn r (b t)}) atTop (𝓝 0) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  obtain ⟨q,d,hq,hd,hown⟩ := payOnce_inactive_ownImpact_moments Γ B F g ρ h
  obtain ⟨K,hK,hLip⟩ := ResponseFactor.exists_lipschitz_phi hn
  have hN : Tendsto (fun t => M t-1) atTop atTop := (tendsto_sub_atTop_nat 1).comp h.population_grows
  have hNr : Tendsto (fun t => ((M t-1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hinv : Tendsto (fun t => ((k+1:ℕ):ℝ)^3/(q*((M t-1:ℕ):ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hNr.const_mul_atTop hq)
  have hexp : Tendsto (fun t => Real.exp (-d*((M t-1:ℕ):ℝ))) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hNr.const_mul_atTop hd)
  have hp := payOnce_inactive_entry_allocation_mean_tendsto_zero Γ B F g ρ h b hb
  have hlim : Tendsto (fun t => ((k+1:ℕ):ℝ)^2*(((k+1:ℕ):ℝ)^3/(q*((M t-1:ℕ):ℝ))+
      3*Real.exp (-d*((M t-1:ℕ):ℝ)))+
      K*(∫ r, allocation (k+1) (C t) hn r (b t) ∂μ t)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using
      ((hinv.add (hexp.const_mul 3)).const_mul (((k+1:ℕ):ℝ)^2)).add (hp.const_mul K)
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ hlim
  filter_upwards [hown,hb.eventually_const_lt hL] with t ht hbp
  obtain ⟨w,hw,hwb,_hgap,_hLp,hder,hwm⟩ := ht.2 (b t) hbp
  have hderiv : b t*deriv (coverage (k+1) (C t) hn (μ t)) (b t) =
      ∫ r, weightedSlope (k+1) (allocation (k+1) (C t) hn r (b t)) (w r) ∂μ t := by
    rw [hder.deriv]
    exact mul_div_cancel₀ _ hbp.ne'
  rw [hderiv]
  have hcmp := integral_weightedSlope_entry_error_le (μ t) hn
    (measurable_allocation_fixed_bid (c := C t) hn (b t)) hw
    (fun r => allocation_bounds hn r (b t)) hwb hK.le (fun r => by
      simpa only [sub_zero,abs_of_nonneg (allocation_bounds hn r (b t)).1] using
        hLip _ (allocation_bounds hn r (b t)) 0 (by constructor <;> norm_num))
  have hwmean := (hwm 1).2
  simp only [pow_one] at hwmean
  exact hcmp.trans (add_le_add (mul_le_mul_of_nonneg_left hwmean (sq_nonneg _)) le_rfl)

theorem payOnce_inactive_central_coverage_derivative
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)))
    {y : ℝ} (hy : Tendsto (fun t => (b t-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 y)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => deriv (coverage (k+1) (C t) hn
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))) (b t))
      atTop (𝓝 ((2*((k+1:ℕ):ℝ)/((((k+1:ℕ):ℝ)-1)*
        Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))*cdf (gaussianReal 0 1) y)) := by
  dsimp only
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  have he := payOnce_inactive_entry_derivative_error_tendsto_zero Γ B F g ρ h b hb
  have hp := (payOnce_inactive_entry_probability_gaussian Γ B F g ρ h hlocal b
    (hb.eventually_const_lt hL) hy).const_mul (phi (k+1) 0)
  have hh := (he.add hp).div hb hL.ne'
  simp only [sub_add_cancel,zero_add] at hh
  have hres := hh.congr' (show ∀ᶠ t in atTop, _ from by
    filter_upwards [hb.eventually_const_lt hL] with t ht
    exact mul_div_cancel_left₀ _ ht.ne')
  convert hres using 1
  congr 1
  simp only [phi_zero hn,div_eq_mul_inv,mul_inv_rev]
  ring

end FCAppendix.Bayes
