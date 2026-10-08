import FCAppendix.PayOnce.ScaledEntryExpectation
import FCAppendix.PayOnce.InactiveCentralPrice
import FCAppendix.PayOnce.InactiveInteriorExpectation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent
open PayOnce.KernelTaylor PayOnce.KernelEntryExpectation Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_test_mean
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z))
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) {D : ℝ}
    (hD : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ D)
    {d K : ℝ} (hK : 0 ≤ K) (hquad : ∀ p ∈ Icc (0:ℝ) 1, |ψ p-d*p| ≤ K*p^2) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let s := inactiveGaussianScale M F (k+1) g ρ
    Tendsto (fun t => (∫ r, ψ (allocation (k+1) (C t) hn r (bar t+s t*y t))
      ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))/s t)
      atTop (𝓝 ((d*(2/((((k+1:ℕ):ℝ)-1)*
        Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)))*gaussianSuccessPrimitive z)) := by
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
  let X := fun t => clippedFocalPrice (N := M t-1) (k+1) (C t) hn (3*L/4) (5*L/4) (b t)
  let α := d*(2/((((k+1:ℕ):ℝ)-1)*L))
  let Amean := fun t => (∫ r, ψ (allocation (k+1) (C t) hn r (b t)) ∂μ t)/s t
  let Bmean := fun t => (∫ r, ψ (kernel (k+1) (b t) (X t r)) ∂μ t)/s t
  let Pmean := fun t => α*(∫ r, max (y t-(X t r-bar t)/s t) 0 ∂μ t)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hσ : 0 < σ := GaussianParameters.sigma_pos μW hn hL hlocal
  have hell : 3*L/4<L := by linarith
  have hu : L<5*L/4 := by linarith
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hs : Tendsto s atTop (𝓝 0) := inactiveGaussianScale_tendsto_zero M F (k+1) g ρ h.population_grows
  have hb : Tendsto b atTop (𝓝 L) := payOnce_inactive_gaussian_bid_tendsto Γ B F g ρ h y hy
  have hbp : ∀ᶠ t in atTop, 0<b t := hb.eventually_const_lt hL
  have hbI : ∀ᶠ t in atTop, b t ∈ Icc (3*L/4) (5*L/4) := by
    filter_upwards [hb.eventually (Ioo_mem_nhds hell hu)] with t ht
    exact ⟨ht.1.le,ht.2.le⟩
  have hsp : ∀ᶠ t in atTop, 0<s t := by
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    exact payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
  obtain ⟨J,_hJ,hJbound⟩ := payOnce_inactive_normalized_clipped_focal_secondMoment Γ B F g ρ h hlocal
    (3*L/4) (5*L/4) hell hu
  obtain ⟨U,hU,hentry⟩ := exists_test_entry_expansion hn hL ψ d K hK hquad
  have hrembound : Tendsto (fun t => U*(4*s t*((y t)^2+J)+|bar t-L| *(|y t|+1+J)))
      atTop (𝓝 0) := by
    have h0 := (hs.const_mul 4).mul ((hy.pow 2).add_const J)
    have h1 := ((hbar.sub_const L).abs).mul ((hy.abs.add_const 1).add_const J)
    simpa only [sub_self,abs_zero,mul_zero,zero_mul,zero_add] using (h0.add h1).const_mul U
  have hrem : Tendsto (fun t => Bmean t-Pmean t) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (.of_forall fun _ => abs_nonneg _) ?_ hrembound
    filter_upwards [hJbound,hbI,hbp,hsp] with t ht htI hbt hst
    exact normalized_integral_entry_error_le (μ t) hn hL (X t)
      (measurable_clippedFocalPrice hn _ _ (b t))
      (fun r => clipToInterval_mem (by linarith : 3*L/4 ≤ 5*L/4) _)
      ψ hψ hD hU.le hst htI (hentry (b t) htI) (ht (b t) hbt).2.2
  have hpos : Tendsto Pmean atTop (𝓝 (α*gaussianSuccessPrimitive z)) :=
    (payOnce_inactive_clipped_focal_positivePart_tendsto Γ B F g ρ h hlocal
      (3*L/4) (5*L/4) hell hu b hbp y hy).const_mul α
  obtain ⟨A,c,_hA,hc,hout⟩ := payOnce_inactive_focal_price_outside_exponential Γ B F g ρ h
    (3*L/4) (5*L/4) hell hu
  have hDnonneg : 0 ≤ D := (abs_nonneg (ψ 0)).trans (hD 0 (by norm_num))
  have hrare : Tendsto (fun t => 2*D*(A*exp (-c*(M t:ℝ)))/s t) atTop (𝓝 0) := by
    have hh := (tendsto_sqrt_mul_exp M h.population_grows hc A).const_mul (2*D/σ)
    convert hh using 1
    · funext t
      change 2*D*(A*exp (-c*(M t:ℝ)))/(σ/sqrt (M t:ℝ)) = _
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    · simp
  have hbad : Tendsto (fun t => Amean t-Bmean t) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (.of_forall fun _ => abs_nonneg _) ?_ hrare
    filter_upwards [hout,hbp,hsp] with t ht hbt hst
    have hXp r : 0<X t r :=
      (by linarith : 0<3*L/4).trans_le (clipToInterval_mem (by linarith : 3*L/4 ≤ 5*L/4) _).1
    have hE : MeasurableSet {r : Fin (M t-1) → ℝ | focalPrice (k+1) (C t) hn (b t) r ∈ Icc (3*L/4) (5*L/4)} :=
      (measurable_focalPrice hn (b t)) measurableSet_Icc
    have hcmp := abs_integral_sub_le_of_eq_on (μ t)
      (hψ.comp (measurable_allocation_fixed_bid hn (b t)))
      (hψ.comp (measurable_kernel_of_positive_price hn hbt
        (measurable_clippedFocalPrice hn _ _ (b t)) hXp))
      (fun r => hD _ (allocation_bounds hn r (b t)))
      (fun r => hD _ (kernel_bounds hn (hXp r) (b t))) hE (by
        intro r hr
        change ψ (allocation (k+1) (C t) hn r (b t)) = ψ (kernel (k+1) (b t) (X t r))
        have he : X t r=focalPrice (k+1) (C t) hn (b t) r := by
          simp only [X,clippedFocalPrice,clipToInterval,min_eq_right hr.2,max_eq_right hr.1]
        rw [he,(focalPrice_spec hn (b t) r hbt).2.2])
    have hbound := hcmp.trans (mul_le_mul_of_nonneg_left (ht (b t) hbt) (by positivity))
    change |(∫ r, ψ (allocation (k+1) (C t) hn r (b t)) ∂μ t)/s t-
      (∫ r, ψ (kernel (k+1) (b t) (X t r)) ∂μ t)/s t| ≤ _
    rw [← sub_div,abs_div,abs_of_pos hst]
    exact div_le_div_of_nonneg_right hbound hst.le
  have hh := (hbad.add hrem).add hpos
  simp only [sub_add_sub_cancel,sub_add_cancel,zero_add] at hh
  exact hh

end FCAppendix.Bayes
