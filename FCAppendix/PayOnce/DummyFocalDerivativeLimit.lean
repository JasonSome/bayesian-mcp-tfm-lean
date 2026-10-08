import FCAppendix.PayOnce.DummyFocalImpactLimit
import FCAppendix.PayOnce.ServedSlope

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open KernelLawConvergence KernelTailEvent CompactifiedBidLaws OwnImpact RareSuccessSlope TruncatedFOC
open scoped BigOperators

theorem tendsto_focal_coverage_derivative
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ}
    {ρ L : ℝ} (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T, 0 < T → KernelDemand.demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hcapacity : Tendsto (fun t => (c t:ℝ)/N t) atTop (𝓝 ρ))
    {a z : ℝ} (ha : L < a) (haz : a < z) (hz : z < (n:ℝ)*L)
    (hwin : 0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z)))
    (x : ℕ → ℝ) (hx : ∀ t, 0 < x t) {x₀ : ℝ} (hx₀ : L < x₀)
    (hxx : Tendsto x atTop (𝓝 x₀))
    (hreg : ∀ t, ∀ᵐ r ∂Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ)),
      RegularClearing n (c t) r (x t)) :
    Tendsto (fun t => deriv (coverage n (c t) hn
      (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ)))) (x t)) atTop
        (𝓝 (phi n (kernel n x₀ L)/x₀)) := by
  let P := fun t => Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))
  let p := fun t (r : Fin (N t) → ℝ) => allocation n (c t) hn r (x t)
  let q := kernel n x₀ L
  have hp t : Measurable (p t) := measurable_allocation_rivals hn (hx t)
  have hpb t r : p t r ∈ Icc (0:ℝ) 1 := allocation_bounds hn r (x t)
  have hqb : q ∈ Icc (0:ℝ) 1 := kernel_bounds hn hL x₀
  have hq : 0 < q := by
    apply lt_of_le_of_ne hqb.1
    intro he
    exact hx₀.not_ge ((kernel_eq_zero_iff n hn (hL.trans hx₀) hL).mp he.symm)
  have herr := tendsto_focal_allocation_kernel_error N hNpos hN hn G hpos hweak hL
    hroot hunique hcapacity x hx
  have hk : Tendsto (fun t => kernel n (x t) L) atTop (𝓝 q) :=
    (continuous_kernel_bid hn hL).continuousAt.tendsto.comp hxx
  have hgap : Tendsto (fun t => ∫ r, |p t r-q| ∂P t) atTop (𝓝 0) := by
    have hlim := herr.add ((hk.sub_const q).abs)
    simp only [sub_self,abs_zero,add_zero] at hlim
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) _ hlim
    intro t
    have hi₀ := CovarianceConcentration.integrable_abs_gap (P t) (hp t) measurable_const
      (hpb t) (fun _ => kernel_bounds hn hL (x t))
    have hi₁ := CovarianceConcentration.integrable_abs_gap (P t) (hp t) measurable_const
      (hpb t) (fun _ => hqb)
    have hh := integral_mono hi₁ (hi₀.add (integrable_const |kernel n (x t) L-q|))
      (fun r => abs_sub_le (p t r) (kernel n (x t) L) q)
    simpa only [Pi.add_apply, integral_add hi₀ (integrable_const _),integral_const,
      probReal_univ,one_smul] using hh
  have hbase := mean_abs_baseSlope_tendsto_zero P hn p hp hpb ⟨hq,hqb.2⟩ hgap
  choose w hw hwb _ hweight hderiv using fun t =>
    exists_measurable_weight_coverage_derivative hn (P t) (hx t) (hreg t)
  have hcor := tendsto_focal_slope_correction N hNpos hN hn G hpos hweak hL hroot
    hunique hcapacity ha haz hz hwin x hx w hw hwb hreg hweight
  have hbaseI t : Integrable (fun r => baseSlope n (p t r)) (P t) :=
    integrable_weightedSlope (P t) hn (hp t) measurable_const (hpb t) (fun _ _ => ⟨le_rfl,zero_le_one⟩)
  have hweightI t : Integrable (fun r => weightedSlope n (p t r) (w t r)) (P t) :=
    integrable_weightedSlope (P t) hn (hp t) (hw t) (hpb t) (fun r _ => hwb t r)
  have hbint : Tendsto (fun t => ∫ r, baseSlope n (p t r) ∂P t) atTop (𝓝 (phi n q)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hbase
    intro t
    have he : (∫ r, baseSlope n (p t r) ∂P t)-phi n q =
        ∫ r, baseSlope n (p t r)-phi n q ∂P t := by
      rw [integral_sub (hbaseI t) (integrable_const _)]
      simp only [integral_const,probReal_univ,one_smul]
    rw [he]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun r => baseSlope n (p t r)-phi n q)
  have hdint : Tendsto (fun t => ∫ r, weightedSlope n (p t r) (w t r) ∂P t) atTop (𝓝 (phi n q)) := by
    have ht := hbint.sub hcor
    simp only [sub_zero] at ht
    apply ht.congr
    intro t
    change (∫ r, baseSlope n (p t r) ∂P t)-
      (∫ r, baseSlope n (p t r)-weightedSlope n (p t r) (w t r) ∂P t) = _
    rw [integral_sub (hbaseI t) (hweightI t),sub_sub_cancel]
  have hlim := hdint.div hxx (hL.trans hx₀).ne'
  apply hlim.congr
  intro t
  exact (hderiv t).deriv.symm

end FCAppendix.PayOnce.DummyKernel
