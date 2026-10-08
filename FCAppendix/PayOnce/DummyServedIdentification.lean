import FCAppendix.PayOnce.ServedIdentification
import FCAppendix.PayOnce.DummyFocalDerivativeLimit
import FCAppendix.PayOnce.DummyRareSuccess

namespace FCAppendix.PayOnce.DummyRareSuccess
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open DummyKernel KernelLawConvergence KernelTailEvent CompactifiedBidLaws RareSuccessSlope
open AnalyticalKernel (served_formulas_of_first_order)

theorem served_formulas_of_supported_IC_limit
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
    {T : ℕ → Set ℝ} {x w : ℕ → ℝ} {x₀ w₀ : ℝ}
    (hgood : ∀ t, x t ∈ regularSupportedSet (ι := Fin (N t)) n (c t) (G t : Measure ℝ) (T t))
    (hx₀ : L < x₀) (hxx : Tendsto x atTop (𝓝 x₀)) (hww : Tendsto w atTop (𝓝 w₀))
    (hIC : ∀ t y, y ∈ T t →
      (w t-y)*coverage n (c t) hn (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
      (w t-x t)*coverage n (c t) hn (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (x t)) :
    L < w₀ ∧ kernel n x₀ L = Limit.pStar n L w₀ ∧
      x₀ = L/H n (Limit.pStar n L w₀) ∧ x₀ < (n:ℝ)*L := by
  let P := fun t => Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))
  let Q := fun t => coverage n (c t) hn (P t)
  have hx t : 0 < x t := (hgood t).1
  have hreg t : ∀ᵐ r ∂P t, RegularClearing n (c t) r (x t) := (hgood t).2.1
  have hd := tendsto_focal_coverage_derivative N hNpos hN hn G hpos hweak hL hroot hunique
    hcapacity ha haz hz hwin x hx hx₀ hxx hreg
  have hq := tendsto_focal_coverage N hNpos hN hn G hpos hweak hL hroot hunique hcapacity x hx hxx
  have hf t : Q t (x t) = (w t-x t)*deriv (Q t) (x t) := by
    have hderiv := hasDerivAt_coverage_of_regular hn (P t) (hx t) (hreg t)
    exact SupportedFOC.payOnce_first_order_condition hderiv.2.differentiableAt.hasDerivAt
      (hgood t).2.2.1 (hgood t).2.2.2 (hIC t)
  have hprod := (hww.sub hxx).mul hd
  have he : success n (kernel n x₀ L) = (w₀-x₀)*(phi n (kernel n x₀ L)/x₀) :=
    tendsto_nhds_unique hq (hprod.congr fun t => (hf t).symm)
  exact served_formulas_of_first_order hn hL hx₀ he

end FCAppendix.PayOnce.DummyRareSuccess
