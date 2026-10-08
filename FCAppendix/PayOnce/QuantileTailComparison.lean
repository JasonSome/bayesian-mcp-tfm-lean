import FCAppendix.PayOnce.RareSuccessRows

namespace FCAppendix.PayOnce.QuantileTailComparison
open MeasureTheory ProbabilityTheory Set Filter Topology Real
open FCAppendix.ExponentialTilt FCAppendix.BoundedLawConvergence
open CompactKernelRareSuccess
open scoped BigOperators

theorem nested_event_tail_ratio
    {Ω : Type*} [MeasurableSpace Ω] (F : ProbabilityMeasure Ω)
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T)
    (hstrict : 0 < (F : Measure Ω) (T \ S)) (hcompl : 0 < (F : Measure Ω) Sᶜ)
    {r s : ℕ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hmean : ρ < (F : Measure Ω).real S)
    (hr : Tendsto (fun t => r t / N t) atTop (𝓝 ρ))
    (hs : Tendsto (fun t => s t / N t) atTop (𝓝 ρ)) :
    (∀ᶠ t in atTop, 0 < (Measure.pi (fun _ : Fin (N t) => (F : Measure Ω))).real
      {ω | ∑ i, S.indicator (fun _ => (1:ℝ)) (ω i) ≤ r t}) ∧
    Tendsto (fun t =>
      (Measure.pi (fun _ : Fin (N t) => (F : Measure Ω))).real
        {ω | ∑ i, T.indicator (fun _ => (1:ℝ)) (ω i) ≤ s t} /
      (Measure.pi (fun _ : Fin (N t) => (F : Measure Ω))).real
        {ω | ∑ i, S.indicator (fun _ => (1:ℝ)) (ω i) ≤ r t}) atTop (𝓝 0) := by
  let X : Ω → ℝ := S.indicator (fun _ => 1)
  let Y : Ω → ℝ := T.indicator (fun _ => 1)
  have hXm : Measurable X := measurable_const.indicator hS
  have hYm : Measurable Y := measurable_const.indicator hT
  have hXb (ω : Ω) : X ω ∈ Icc (0:ℝ) 1 := by
    by_cases h : ω ∈ S <;> simp [X, h]
  have hYb (ω : Ω) : Y ω ∈ Icc (0:ℝ) 1 := by
    by_cases h : ω ∈ T <;> simp [Y, h]
  let μX := F.map hXm.aemeasurable
  let μY := F.map hYm.aemeasurable
  let P := fun t => Measure.pi (fun _ : Fin (N t) => (F : Measure Ω))
  let rowX := fun t (i : Fin (N t)) (ω : Fin (N t) → Ω) => X (ω i)
  let rowY := fun t (i : Fin (N t)) (ω : Fin (N t) → Ω) => Y (ω i)
  have hRX t i : Measurable (rowX t i) := hXm.comp (measurable_pi_apply i)
  have hRY t i : Measurable (rowY t i) := hYm.comp (measurable_pi_apply i)
  have hiX t : iIndepFun (rowX t) (P t) := iIndepFun_pi fun _ => hXm.aemeasurable
  have hiY t : iIndepFun (rowY t) (P t) := iIndepFun_pi fun _ => hYm.aemeasurable
  have hlawX t i : IdentDistrib (rowX t i) id (P t) (μX : Measure ℝ) :=
    identDistrib_pi_map F hXm i
  have hlawY t i : IdentDistrib (rowY t i) id (P t) (μY : Measure ℝ) :=
    identDistrib_pi_map F hYm i
  have hlower : essInf id (μX : Measure ℝ) < ρ := by
    change essInf id ((F : Measure Ω).map X) < ρ
    rw [essInf_id_map _ hXm]
    apply lt_of_le_of_lt _ hρ
    have hfreq : ∃ᵐ ω ∂(F : Measure Ω), X ω ≤ 0 := by
      apply frequently_ae_iff.mpr
      apply ne_of_gt (hcompl.trans_le (measure_mono ?_))
      intro ω hω
      simp only [mem_compl_iff] at hω
      simp [X, hω]
    have hbdd : IsBoundedUnder (· ≥ ·) (ae (F : Measure Ω)) X := ⟨0, by
      change ∀ᵐ ω ∂(F : Measure Ω), 0 ≤ X ω
      exact Filter.Eventually.of_forall fun ω => (hXb ω).1⟩
    exact liminf_le_of_frequently_le hfreq hbdd
  have hmeanX : ρ < ∫ x, x ∂(μX : Measure ℝ) := by
    change ρ < ∫ x, id x ∂(F.map hXm.aemeasurable : Measure ℝ)
    rw [← (identDistrib_map F hXm).integral_eq]
    simpa only [X, integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one] using hmean
  have hgap (u : ℝ) (hu : u < 0) : cgf id (μY : Measure ℝ) u < cgf id (μX : Measure ℝ) u := by
    rw [← cgf_eq_of_identDistrib (identDistrib_map F hYm),
      ← cgf_eq_of_identDistrib (identDistrib_map F hXm)]
    apply StrictCramerComparison.cgf_lt_of_order (F : Measure Ω) hXm.aemeasurable hYm.aemeasurable
      (Filter.Eventually.of_forall hXb) (Filter.Eventually.of_forall hYb) ?_ ?_ hu
    · exact Filter.Eventually.of_forall fun ω => by
        by_cases hx : ω ∈ S
        · simp [X, Y, hx, hST hx]
        · simpa only [X, indicator_of_notMem hx] using (hYb ω).1
    · apply ne_of_gt (hstrict.trans_le (measure_mono ?_))
      intro ω hω
      simp [X, Y, hω.1, hω.2]
  have hpos := (TriangularCramer.tendsto_log_tail_rows N hNpos hN P rowX hRX hiX
    (fun t i => Filter.Eventually.of_forall fun ω => hXb (ω i)) hlawX
    tendsto_const_nhds hr hlower hmeanX).1
  have hratio := (StrictCramerComparison.exponential_tail_ratio_rows N hNpos hN P P rowX rowY
    hRX hRY hiX hiY (fun t i => Filter.Eventually.of_forall fun ω => hXb (ω i))
    (fun t i => Filter.Eventually.of_forall fun ω => hYb (ω i)) hlawX hlawY
    tendsto_const_nhds tendsto_const_nhds hr hs hlower hmeanX hgap)
  obtain ⟨a, ha, _, ht⟩ := hratio
  exact ⟨hpos, ht⟩

end FCAppendix.PayOnce.QuantileTailComparison
