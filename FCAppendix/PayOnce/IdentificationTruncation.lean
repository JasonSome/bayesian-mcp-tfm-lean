import FCAppendix.PayOnce.RemoveZeroCutoff
import FCAppendix.Probability.UnitInterval

namespace FCAppendix.PayOnce.CompactifiedBidLaws
open MeasureTheory ProbabilityTheory Filter Topology Set

theorem tendsto_defect_mass_zero_of_compact_blocks
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t))
    (b w : ∀ t, Ω t → ℝ) (hb : ∀ t, Measurable (b t))
    (hbound : ∀ t, ∀ᵐ y ∂P t, 0 ≤ w t y ∧ b t y ≤ w t y)
    (htail : ∀ q : ENNReal, 0 < q → ∃ R : ℝ, ∀ t, P t {y | R < w t y} ≤ q)
    (K : ℕ → ProbabilityMeasure ENNReal) (G : ProbabilityMeasure ENNReal)
    (hmap : ∀ t, (K t : Measure ENNReal) = (P t).map (fun y => ENNReal.ofReal (b t y)))
    (hweak : Tendsto K atTop (𝓝 G)) (hzero : (G : Measure ENNReal) {0} = 0)
    (E : ∀ t, Set (Ω t))
    (hcompact : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ,
      Tendsto (fun t => P t {y | y ∈ E t ∧ w t y ∈ Icc (0:ℝ) R ∧ b t y ∈ Icc ε R})
        atTop (𝓝 0)) :
    Tendsto (fun t => P t (E t)) atTop (𝓝 0) := by
  apply tendsto_defect_mass_zero_of_away_zero P b hb K G hmap hweak hzero E
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact (not_lt_of_ge bot_le hr).elim
  · intro q hq
    obtain ⟨r,hr,hrq⟩ := exists_between hq
    have hr2 : 0 < r/2 := ENNReal.div_pos hr.ne' (by norm_num)
    obtain ⟨R,hR⟩ := htail (r/2) hr2
    filter_upwards [(hcompact ε hε R).eventually_lt_const hr2] with t ht
    have hsub : (E t ∩ {y | ε ≤ b t y} : Set (Ω t)) ≤ᵐ[P t]
        ({y | R < w t y} ∪ {y | y ∈ E t ∧ w t y ∈ Icc (0:ℝ) R ∧ b t y ∈ Icc ε R} : Set (Ω t)) := by
      filter_upwards [hbound t] with y hy hE
      by_cases hwy : R < w t y
      · exact Or.inl hwy
      · exact Or.inr ⟨hE.1,⟨hy.1,le_of_not_gt hwy⟩,⟨hE.2,hy.2.trans (le_of_not_gt hwy)⟩⟩
    have hh := (measure_mono_ae hsub).trans (measure_union_le _ _)
    exact (hh.trans ((add_le_add (hR t) ht.le).trans_eq (ENNReal.add_halves r))).trans_lt hrq

theorem tendsto_integral_zero_of_bounded_defects
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (e : ∀ t, Ω t → ℝ) (he : ∀ t, Measurable (e t))
    (heb : ∀ t y, e t y ∈ Icc (0:ℝ) 1)
    (hmass : ∀ δ : ℝ, 0 < δ → Tendsto (fun t => P t {y | δ ≤ e t y}) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ y, e t y ∂P t) atTop (𝓝 0) := by
  have hI t : Integrable (e t) (P t) :=
    UnitInterval.integrable (P t) (e t) (he t) (fun y => (heb t y).1) (fun y => (heb t y).2)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans_le (integral_nonneg fun y => (heb t y).1)
  · intro ε hε
    let δ := ε/2
    have hδ : 0 < δ := half_pos hε
    have hm : Tendsto (fun t => (P t).real {y | δ ≤ e t y}) atTop (𝓝 0) := by
      simpa only [measureReal_def,ENNReal.toReal_zero,Function.comp_def] using
        (ENNReal.continuousAt_toReal (by simp : (0:ENNReal) ≠ ⊤)).tendsto.comp (hmass δ hδ)
    filter_upwards [hm.eventually_lt_const hδ] with t ht
    let E := {y | δ ≤ e t y}
    have hE : MeasurableSet E := measurableSet_le measurable_const (he t)
    have hEi : Integrable (E.indicator (fun _ => (1:ℝ))) (P t) := (integrable_const 1).indicator hE
    have hh := integral_mono (hI t) ((integrable_const δ).add hEi) (fun y => by
      change e t y ≤ δ+E.indicator (fun _ => (1:ℝ)) y
      by_cases hy : y ∈ E
      · rw [indicator_of_mem hy]
        linarith [(heb t y).2]
      · rw [indicator_of_notMem hy]
        exact (le_of_not_ge hy).trans (by simp))
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const δ) hEi,integral_const,probReal_univ,one_smul,
      integral_indicator_const 1 hE,smul_eq_mul,mul_one] at hh
    change (P t).real E < δ at ht
    dsimp only [δ] at hh ht
    linarith

end FCAppendix.PayOnce.CompactifiedBidLaws
