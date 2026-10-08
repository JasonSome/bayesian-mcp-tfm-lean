import FCAppendix.PayOnce.RemoveFixedZeroAtom
import FCAppendix.Probability.UnitInterval

namespace FCAppendix.PayOnce.CompactifiedBidLaws
open MeasureTheory ProbabilityTheory Filter Topology Set

theorem tendsto_defect_mass_zero_of_compact_blocks_fixed_atom
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t))
    (b w : ∀ t, Ω t → ℝ) (hb : ∀ t, Measurable (b t))
    (hbound : ∀ t, ∀ᵐ y ∂P t, 0 ≤ w t y ∧ b t y ≤ w t y)
    (htail : ∀ q : ENNReal, 0 < q → ∃ R : ℝ, ∀ t, P t {y | R < w t y} ≤ q)
    (K : ℕ → ProbabilityMeasure ENNReal) (G : ProbabilityMeasure ENNReal)
    (hmap : ∀ t, (K t : Measure ENNReal) = (P t).map (fun y => ENNReal.ofReal (b t y)))
    (hweak : Tendsto K atTop (𝓝 G)) (hzero : ∀ t, (K t : Measure ENNReal) {0} = (G : Measure ENNReal) {0})
    (E : ∀ t, Set (Ω t)) (hpositive : ∀ t, ∀ᵐ y ∂P t, y ∈ E t → 0 < b t y)
    (hcompact : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ,
      Tendsto (fun t => P t {y | y ∈ E t ∧ w t y ∈ Icc (0:ℝ) R ∧ b t y ∈ Icc ε R})
        atTop (𝓝 0)) :
    Tendsto (fun t => P t (E t)) atTop (𝓝 0) := by
  apply tendsto_defect_mass_zero_of_away_zero_fixed_atom P b hb K G hmap hweak hzero E hpositive
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

end FCAppendix.PayOnce.CompactifiedBidLaws
