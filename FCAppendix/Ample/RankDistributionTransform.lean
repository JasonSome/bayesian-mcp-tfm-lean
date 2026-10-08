import FCAppendix.Ample.SlackSelection
import FCAppendix.Ample.RankMeasureTools
import Mathlib.Probability.CDF

noncomputable section
namespace FCAppendix.Ample.BidStratum
open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {bid : Ω → ℝ} (E : BidStratum μ bid) (hb : Measurable bid)

def rank (b : ℝ) : ℝ := E.mass - E.tail b

include hb in
theorem rank_eq_lower_mass (b : ℝ) :
    E.rank b = μ.real (E.carrier ∩ {x | bid x ≤ b}) := by
  have hm : MeasurableSet (E.carrier ∩ {x | b < bid x}) :=
    E.measurable_carrier.inter (measurableSet_lt measurable_const hb)
  have hd : Disjoint (E.carrier ∩ {x | bid x ≤ b})
      (E.carrier ∩ {x | b < bid x}) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (show bid x ≤ b from hx.2)) (show b < bid x from hy.2)
  have he : E.carrier = (E.carrier ∩ {x | bid x ≤ b}) ∪
      (E.carrier ∩ {x | b < bid x}) := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro hx
      rcases le_or_gt (bid x) b with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (hx | hx) <;> exact hx.1
  have hs := congrArg (μ.real) he
  rw [measureReal_union hd hm] at hs
  dsimp [rank, mass, tail]
  linarith

theorem rank_nonneg (b : ℝ) : 0 ≤ E.rank b := sub_nonneg.mpr (E.tail_le_mass b)

omit [IsFiniteMeasure μ] in
theorem rank_le_mass (b : ℝ) : E.rank b ≤ E.mass :=
  sub_le_self _ (E.tail_nonneg b)

theorem rank_monotone : Monotone E.rank := by
  intro b c hbc
  exact sub_le_sub_left (E.tail_antitone hbc) _

include hb in
theorem continuous_rank : Continuous E.rank :=
  continuous_const.sub (E.continuous_tail hb)

include hb in
theorem exists_rank_threshold {q : ℝ} (hq : 0 < q) (hqa : q < E.mass) :
    ∃ b : ℝ, 0 < b ∧ E.rank b = q := by
  obtain ⟨b, hb0, he⟩ := E.exists_threshold hb
    (show 0 < E.mass - q by linarith)
    (show E.mass - q < E.mass by linarith)
  refine ⟨b, hb0, ?_⟩
  dsimp [rank]
  rw [he]
  ring

def rankMeasure (_hb : Measurable bid) : Measure ℝ :=
  (μ.restrict E.carrier).map (fun x => E.rank (bid x))

instance rankMeasure_finite : IsFiniteMeasure (E.rankMeasure hb) := by
  unfold rankMeasure
  infer_instance

theorem rankMeasure_apply (s : Set ℝ) (hs : MeasurableSet s) :
    (E.rankMeasure hb).real s = μ.real (E.carrier ∩ {x | E.rank (bid x) ∈ s}) := by
  have hr : Measurable (fun x => E.rank (bid x)) :=
    (E.continuous_rank hb).measurable.comp hb
  unfold rankMeasure
  rw [map_measureReal_apply hr hs, measureReal_restrict_apply (hr hs)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq]
  tauto

theorem rankMeasure_Iic (u : ℝ) :
    (E.rankMeasure hb).real (Iic u) = max 0 (min E.mass u) := by
  classical
  rw [E.rankMeasure_apply hb _ measurableSet_Iic]
  change μ.real (E.carrier ∩ {x | E.rank (bid x) ≤ u}) = _
  have ha : 0 ≤ E.mass := measureReal_nonneg
  by_cases hu0 : u < 0
  · have he : E.carrier ∩ {x | E.rank (bid x) ≤ u} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_le_of_gt hu0) ((E.rank_nonneg (bid x)).trans hx.2)
    rw [he, measureReal_empty, min_eq_right (hu0.le.trans ha), max_eq_left hu0.le]
  · have hu : 0 ≤ u := le_of_not_gt hu0
    by_cases hua : E.mass ≤ u
    · have he : E.carrier ∩ {x | E.rank (bid x) ≤ u} = E.carrier := by
        apply inter_eq_left.mpr
        intro x _
        exact (E.rank_le_mass (bid x)).trans hua
      rw [he, min_eq_left hua, max_eq_right ha]
      rfl
    · have hua' : u < E.mass := lt_of_not_ge hua
      rw [min_eq_right hua'.le, max_eq_right hu]
      let s := E.carrier ∩ {x | E.rank (bid x) ≤ u}
      change μ.real s = u
      have hupper : μ.real s ≤ u := by
        by_contra hbad
        have hus : u < μ.real s := lt_of_not_ge hbad
        obtain ⟨q, huq, hq⟩ := exists_between (lt_min hus hua')
        obtain ⟨b, _hb0, hbq⟩ := E.exists_rank_threshold hb
          (hu.trans_lt huq) (lt_of_lt_of_le hq (min_le_right _ _))
        have hsub : s ⊆ E.carrier ∩ {x | bid x ≤ b} := by
          intro x hx
          refine ⟨hx.1, ?_⟩
          by_contra hxb
          have hbr := E.rank_monotone (le_of_lt (lt_of_not_ge hxb))
          rw [hbq] at hbr
          exact (not_le_of_gt huq) (hbr.trans hx.2)
        have hm := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
        rw [← E.rank_eq_lower_mass hb b, hbq] at hm
        exact (not_le_of_gt (lt_of_lt_of_le hq (min_le_left _ _))) hm
      have hlower : u ≤ μ.real s := by
        by_cases huz : u = 0
        · rw [huz]
          exact measureReal_nonneg
        · obtain ⟨b, _hb0, hbu⟩ := E.exists_rank_threshold hb
            (lt_of_le_of_ne hu (Ne.symm huz)) hua'
          have hsub : E.carrier ∩ {x | bid x ≤ b} ⊆ s := by
            intro x hx
            refine ⟨hx.1, ?_⟩
            exact (E.rank_monotone hx.2).trans hbu.le
          have hm := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
          rwa [← E.rank_eq_lower_mass hb b, hbu] at hm
      exact le_antisymm hupper hlower

end FCAppendix.Ample.BidStratum

namespace FCAppendix.Ample.RankMeasureTools
open MeasureTheory Set
open scoped ENNReal

theorem volume_restrict_Ioc_Iic_real {a : ℝ} (_ha : 0 ≤ a) (u : ℝ) :
    (volume.restrict (Ioc 0 a)).real (Iic u) = max 0 (min a u) := by
  rw [measureReal_restrict_apply measurableSet_Iic]
  have he : Iic u ∩ Ioc (0 : ℝ) a = Ioc 0 (min a u) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
    tauto
  rw [he, Measure.real, Real.volume_Ioc, sub_zero]
  by_cases hu : 0 ≤ min a u
  · rw [ENNReal.toReal_ofReal hu, max_eq_right hu]
  · have hu' : min a u ≤ 0 := (lt_of_not_ge hu).le
    rw [ENNReal.ofReal_of_nonpos hu', ENNReal.toReal_zero, max_eq_left hu']

end FCAppendix.Ample.RankMeasureTools

namespace FCAppendix.Ample.BidStratum
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {bid : Ω → ℝ} (E : BidStratum μ bid) (hb : Measurable bid)

theorem rankMeasure_eq_volume :
    E.rankMeasure hb = volume.restrict (Ioc 0 E.mass) := by
  letI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) E.mass)) := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Iic
  intro u
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [E.rankMeasure_Iic hb u,
    RankMeasureTools.volume_restrict_Ioc_Iic_real (show 0 ≤ E.mass from measureReal_nonneg)]

end FCAppendix.Ample.BidStratum
