import FCAppendix.PayOnce.CompactifiedBidLaws

namespace FCAppendix.PayOnce.CompactifiedBidLaws
open MeasureTheory ProbabilityTheory Filter Topology Set

theorem exists_small_positive_window (G : ProbabilityMeasure ENNReal)
    (hzero : (G : Measure ENNReal) {0} = 0) {q : ENNReal} (hq : 0 < q) :
    ∃ ε : ℝ, 0 < ε ∧ (G : Measure ENNReal) (Iic (ENNReal.ofReal ε)) < q := by
  let a : ℕ → ℝ := fun j => 1 / ((j:ℝ)+1)
  have ha j : 0 < a j := by dsimp only [a]; positivity
  have ht : Tendsto (fun j => ENNReal.ofReal (a j)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def, a] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hanti : Antitone (fun j => Iic (ENNReal.ofReal (a j))) := by
    intro i j hij
    apply Iic_subset_Iic.mpr
    apply ENNReal.ofReal_le_ofReal
    dsimp only [a]
    gcongr
  have hinter : (⋂ j, Iic (ENNReal.ofReal (a j))) = ({0} : Set ENNReal) := by
    ext b
    simp only [mem_iInter, mem_Iic, mem_singleton_iff]
    constructor
    · intro hb
      exact le_antisymm (ge_of_tendsto ht (Filter.Eventually.of_forall hb)) bot_le
    · rintro rfl
      exact fun _ => bot_le
  have hm := tendsto_measure_iInter_atTop (μ := (G : Measure ENNReal))
    (fun _ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, hzero] at hm
  obtain ⟨j,hj⟩ := (hm.eventually_lt_const hq).exists
  exact ⟨a j, ha j, hj⟩

theorem tendsto_defect_mass_zero_of_away_zero
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t))
    (b : ∀ t, Ω t → ℝ) (hb : ∀ t, Measurable (b t))
    (K : ℕ → ProbabilityMeasure ENNReal) (G : ProbabilityMeasure ENNReal)
    (hmap : ∀ t, (K t : Measure ENNReal) = (P t).map (fun z => ENNReal.ofReal (b t z)))
    (hweak : Tendsto K atTop (𝓝 G)) (hzero : (G : Measure ENNReal) {0} = 0)
    (E : ∀ t, Set (Ω t))
    (haway : ∀ ε : ℝ, 0 < ε → Tendsto (fun t => P t (E t ∩ {z | ε ≤ b t z})) atTop (𝓝 0)) :
    Tendsto (fun t => P t (E t)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact (not_lt_of_ge bot_le hr).elim
  · intro q hq
    obtain ⟨r,hr,hrq⟩ := exists_between hq
    have hr2 : 0 < r/2 := ENNReal.div_pos hr.ne' (by norm_num)
    obtain ⟨ε,hε,hsmall⟩ := exists_small_positive_window G hzero hr2
    have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak
      (isClosed_Iic (a := ENNReal.ofReal ε))
    have hevent := eventually_lt_of_limsup_lt (hport.trans_lt hsmall)
    filter_upwards [hevent, (haway ε hε).eventually_lt_const hr2] with t ht ht'
    have hsub : E t ⊆ (fun z => ENNReal.ofReal (b t z)) ⁻¹' Iic (ENNReal.ofReal ε) ∪
        (E t ∩ {z | ε ≤ b t z}) := by
      intro z hz
      rcases le_total (b t z) ε with h | h
      · exact Or.inl (ENNReal.ofReal_le_ofReal h)
      · exact Or.inr ⟨hz,h⟩
    have hbound := (measure_mono (μ := P t) hsub).trans (measure_union_le _ _)
    rw [hmap t, Measure.map_apply (show Measurable (fun z => ENNReal.ofReal (b t z)) from
      ENNReal.measurable_ofReal.comp (hb t)) measurableSet_Iic] at ht
    exact (hbound.trans ((add_le_add ht.le ht'.le).trans_eq (ENNReal.add_halves r))).trans_lt hrq

end FCAppendix.PayOnce.CompactifiedBidLaws
