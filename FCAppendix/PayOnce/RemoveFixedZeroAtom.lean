import FCAppendix.PayOnce.CompactifiedBidLaws

namespace FCAppendix.PayOnce.CompactifiedBidLaws
open MeasureTheory ProbabilityTheory Filter Topology Set

theorem exists_lower_window_lt_zero_mass_add (G : ProbabilityMeasure ENNReal)
    {q : ENNReal} (hq : 0 < q) :
    ∃ ε : ℝ, 0 < ε ∧ (G : Measure ENNReal) (Iic (ENNReal.ofReal ε)) < (G : Measure ENNReal) {0} + q := by
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
  rw [hinter] at hm
  obtain ⟨j,hj⟩ := (hm.eventually_lt_const (ENNReal.lt_add_right (measure_ne_top _ _) hq.ne')).exists
  exact ⟨a j, ha j, hj⟩

theorem eventually_small_positive_window_of_fixed_atom
    (K : ℕ → ProbabilityMeasure ENNReal) (G : ProbabilityMeasure ENNReal)
    (hweak : Tendsto K atTop (𝓝 G))
    (hzero : ∀ t, (K t : Measure ENNReal) {0} = (G : Measure ENNReal) {0})
    {q : ENNReal} (hq : 0 < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t in atTop, (K t : Measure ENNReal) (Ioc 0 (ENNReal.ofReal ε)) < q := by
  obtain ⟨ε,hε,hsmall⟩ := exists_lower_window_lt_zero_mass_add G hq
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak
    (isClosed_Iic (a := ENNReal.ofReal ε))
  refine ⟨ε,hε,?_⟩
  filter_upwards [eventually_lt_of_limsup_lt (hport.trans_lt hsmall)] with t ht
  have he : (K t : Measure ENNReal) (Ioc 0 (ENNReal.ofReal ε)) =
      (K t : Measure ENNReal) (Iic (ENNReal.ofReal ε)) - (G : Measure ENNReal) {0} := by
    rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr (show (0:ENNReal) ≤ ENNReal.ofReal ε from zero_le))
      measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _),
      (show Iic (0:ENNReal) = {0} by ext x; simp), hzero t]
  rw [he]
  apply (ENNReal.sub_lt_iff_lt_left (measure_ne_top _ _) ?_).mpr ht
  rw [← hzero t]
  exact measure_mono (singleton_subset_iff.mpr (show (0:ENNReal) ≤ ENNReal.ofReal ε from zero_le))

theorem tendsto_defect_mass_zero_of_away_zero_fixed_atom
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t))
    (b : ∀ t, Ω t → ℝ) (hb : ∀ t, Measurable (b t))
    (K : ℕ → ProbabilityMeasure ENNReal) (G : ProbabilityMeasure ENNReal)
    (hmap : ∀ t, (K t : Measure ENNReal) = (P t).map (fun z => ENNReal.ofReal (b t z)))
    (hweak : Tendsto K atTop (𝓝 G))
    (hzero : ∀ t, (K t : Measure ENNReal) {0} = (G : Measure ENNReal) {0})
    (E : ∀ t, Set (Ω t)) (hpositive : ∀ t, ∀ᵐ z ∂P t, z ∈ E t → 0 < b t z)
    (haway : ∀ ε : ℝ, 0 < ε → Tendsto (fun t => P t (E t ∩ {z | ε ≤ b t z})) atTop (𝓝 0)) :
    Tendsto (fun t => P t (E t)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact (not_lt_of_ge bot_le hr).elim
  · intro q hq
    obtain ⟨r,hr,hrq⟩ := exists_between hq
    have hr2 : 0 < r/2 := ENNReal.div_pos hr.ne' (by norm_num)
    obtain ⟨ε,hε,hsmall⟩ := eventually_small_positive_window_of_fixed_atom K G hweak hzero hr2
    filter_upwards [hsmall, (haway ε hε).eventually_lt_const hr2] with t ht ht'
    have hsub : E t ≤ᵐ[P t] ((fun z => ENNReal.ofReal (b t z)) ⁻¹' Ioc 0 (ENNReal.ofReal ε) ∪
        (E t ∩ {z | ε ≤ b t z}) : Set (Ω t)) := by
      filter_upwards [hpositive t] with z hpos hz
      rcases le_total (b t z) ε with h | h
      · exact Or.inl ⟨ENNReal.ofReal_pos.mpr (hpos hz), ENNReal.ofReal_le_ofReal h⟩
      · exact Or.inr ⟨hz,h⟩
    have hbound := (measure_mono_ae hsub).trans (measure_union_le _ _)
    rw [hmap t, Measure.map_apply (show Measurable (fun z => ENNReal.ofReal (b t z)) from
      ENNReal.measurable_ofReal.comp (hb t)) measurableSet_Ioc] at ht
    exact (hbound.trans ((add_le_add ht.le ht'.le).trans_eq (ENNReal.add_halves r))).trans_lt hrq

end FCAppendix.PayOnce.CompactifiedBidLaws
