import FCAppendix.Affine.Tail04.SourceValuePartition

noncomputable section
namespace FCAppendix.Affine.Tail04.ValueParameters
open OriginalValues
open MeasureTheory ProbabilityTheory Set Filter

variable (P : ValueParameters)

abbrev bulkValues : Set ℝ := Icc (P.vA-P.w) (P.vA+P.w)
abbrev truncatedTailValues (t : ℝ) : Set ℝ := Icc P.M t

def bulkWeight : ℝ := activeMass P.theta*(1-P.zeta)
def truncatedTailWeight (t : ℝ) : ℝ := activeMass P.theta*P.zeta-
  activeMass P.theta*P.zeta*powerTail P.M 10 t

theorem bulkWeight_pos : 0< P.bulkWeight :=
  mul_pos P.active_mass_pos (sub_pos.mpr P.zeta_lt_one)

theorem density_on_bulk (v : ℝ) (hv : v∈P.bulkValues) :
    valueDensity P v=P.bulkWeight/(2*P.w) := by
  have hL : v∉Icc (0:ℝ) P.d0 := by
    intro h
    linarith [h.2,hv.1,P.low_partial_gap,P.partial_active_gap,P.w_pos]
  have hP : v∉P.partialValues := by
    intro h
    exact (not_le.mpr P.partial_active_gap) (hv.1.trans h.2)
  change v ∉ Icc (2-P.w) (2+P.w) at hP
  have hT : v∉Ici P.M := fun h => (not_le.mpr P.active_tail_gap) (h.trans hv.2)
  simp only [valueDensity,bandDensity,paretoDensity,indicator_of_notMem hL,
    indicator_of_notMem hP,indicator_of_mem hv,indicator_of_notMem hT,
    mul_zero,zero_add,add_zero]
  rw [show (P.vA+P.w)-(P.vA-P.w)=2*P.w by ring]
  unfold bulkWeight
  ring

theorem bulk_indicator : P.bulkValues.indicator (valueDensity P)=
    fun v => P.bulkWeight*bandDensity (P.vA-P.w) (P.vA+P.w) v := by
  funext v
  by_cases hv : v∈P.bulkValues
  · rw [indicator_of_mem hv,P.density_on_bulk v hv]
    simp only [bandDensity,indicator_of_mem hv]
    rw [show (P.vA+P.w)-(P.vA-P.w)=2*P.w by ring]
    ring
  · simp only [bandDensity,indicator_of_notMem hv,mul_zero]

theorem bulk_mass : (valueLaw P).real P.bulkValues=P.bulkWeight := by
  have hi : (∫ v in P.bulkValues,valueDensity P v)=P.bulkWeight := by
    rw [←integral_indicator measurableSet_Icc,P.bulk_indicator,integral_const_mul,
      integral_bandDensity _ _ (by linarith [P.w_pos]),mul_one]
  rw [measureReal_def,valueLaw,withDensity_apply _ measurableSet_Icc,
    ←ofReal_integral_eq_lintegral_ofReal (valueDensity_integrable P).integrableOn
      (Eventually.of_forall (valueDensity_nonneg P)),hi,
    ENNReal.toReal_ofReal P.bulkWeight_pos.le]

theorem full_tail_mass : (valueLaw P).real (Ici P.M)=activeMass P.theta*P.zeta := by
  have hne : ∀ᵐ v ∂valueLaw P,v≠P.M := by
    rw [ae_iff]
    have hs : {v : ℝ | ¬v ≠ P.M} = {P.M} := by ext v;simp
    rw [hs]
    exact measure_singleton P.M
  have he : Ici P.M=ᵐ[valueLaw P] Ioi P.M := by
    filter_upwards [hne] with v hv
    change (v ∈ Ici P.M) = (v ∈ Ioi P.M)
    simp only [mem_Ici,mem_Ioi]
    exact propext ⟨fun h => lt_of_le_of_ne h (Ne.symm hv),le_of_lt⟩
  rw [show (valueLaw P).real (Ici P.M)=(valueLaw P).real (Ioi P.M) from
    congrArg ENNReal.toReal (measure_congr he),P.real_tail P.M le_rfl,
    powerTail_ten P.M P.M P.M_pos P.M_pos,div_self P.M_pos.ne']
  simp

theorem truncatedTail_mass (t : ℝ) (ht : P.M≤ t) :
    (valueLaw P).real (P.truncatedTailValues t)=P.truncatedTailWeight t := by
  have hdis : Disjoint (P.truncatedTailValues t) (Ioi t) := by
    apply disjoint_left.mpr
    intro v hv hw
    exact (not_lt.mpr hv.2) hw
  have hun : P.truncatedTailValues t∪Ioi t=Ici P.M := by
    ext v
    constructor
    · rintro (hv|hv)
      · exact hv.1
      · exact ht.trans hv.le
    · intro hv
      by_cases hvt : v≤ t
      · exact Or.inl ⟨hv,hvt⟩
      · exact Or.inr (lt_of_not_ge hvt)
  have h := measureReal_union (μ:=valueLaw P) hdis measurableSet_Ioi
  rw [hun,P.full_tail_mass,P.real_tail t ht] at h
  unfold truncatedTailWeight
  linarith

theorem truncatedTailWeight_pos (t : ℝ) (ht : P.M< t) : 0< P.truncatedTailWeight t := by
  have ht0 : 0< t := P.M_pos.trans ht
  have hratio : P.M/t<1 := (div_lt_one ht0).mpr ht
  have hp : powerTail P.M 10 t<1 := by
    rw [powerTail_ten P.M t P.M_pos ht0]
    exact pow_lt_one₀ (div_nonneg P.M_pos.le ht0.le) hratio (by norm_num)
  have hm := mul_pos P.active_mass_pos P.zeta_pos
  have hlt := mul_lt_mul_of_pos_left hp hm
  unfold truncatedTailWeight
  linarith

theorem component_weight_sum (t : ℝ) :
    P.bulkWeight+P.truncatedTailWeight t=
      activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  unfold bulkWeight truncatedTailWeight
  ring

theorem fine_support : ∀ᵐ v ∂valueLaw P,
    v∈Icc (0:ℝ) P.d0∪P.partialValues∪P.bulkValues∪Ici P.M := by
  have hLA : Disjoint (Icc (0:ℝ) P.d0∪P.partialValues) P.bulkValues := by
    apply disjoint_left.mpr
    intro v hv ha
    rcases hv with hl|hp
    · linarith [hl.2,ha.1,P.low_partial_gap,P.partial_active_gap,P.w_pos]
    · exact (not_le.mpr P.partial_active_gap) (ha.1.trans hp.2)
  have hT : Disjoint (Icc (0:ℝ) P.d0∪P.partialValues∪P.bulkValues) (Ici P.M) := by
    apply disjoint_left.mpr
    intro v hv ht
    change P.M ≤ v at ht
    rcases hv with (hl|hp)|ha
    · linarith [hl.2,ht,P.low_partial_gap,P.partial_active_gap,P.active_tail_gap,P.w_pos]
    · change v ∈ Icc (2-P.w) (2+P.w) at hp
      linarith [hp.2,ht,P.partial_active_gap,P.active_tail_gap,P.w_pos]
    · exact (not_le.mpr P.active_tail_gap) (ht.trans ha.2)
  apply ae_mem_of_real_one (valueLaw P) _
    (((measurableSet_Icc.union measurableSet_Icc).union measurableSet_Icc).union measurableSet_Ici)
  change (valueLaw P).real (Icc (0:ℝ) P.d0 ∪ P.partialValues ∪ P.bulkValues ∪ Ici P.M) = 1
  rw [measureReal_union hT measurableSet_Ici,measureReal_union hLA measurableSet_Icc,
    measureReal_union P.low_partial_disjoint measurableSet_Icc,
    P.partial_mass,P.bulk_mass,P.full_tail_mass]
  have hlow : (valueLaw P).real (Icc (0:ℝ) P.d0)=lowMass P.theta := by
    rw [measureReal_def,P.low_closed_mass,ENNReal.toReal_ofReal P.low_mass_pos.le]
  rw [hlow]
  unfold bulkWeight
  linarith [mass_sum P.theta]

theorem active_component_restrictions (t : ℝ) (ht : P.M≤ t) :
    (valueLaw P).restrict P.bulkValues+
      (valueLaw P).restrict (P.truncatedTailValues t)=
        (valueLaw P).restrict (P.movingActiveValues t) := by
  have hdis : Disjoint P.bulkValues (P.truncatedTailValues t) := by
    apply disjoint_left.mpr
    intro v hb ht
    exact (not_le.mpr P.active_tail_gap) (ht.1.trans hb.2)
  rw [←Measure.restrict_union hdis measurableSet_Icc]
  apply Measure.ext
  intro B hB
  rw [Measure.restrict_apply hB,Measure.restrict_apply hB]
  apply measure_congr
  filter_upwards [P.fine_support] with v hv
  apply propext
  constructor
  · rintro ⟨hBv,hb|htv⟩
    · exact ⟨hBv,hb.1,hb.2.trans (P.active_tail_gap.le.trans ht)⟩
    · exact ⟨hBv,by linarith [htv.1,P.active_tail_gap,P.w_pos],htv.2⟩
  · rintro ⟨hBv,hva⟩
    refine ⟨hBv,?_⟩
    rcases hv with ((hl|hp)|hb)|htv
    · exfalso
      linarith [hl.2,hva.1,P.low_partial_gap,P.partial_active_gap,P.w_pos]
    · exfalso
      exact (not_le.mpr P.partial_active_gap) (hva.1.trans hp.2)
    · exact Or.inl hb
    · exact Or.inr ⟨htv,hva.2⟩

def originalBulkLaw : Measure (Icc (P.vA-P.w) (P.vA+P.w)) :=
  compactConditional (valueLaw P) (P.vA-P.w) (P.vA+P.w) (by linarith [P.w_pos])

instance originalBulkLaw_probability : IsProbabilityMeasure P.originalBulkLaw := by
  apply compactConditional_probability
  intro hz
  have h := P.bulk_mass
  rw [measureReal_def,hz,ENNReal.toReal_zero] at h
  linarith [P.bulkWeight_pos]

theorem originalBulkLaw_real : P.originalBulkLaw.map Subtype.val=cond (valueLaw P) P.bulkValues :=
  compactConditional_real _ _ _ _

def originalTruncatedTailLaw (t : ℝ) (ht : P.M< t) : Measure (Icc P.M t) :=
  compactConditional (valueLaw P) P.M t ht.le

instance originalTruncatedTailLaw_probability (t : ℝ) (ht : P.M< t) :
    IsProbabilityMeasure (P.originalTruncatedTailLaw t ht) := by
  apply compactConditional_probability
  intro hz
  have h := P.truncatedTail_mass t ht.le
  rw [measureReal_def,hz,ENNReal.toReal_zero] at h
  linarith [P.truncatedTailWeight_pos t ht]

theorem originalTruncatedTailLaw_real (t : ℝ) (ht : P.M< t) :
    (P.originalTruncatedTailLaw t ht).map Subtype.val=
      cond (valueLaw P) (P.truncatedTailValues t) :=
  compactConditional_real _ _ _ _

theorem weighted_originalBulkLaw :
    ENNReal.ofReal P.bulkWeight • P.originalBulkLaw.map Subtype.val=
      (valueLaw P).restrict P.bulkValues := by
  have hm : valueLaw P P.bulkValues=ENNReal.ofReal P.bulkWeight := by
    rw [←P.bulk_mass,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [P.originalBulkLaw_real,←hm,Hybrid.measure_smul_cond]

theorem weighted_originalTruncatedTailLaw (t : ℝ) (ht : P.M< t) :
    ENNReal.ofReal (P.truncatedTailWeight t) • (P.originalTruncatedTailLaw t ht).map Subtype.val=
      (valueLaw P).restrict (P.truncatedTailValues t) := by
  have hm : valueLaw P (P.truncatedTailValues t)=ENNReal.ofReal (P.truncatedTailWeight t) := by
    rw [←P.truncatedTail_mass t ht.le,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [P.originalTruncatedTailLaw_real t ht,←hm,Hybrid.measure_smul_cond]

theorem weighted_active_components (t : ℝ) (ht : P.M< t) :
    ENNReal.ofReal P.bulkWeight • P.originalBulkLaw.map Subtype.val+
      ENNReal.ofReal (P.truncatedTailWeight t) • (P.originalTruncatedTailLaw t ht).map Subtype.val=
      ENNReal.ofReal (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t) •
        (P.originalMovingActiveLaw t ht.le).map Subtype.val := by
  rw [P.weighted_originalBulkLaw,P.weighted_originalTruncatedTailLaw t ht,
    P.weighted_originalMovingActiveLaw t ht.le]
  exact P.active_component_restrictions t ht.le

end FCAppendix.Affine.Tail04.ValueParameters

namespace FCAppendix.Affine.Tail04.OriginalValues
export FCAppendix.Affine.Tail04.ValueParameters (bulkValues truncatedTailValues bulkWeight truncatedTailWeight bulkWeight_pos density_on_bulk bulk_indicator bulk_mass full_tail_mass truncatedTail_mass truncatedTailWeight_pos component_weight_sum fine_support active_component_restrictions originalBulkLaw originalBulkLaw_real originalTruncatedTailLaw originalTruncatedTailLaw_real weighted_originalBulkLaw weighted_originalTruncatedTailLaw weighted_active_components)
end FCAppendix.Affine.Tail04.OriginalValues
