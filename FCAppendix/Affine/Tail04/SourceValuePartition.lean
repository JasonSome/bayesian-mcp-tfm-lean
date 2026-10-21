import FCAppendix.Affine.Tail04.OriginalCompactLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalValues
open MeasureTheory ProbabilityTheory Set

theorem ae_mem_of_real_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : Set X)
    (hE : MeasurableSet E) (h : μ.real E = 1) : ∀ᵐ x ∂μ, x ∈ E := by
  have hm : μ E = 1 := by
    calc
      μ E = ENNReal.ofReal (μ.real E) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ E)).symm
      _ = 1 := by rw [h, ENNReal.ofReal_one]
  rw [ae_iff]
  change μ Eᶜ = 0
  rw [measure_compl hE (measure_ne_top μ E), measure_univ, hm, tsub_self]

end FCAppendix.Affine.Tail04.OriginalValues
namespace FCAppendix.Affine.Tail04.ValueParameters
open MeasureTheory ProbabilityTheory Set OriginalValues

variable (P : ValueParameters)

theorem low_partial_disjoint :
    Disjoint (Icc (0:ℝ) P.d0) P.partialValues := by
  apply disjoint_left.mpr
  intro v hv hw
  exact (not_le.mpr P.low_partial_gap) (hw.1.trans hv.2)

theorem low_fixedUpper_disjoint :
    Disjoint (Icc (0:ℝ) P.d0) P.fixedUpperValues := by
  apply disjoint_left.mpr
  intro v hv hw
  change P.vA-P.w ≤ v at hw
  have hg : P.d0 < P.vA-P.w := by
    linarith [P.low_partial_gap, P.partial_active_gap, P.w_pos]
  linarith [hv.2]

theorem partial_fixedUpper_disjoint :
    Disjoint P.partialValues P.fixedUpperValues := by
  apply disjoint_left.mpr
  intro v hv hw
  change P.vA-P.w ≤ v at hw
  exact (not_le.mpr P.partial_active_gap) (hw.trans hv.2)

theorem original_support : ∀ᵐ v ∂valueLaw P,
    v ∈ Icc (0:ℝ) P.d0 ∪ P.partialValues ∪ P.fixedUpperValues := by
  have hLP : MeasurableSet (Icc (0:ℝ) P.d0 ∪ P.partialValues) :=
    measurableSet_Icc.union measurableSet_Icc
  have hdis : Disjoint (Icc (0:ℝ) P.d0 ∪ P.partialValues) P.fixedUpperValues :=
    disjoint_union_left.mpr ⟨P.low_fixedUpper_disjoint, P.partial_fixedUpper_disjoint⟩
  apply ae_mem_of_real_one (valueLaw P)
    (Icc (0:ℝ) P.d0 ∪ P.partialValues ∪ P.fixedUpperValues) (hLP.union measurableSet_Ici)
  rw [measureReal_union hdis measurableSet_Ici,
    measureReal_union P.low_partial_disjoint measurableSet_Icc,
    P.partial_mass, P.fixed_upper_mass]
  have hlow : (valueLaw P).real (Icc (0:ℝ) P.d0) = lowMass P.theta := by
    rw [measureReal_def, P.low_closed_mass,
      ENNReal.toReal_ofReal P.low_mass_pos.le]
  rw [hlow]
  exact mass_sum P.theta

theorem fixed_restriction_partition :
    (valueLaw P).restrict (Icc (0:ℝ) P.d0) +
      (valueLaw P).restrict P.partialValues + P.fixedUpperMeasure = valueLaw P := by
  have hdis : Disjoint (Icc (0:ℝ) P.d0 ∪ P.partialValues) P.fixedUpperValues :=
    disjoint_union_left.mpr ⟨P.low_fixedUpper_disjoint, P.partial_fixedUpper_disjoint⟩
  rw [fixedUpperMeasure,
    ← Measure.restrict_union P.low_partial_disjoint measurableSet_Icc,
    ← Measure.restrict_union hdis measurableSet_Ici,
    Measure.restrict_eq_self_of_ae_mem P.original_support]

theorem upper_moving_partition (t : ℝ) (ht : P.M ≤ t) :
    (valueLaw P).restrict (P.movingActiveValues t) + P.movingUpperMeasure t =
      P.fixedUpperMeasure := by
  have hLt : P.vA-P.w ≤ t := by linarith [P.active_tail_gap, P.w_pos]
  have hdis : Disjoint (P.movingActiveValues t) (P.movingUpperValues t) := by
    apply disjoint_left.mpr
    intro v hv hw
    exact (not_lt.mpr hv.2) hw
  have hun : P.movingActiveValues t ∪ P.movingUpperValues t = P.fixedUpperValues := by
    ext v
    constructor
    · rintro (hv | hv)
      · exact hv.1
      · exact hLt.trans hv.le
    · intro hv
      by_cases hvt : v ≤ t
      · exact Or.inl ⟨hv, hvt⟩
      · exact Or.inr (lt_of_not_ge hvt)
  rw [movingUpperMeasure, fixedUpperMeasure,
    ← Measure.restrict_union hdis measurableSet_Ioi, hun]

theorem moving_restriction_partition (t : ℝ) (ht : P.M ≤ t) :
    (valueLaw P).restrict (Icc (0:ℝ) P.d0) +
      (valueLaw P).restrict P.partialValues +
      (valueLaw P).restrict (P.movingActiveValues t) +
      P.movingUpperMeasure t = valueLaw P := by
  rw [add_assoc ((valueLaw P).restrict (Icc 0 P.d0) +
    (valueLaw P).restrict P.partialValues), P.upper_moving_partition t ht,
    P.fixed_restriction_partition]

theorem weighted_originalPartialLaw :
    ENNReal.ofReal partialMass • P.originalPartialLaw.map Subtype.val =
      (valueLaw P).restrict P.partialValues := by
  have hm : valueLaw P P.partialValues = ENNReal.ofReal partialMass := by
    calc
      _ = ENNReal.ofReal ((valueLaw P).real P.partialValues) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = _ := by rw [P.partial_mass]
  rw [P.originalPartialLaw_real, ← hm, Hybrid.measure_smul_cond]

theorem movingActiveMass_positive (t : ℝ) (ht : P.M ≤ t) :
    0 < activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  have hpow : powerTail P.M 10 t ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      ((le_div_iff₀ P.M_pos).2 (by simpa using ht)) (by norm_num)
  have hp := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg P.active_mass_pos.le P.zeta_pos.le)
  have hz := mul_lt_mul_of_pos_left P.zeta_lt_one P.active_mass_pos
  nlinarith

theorem weighted_originalMovingActiveLaw (t : ℝ) (ht : P.M ≤ t) :
    ENNReal.ofReal (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t) •
      (P.originalMovingActiveLaw t ht).map Subtype.val =
      (valueLaw P).restrict (P.movingActiveValues t) := by
  have hm : valueLaw P (P.movingActiveValues t) =
      ENNReal.ofReal (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t) := by
    calc
      _ = ENNReal.ofReal ((valueLaw P).real (P.movingActiveValues t)) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = _ := by rw [P.moving_active_mass t ht]
  rw [P.originalMovingActiveLaw_real t ht, ← hm, Hybrid.measure_smul_cond]

def originalMovingUpperLaw (t : ℝ) : Measure ℝ :=
  cond (valueLaw P) (P.movingUpperValues t)

theorem originalMovingUpperLaw_probability (t : ℝ) :
    IsProbabilityMeasure (P.originalMovingUpperLaw t) := by
  apply cond_isProbabilityMeasure
  exact (valueLaw_unbounded P t).ne'

include P in
theorem originalMovingUpperLaw_support (t : ℝ) :
    ∀ᵐ v ∂P.originalMovingUpperLaw t, t < v :=
  conditional_mem (valueLaw P) (Ioi t) measurableSet_Ioi

theorem weighted_originalMovingUpperLaw (t : ℝ) (ht : P.M ≤ t) :
    ENNReal.ofReal (activeMass P.theta*P.zeta*powerTail P.M 10 t) •
      P.originalMovingUpperLaw t = P.movingUpperMeasure t := by
  rw [originalMovingUpperLaw, movingUpperMeasure, movingUpperValues,
    ← valueLaw_tail P t ht, Hybrid.measure_smul_cond]

theorem originalMovingUpperLaw_atomless (t : ℝ) :
    NullSingletonClass (P.originalMovingUpperLaw t) := by
  constructor
  intro v
  change cond (valueLaw P) (Ioi t) {v} = 0
  rw [cond_apply measurableSet_Ioi]
  have hz : valueLaw P (Ioi t ∩ {v}) = 0 :=
    measure_mono_null inter_subset_right (measure_singleton v)
  rw [hz, mul_zero]

theorem moving_weighted_value_partition (t : ℝ) (ht : P.M ≤ t) :
    ENNReal.ofReal (lowMass P.theta) • P.originalLowLaw.map Subtype.val +
      ENNReal.ofReal partialMass • P.originalPartialLaw.map Subtype.val +
      ENNReal.ofReal (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t) •
        (P.originalMovingActiveLaw t ht).map Subtype.val +
      ENNReal.ofReal (activeMass P.theta*P.zeta*powerTail P.M 10 t) •
        P.originalMovingUpperLaw t = valueLaw P := by
  rw [P.weighted_originalLowLaw, P.weighted_originalPartialLaw,
    P.weighted_originalMovingActiveLaw t ht, P.weighted_originalMovingUpperLaw t ht]
  exact P.moving_restriction_partition t ht

end FCAppendix.Affine.Tail04.ValueParameters
namespace FCAppendix.Affine.Tail04.OriginalValues
export FCAppendix.Affine.Tail04.ValueParameters (low_partial_disjoint low_fixedUpper_disjoint partial_fixedUpper_disjoint original_support fixed_restriction_partition upper_moving_partition moving_restriction_partition weighted_originalPartialLaw movingActiveMass_positive weighted_originalMovingActiveLaw originalMovingUpperLaw originalMovingUpperLaw_probability originalMovingUpperLaw_support weighted_originalMovingUpperLaw originalMovingUpperLaw_atomless moving_weighted_value_partition)
end FCAppendix.Affine.Tail04.OriginalValues
