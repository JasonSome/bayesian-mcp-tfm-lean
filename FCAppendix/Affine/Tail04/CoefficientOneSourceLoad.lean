import FCAppendix.Affine.Tail04.OriginalFixedCountFamily
import FCAppendix.Affine.Tail04.SourceValuePartition

noncomputable section
namespace FCAppendix.Affine.Tail04.CoefficientOne
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open OriginalValues

namespace BoundedSource
attribute [local instance] Classical.propDecidable
variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)

theorem partialLimit_load (v : ℝ) (hv : v∈P.partialValues) :
    (s.partialLimit hs v hv).load=
      s.scalar.ownerMass+s.scalar.mixedMass*(2*s.q v) := by
  have h:=s.partialLimit_expect hs v hv (fun r : Fin 3=>(r.val:ℝ))
  norm_num only [Fin.val_one,Nat.cast_one] at h
  change (s.partialLimit hs v hv).load=s.scalar.ownerMass*1+
    s.scalar.mixedMass*(IndependentCounts.binomial 2 (s.q v)
      (hs.q_interior v hv).1.le (hs.q_interior v hv).2.le).load at h
  rw [IndependentCounts.binomial_load] at h
  simpa only [Nat.cast_ofNat,mul_one] using h

theorem fullLimit_load_formula (v : ℝ) :
    (s.fullLimit hs v).load=
      if P.vA-P.w≤ v then 1 else
        if v∈P.partialValues then
          s.scalar.ownerMass+s.scalar.mixedMass*(2*s.q v) else 0 := by
  by_cases hH : P.vA-P.w≤ v
  · simp only [fullLimit,if_pos hH,CountLaw.load,FiniteLaw.expect_dirac]
    norm_num
  · by_cases hP : v∈P.partialValues
    · simp only [fullLimit,if_neg hH,lowerLimit,dif_pos hP,if_pos hP,
        s.partialLimit_load hs v hP]
    · simp only [fullLimit,if_neg hH,lowerLimit,dif_neg hP,if_neg hP,
        CountLaw.load,FiniteLaw.expect_dirac]
      norm_num

theorem measurable_fullLimit_load : Measurable (fun v=>(s.fullLimit hs v).load) := by
  simp_rw [s.fullLimit_load_formula hs]
  apply Measurable.ite measurableSet_Ici measurable_const
  apply Measurable.ite measurableSet_Icc
  · exact measurable_const.add
      (measurable_const.mul (measurable_const.mul s.q_measurable))
  · exact measurable_const

theorem integrable_fullLimit_load (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun v=>(s.fullLimit hs v).load) μ := by
  apply (integrable_const (2:ℝ)).mono' (s.measurable_fullLimit_load hs).aestronglyMeasurable
  exact Eventually.of_forall (fun v=> by
    rw [Real.norm_eq_abs,abs_of_nonneg (s.fullLimit hs v).load_nonneg]
    exact (s.fullLimit hs v).load_le_n)

theorem original_low_load :
    (∫v,(s.fullLimit hs v).load ∂(valueLaw P).restrict (Icc (0:ℝ) P.d0))=0 := by
  calc
    _=(∫_v : ℝ,(0:ℝ) ∂(valueLaw P).restrict (Icc (0:ℝ) P.d0)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      rw [s.fullLimit_low hs v hv]
      simp [CountLaw.load,FiniteLaw.expect_dirac]
    _=0 := by simp

theorem original_partial_load :
    (∫v,(s.fullLimit hs v).load ∂(valueLaw P).restrict P.partialValues)=
      partialMass*(s.scalar.ownerMass+s.scalar.mixedMass*(2*(3/5))) := by
  letI : IsProbabilityMeasure (P.originalPartialLaw.map Subtype.val) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  have hP : ∀ᵐv ∂P.originalPartialLaw.map Subtype.val,v∈P.partialValues := by
    rw [P.originalPartialLaw_real]
    exact conditional_mem (valueLaw P) P.partialValues measurableSet_Icc
  have hq : Integrable s.q (P.originalPartialLaw.map Subtype.val) := by
    apply (integrable_const (1:ℝ)).mono' s.q_measurable.aestronglyMeasurable
    filter_upwards [hP] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (hs.q_interior v hv).1.le]
    exact (hs.q_interior v hv).2.le
  rw [←P.weighted_originalPartialLaw,integral_smul_measure,
    ENNReal.toReal_ofReal (by norm_num [partialMass])]
  change partialMass*(∫v,(s.fullLimit hs v).load ∂P.originalPartialLaw.map Subtype.val)=_
  congr 1
  calc
    _=(∫v,s.scalar.ownerMass+s.scalar.mixedMass*(2*s.q v)
        ∂P.originalPartialLaw.map Subtype.val) := by
      apply integral_congr_ae
      filter_upwards [hP] with v hv
      rw [s.fullLimit_partial hs v hv,s.partialLimit_load hs v hv]
    _=s.scalar.ownerMass+s.scalar.mixedMass*(2*(3/5)) := by
      rw [integral_add (integrable_const _) ((hq.const_mul 2).const_mul _),
        integral_const,integral_const_mul,integral_const_mul,hs.q_mean]
      simp only [probReal_univ,one_smul]

theorem original_upper_load :
    (∫v,(s.fullLimit hs v).load ∂P.fixedUpperMeasure)=activeMass P.theta := by
  calc
    _=(∫_v : ℝ,(1:ℝ) ∂P.fixedUpperMeasure) := by
      apply integral_congr_ae
      filter_upwards [P.fixedUpperMeasure_support] with v hv
      rw [s.fullLimit_upper hs v hv]
      simp [CountLaw.load,FiniteLaw.expect_dirac]
    _=activeMass P.theta := by
      rw [integral_const]
      change P.fixedUpperMeasure.real univ*1=activeMass P.theta
      rw [P.fixedUpperMeasure_mass,mul_one]

theorem source_load_clearing :
    partialMass*(s.scalar.ownerMass+s.scalar.mixedMass*(2*(3/5)))+
      activeMass P.theta=99/100 := by
  have he : 1-s.scalar.ownerMass=s.scalar.mixedMass := by
    unfold ScalarInput.ownerMass
    ring
  have hc:= (div_eq_iff (sub_pos.mpr s.scalar.ownerMass_bounds.2).ne').mp
    s.scalar.source_qbar
  rw [he] at hc
  norm_num [partialMass,div_eq_mul_inv] at hc ⊢
  nlinarith

theorem fullLimit_load_integral :
    (∫v,(s.fullLimit hs v).load ∂valueLaw P)=99/100 := by
  calc
    _=(∫v,(s.fullLimit hs v).load ∂(valueLaw P).restrict (Icc (0:ℝ) P.d0))+
      (∫v,(s.fullLimit hs v).load ∂(valueLaw P).restrict P.partialValues)+
      (∫v,(s.fullLimit hs v).load ∂P.fixedUpperMeasure) := by
        conv_lhs => rw [←P.fixed_restriction_partition]
        rw [integral_add_measure (s.integrable_fullLimit_load hs _)
          (s.integrable_fullLimit_load hs _),
          integral_add_measure (s.integrable_fullLimit_load hs _)
            (s.integrable_fullLimit_load hs _)]
    _=99/100 := by
      rw [s.original_low_load hs,s.original_partial_load hs,
        s.original_upper_load hs,zero_add]
      exact s.source_load_clearing

end BoundedSource

end FCAppendix.Affine.Tail04.CoefficientOne
