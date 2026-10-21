import FCAppendix.Affine.Tail04.VersionedOriginalUpper
import FCAppendix.Affine.Tail04.BoundedSourceNativeInput
import FCAppendix.Affine.Tail04.NativeClosedCarrier

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedRows
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)

include hs in
lemma source_probability : IsProbabilityMeasure s.valueMeasure := by
  rw [← NativeSource.input_original_values s hs]
  infer_instance

def row (mu : ProbabilityMeasure ℝ) (sigma : Kernel ℝ (JointAction 2))
    [IsMarkovKernel sigma] : ProbabilityMeasure (ℝ × JointAction 2) :=
  ⟨(mu : Measure ℝ) ⊗ₘ sigma,inferInstance⟩

lemma row_value (mu : ProbabilityMeasure ℝ) (sigma : Kernel ℝ (JointAction 2))
    [IsMarkovKernel sigma] :
    (row mu sigma : Measure (ℝ × JointAction 2)).map Prod.fst = mu :=
  Measure.fst_compProd _ _

def lowValue : ProbabilityMeasure ℝ :=
  ⟨P.originalLowLaw.map Subtype.val,Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable⟩
def activeValue : ProbabilityMeasure ℝ :=
  ⟨P.originalPartialLaw.map Subtype.val,Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable⟩

lemma population_row (sigma : Kernel ℝ (JointAction 2)) [IsMarkovKernel sigma] :
    populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
      (row (lowValue (P := P)) sigma) (row (activeValue (P := P)) sigma) (row s.FH0 sigma) =
      s.valueMeasure ⊗ₘ sigma := by
  simp only [BoundedSource.valueMeasure,Measure.compProd_add_left,Measure.compProd_smul_left,
    populationJoint,row,lowValue,activeValue]
  rfl

lemma low_ac : (P.originalLowLaw.map Subtype.val) ≪ s.valueMeasure := by
  apply (Measure.absolutelyContinuous_smul ((ENNReal.ofReal_pos.mpr P.low_mass_pos).ne')).trans
  apply Measure.absolutelyContinuous_of_le
  exact le_trans (Measure.le_add_right le_rfl) (Measure.le_add_right le_rfl)

lemma active_ac : (P.originalPartialLaw.map Subtype.val) ≪ s.valueMeasure := by
  apply (Measure.absolutelyContinuous_smul ((ENNReal.ofReal_pos.mpr (by norm_num [partialMass] : (0:ℝ) < partialMass)).ne')).trans
  apply Measure.absolutelyContinuous_of_le
  exact le_trans (Measure.le_add_left le_rfl) (Measure.le_add_right le_rfl)

lemma upper_ac : (s.FH0 : Measure ℝ) ≪ s.valueMeasure := by
  apply (Measure.absolutelyContinuous_smul ((ENNReal.ofReal_pos.mpr P.active_mass_pos).ne')).trans
  exact (Measure.le_add_left le_rfl).absolutelyContinuous

include hs in
lemma reference_kernel {m : ℕ} (C : ContextPolicy m (marketCapacity m) unitInterval)
    (sigma : Kernel ℝ (JointAction 2)) [IsMarkovKernel sigma] :
    sigma =ᵐ[(P.originalFixedReference C s.scalar.U s.scalar.R
      (row (lowValue (P := P)) sigma) (row (activeValue (P := P)) sigma)
      s.scalar.eta s.scalar.eta_pos.le s.scalar.eta_lt_one (row s.FH0 sigma)).F]
      (P.originalFixedReference C s.scalar.U s.scalar.R
      (row (lowValue (P := P)) sigma) (row (activeValue (P := P)) sigma)
      s.scalar.eta s.scalar.eta_pos.le s.scalar.eta_lt_one (row s.FH0 sigma)).σ := by
  letI := source_probability s hs
  letI : Nonempty (JointAction 2) := ⟨⟨0,le_rfl,0,by omega⟩⟩
  letI : IsProbabilityMeasure (populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
      (row (lowValue (P := P)) sigma) (row (activeValue (P := P)) sigma) (row s.FH0 sigma)) := by
    rw [population_row s sigma]
    infer_instance
  change sigma =ᵐ[(populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
    (row (lowValue (P := P)) sigma) (row (activeValue (P := P)) sigma) (row s.FH0 sigma)).map Prod.fst]
    (populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
    (row (lowValue (P := P)) sigma) (row (activeValue (P := P)) sigma) (row s.FH0 sigma)).condKernel
  apply eq_condKernel_of_measure_eq_compProd sigma
  rw [population_row s sigma,Measure.fst_compProd]

end FCAppendix.Affine.Tail04.NativeVersionedRows
