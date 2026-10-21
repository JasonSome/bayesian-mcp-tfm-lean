import Mathlib

noncomputable section
namespace FCAppendix.Affine.Tail04.WeakProbability
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal

structure Law (X : Type*) [MeasurableSpace X] where
  val : ProbabilityMeasure X

abbrev mk {X : Type*} [MeasurableSpace X] (μ : ProbabilityMeasure X) : Law X := Law.mk μ

@[simp] lemma val_mk {X : Type*} [MeasurableSpace X] (μ : ProbabilityMeasure X) :
    (mk μ).val=μ := rfl

@[simp] lemma mk_val {X : Type*} [MeasurableSpace X] (μ : Law X) : mk μ.val=μ := by
  cases μ
  rfl

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

instance : TopologicalSpace (Law X) := TopologicalSpace.induced Law.val inferInstance
instance : MeasurableSpace (Law X) := borel (Law X)
instance : BorelSpace (Law X) := ⟨rfl⟩

def homeomorph : Law X ≃ₜ ProbabilityMeasure X where
  toEquiv := {
    toFun := Law.val
    invFun := Law.mk
    left_inv := by intro μ; cases μ; rfl
    right_inv := fun _ => rfl }
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance [CompactSpace (ProbabilityMeasure X)] : CompactSpace (Law X) :=
  (homeomorph (X := X)).symm.compactSpace

instance [MetrizableSpace (ProbabilityMeasure X)] : MetrizableSpace (Law X) :=
  (homeomorph (X := X)).isEmbedding.metrizableSpace

instance [Nonempty X] : Nonempty (Law X) :=
  ⟨⟨⟨Measure.dirac (Classical.arbitrary X),inferInstance⟩⟩⟩

def toMeasure (μ : Law X) : Measure X := (μ.val : Measure X)

instance (μ : Law X) : IsProbabilityMeasure (toMeasure μ) :=
  (show IsProbabilityMeasure (μ.val : Measure X) from inferInstance)

lemma continuous_val : Continuous (Law.val : Law X → ProbabilityMeasure X) :=
  (homeomorph (X := X)).continuous

lemma continuous_mk : Continuous (Law.mk : ProbabilityMeasure X → Law X) :=
  (homeomorph (X := X)).symm.continuous

lemma measurable_toMeasure [BorelSpace X] [PseudoMetrizableSpace X] :
    Measurable (toMeasure : Law X → Measure X) := by
  have hgen : (inferInstance : MeasurableSpace X) =
      MeasurableSpace.generateFrom {s : Set X | IsClosed s} := by
    rw [BorelSpace.measurable_eq (α := X),borel_eq_generateFrom_isClosed]
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure hgen isPiSystem_isClosed
  intro F hF
  have hf (n : ℕ) : Measurable (fun μ : Law X =>
      ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂toMeasure μ) := by
    exact ((ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (hF.apprSeq n)).comp continuous_val).measurable
  apply measurable_of_tendsto_metrizable hf
  apply tendsto_pi_nhds.mpr
  intro μ
  exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (toMeasure μ)

lemma measurable_apply [BorelSpace X] [PseudoMetrizableSpace X]
    {s : Set X} (hs : MeasurableSet s) : Measurable (fun μ : Law X => toMeasure μ s) :=
  (Measure.measurable_coe hs).comp measurable_toMeasure

def kernel {P : Type*} [MeasurableSpace P] [BorelSpace X] [PseudoMetrizableSpace X]
    (f : P → Law X) (hf : Measurable f) : Kernel P X where
  toFun := fun p => toMeasure (f p)
  measurable' := measurable_toMeasure.comp hf

instance {P : Type*} [MeasurableSpace P] [BorelSpace X] [PseudoMetrizableSpace X]
    (f : P → Law X) (hf : Measurable f) : IsMarkovKernel (kernel f hf) where
  isProbabilityMeasure := fun p =>
    (show IsProbabilityMeasure (toMeasure (f p)) from inferInstance)

@[simp] lemma kernel_apply {P : Type*} [MeasurableSpace P]
    [BorelSpace X] [PseudoMetrizableSpace X] (f : P → Law X) (hf : Measurable f) (p : P) :
    kernel f hf p = toMeasure (f p) := rfl

end FCAppendix.Affine.Tail04.WeakProbability
