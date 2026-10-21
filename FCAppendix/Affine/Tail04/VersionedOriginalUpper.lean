import FCAppendix.Affine.Tail04.OriginalFixedConditional

noncomputable section
namespace FCAppendix.Affine.Tail04.VersionedOriginalUpper
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open OriginalValues

structure Data (P : ValueParameters) (m : ℕ) where
  large : 200 ≤ m
  C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval
  U : ℝ
  R : ℝ
  R_pos : 0 < R
  R_value : R < P.vA-P.w
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  eta_lt_one : eta < 1
  PL : ProbabilityMeasure (ℝ × JointAction 2)
  PA : ProbabilityMeasure (ℝ × JointAction 2)
  PH : ProbabilityMeasure (ℝ × JointAction 2)
  low_value : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = P.originalLowLaw.map Subtype.val
  active_value : (PA : Measure (ℝ × JointAction 2)).map Prod.fst = P.originalPartialLaw.map Subtype.val
  kernel : Kernel ℝ (JointAction 2)
  markov : IsMarkovKernel kernel
  low_kernel : (P.originalLowLaw.map Subtype.val) ⊗ₘ kernel = (PL : Measure (ℝ × JointAction 2))
  active_kernel : (P.originalPartialLaw.map Subtype.val) ⊗ₘ kernel = (PA : Measure (ℝ × JointAction 2))
  reference_version : kernel =ᵐ[(P.originalFixedReference C U R PL PA eta eta_nonneg eta_lt_one PH).F]
    (P.originalFixedReference C U R PL PA eta eta_nonneg eta_lt_one PH).σ
  upper_shape : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)),R ≤ x.2.bid ∧ x.2.routeCount = 1

attribute [instance] Data.markov

namespace Data

variable {P : ValueParameters} {m : ℕ} (D : Data P m)

def baseReference : FiniteGame m 2 (marketCapacity m) unitInterval :=
  P.originalFixedReference D.C D.U D.R D.PL D.PA D.eta D.eta_nonneg D.eta_lt_one D.PH

def reference : FiniteGame m 2 (marketCapacity m) unitInterval :=
  ConditionalVersions.withStrategy D.baseReference D.kernel

def baseOriginal : FiniteGame m 2 (marketCapacity m) unitInterval :=
  P.originalFixedGame D.large D.C D.U D.R D.R_pos D.R_value D.PL D.PA
    D.eta D.eta_nonneg D.eta_lt_one

def originalKernel : Kernel ℝ (JointAction 2) :=
  ValueParameters.fixUpperKernel D.kernel (P.vA-P.w) (P.originalFixedUpperBid m D.R)
    (P.exists_originalFixedUpperJoint m D.large D.R D.R_pos D.R_value).1.measurable

instance originalKernel_markov : IsMarkovKernel D.originalKernel := by
  dsimp only [originalKernel]
  infer_instance

def original : FiniteGame m 2 (marketCapacity m) unitInterval :=
  ConditionalVersions.withStrategy D.baseOriginal D.originalKernel

lemma original_value : D.original.F = valueLaw P :=
  P.originalFixedGame_valueLaw D.large D.C D.U D.R D.R_pos D.R_value D.PL D.PA
    D.low_value D.active_value D.eta D.eta_nonneg D.eta_lt_one

lemma original_joint : D.original.F ⊗ₘ D.original.σ =
    Hybrid.populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
      D.PL D.PA (P.originalFixedUpperJoint m D.large D.R D.R_pos D.R_value) := by
  change D.baseOriginal.F ⊗ₘ D.originalKernel = _
  rw [show D.baseOriginal.F = valueLaw P from D.original_value]
  exact P.originalFixed_borrowed_joint m D.large D.R D.R_pos D.R_value D.PL D.PA
    D.kernel D.low_kernel D.active_kernel

lemma original_kernel_ae : D.originalKernel =ᵐ[D.baseOriginal.F] D.baseOriginal.σ := by
  have hj : D.baseOriginal.F ⊗ₘ D.originalKernel = D.baseOriginal.F ⊗ₘ D.baseOriginal.σ := by
    unfold baseOriginal
    rw [P.originalFixedGame_joint]
    exact D.original_joint
  letI : Nonempty (JointAction 2) := ⟨⟨0,le_rfl,0,by omega⟩⟩
  have h := eq_condKernel_of_measure_eq_compProd (ρ := D.baseOriginal.F ⊗ₘ D.baseOriginal.σ)
    D.originalKernel (by rw [Measure.fst_compProd];exact hj.symm)
  have hae : D.originalKernel =ᵐ[D.baseOriginal.F]
      (D.baseOriginal.F ⊗ₘ D.baseOriginal.σ).condKernel := by
    convert! h using 1
    rw [Measure.fst_compProd]
    rfl
  exact hae.trans (condKernel_compProd D.baseOriginal.F D.baseOriginal.σ)

lemma original_problem (i : Fin m) : problem D.original i = problem D.baseOriginal i :=
  ConditionalVersions.withStrategy_problem D.baseOriginal D.originalKernel D.original_kernel_ae i

lemma reference_problem (i : Fin m) : problem D.reference i = problem D.baseReference i :=
  ConditionalVersions.withStrategy_problem D.baseReference D.kernel D.reference_version i

lemma lower_kernel (v : ℝ) (hv : v < P.vA-P.w) : D.original.σ v = D.reference.σ v :=
  ValueParameters.fixUpperKernel_below D.kernel (P.vA-P.w) (P.originalFixedUpperBid m D.R)
    (P.exists_originalFixedUpperJoint m D.large D.R D.R_pos D.R_value).1.measurable v hv

lemma upper_kernel (v : ℝ) (hv : P.vA-P.w ≤ v) :
    D.original.σ v = Measure.dirac (Hybrid.upperAction (P.originalFixedUpperBid m D.R) v) :=
  ValueParameters.fixUpperKernel_at_value D.kernel (P.vA-P.w) (P.originalFixedUpperBid m D.R)
    (P.exists_originalFixedUpperJoint m D.large D.R D.R_pos D.R_value).1.measurable v hv

lemma lower_count (i : Fin m) (act : JointAction 2) (ha : act.bid < D.R) :
    (problem D.original i).outcome act = (problem D.reference i).outcome act := by
  rw [D.original_problem i,D.reference_problem i]
  exact P.originalFixedGame_lower_count D.large D.C D.U D.R D.R_pos D.R_value
    D.PL D.PA D.eta D.eta_nonneg D.eta_lt_one D.PH D.upper_shape i act ha

lemma lower_payoff (i : Fin m) (v : ℝ) (act : JointAction 2) (ha : act.bid < D.R) :
    (problem D.original i).payoff v act = (problem D.reference i).payoff v act := by
  rw [D.original_problem i,D.reference_problem i]
  exact P.originalFixedGame_lower_payoff D.large D.C D.U D.R D.R_pos D.R_value
    D.PL D.PA D.eta D.eta_nonneg D.eta_lt_one D.PH D.upper_shape i v act ha

lemma lower_expect (v : ℝ) (hv : v < P.vA-P.w)
    (hband : ∀ᵐ act ∂D.reference.σ v,act.bid < D.R) (f : Fin 3 → ℝ) :
    (conditionalTypeCountLaw D.original (by have := D.large;omega) v).expect f =
      (conditionalTypeCountLaw D.reference (by have := D.large;omega) v).expect f := by
  rw [conditionalTypeCountLaw_expect,conditionalTypeCountLaw_expect,D.lower_kernel v hv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hband] with act ha
  rw [D.lower_count i act ha]

end Data
end FCAppendix.Affine.Tail04.VersionedOriginalUpper
