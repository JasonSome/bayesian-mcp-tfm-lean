import FCAppendix.Affine.Tail04.NativeVersionedRows

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

def context (k : ℕ) : ContextPolicy (V.toNativeFamilyData.M k)
    (marketCapacity (V.toNativeFamilyData.M k)) unitInterval :=
  FullContext.contextPolicy (NativeSource.input s hs).xi_pos (NativeSource.input s hs).xi_lt_one
    P.d0 s.L s.scalar.U s.scalar.ownerMass (marketCapacity (V.toNativeFamilyData.M k))
    (V.source.lowLaw (V.toNativeFamilyData.index k))

lemma upper_shape (k : ℕ) : ∀ᵐ x ∂(row s.FH0 (V.toNativeFamilyData.game k).σ :
    Measure (ℝ × JointAction 2)),s.scalar.R ≤ x.2.bid ∧ x.2.routeCount = 1 := by
  have hfull : ∀ᵐ v ∂s.valueMeasure,v ∈ V.valueSet := by
    rw [← NativeSource.input_original_values s hs]
    exact V.full_valueSet
  apply Measure.ae_compProd_of_ae_ae
    ((measurableSet_le measurable_const ((measurable_bid 2).comp measurable_snd)).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))
  filter_upwards [(upper_ac s).ae_le hfull,s.upper_value_support] with v hv hband
  exact (V.common_bands v hv k).mono (fun a ha => ha.2.2 (by
    change 2+P.w < v
    exact P.partial_active_gap.trans_le hband.1))

def data (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    VersionedOriginalUpper.Data P (V.toNativeFamilyData.M k) where
  large := hk
  C := context s hs V k
  U := s.scalar.U
  R := s.scalar.R
  R_pos := s.scalar.floor_pos
  R_value := s.scalar.floor_below_upper
  eta := s.scalar.eta
  eta_nonneg := s.scalar.eta_pos.le
  eta_lt_one := s.scalar.eta_lt_one
  PL := row (lowValue (P := P)) (V.toNativeFamilyData.game k).σ
  PA := row (activeValue (P := P)) (V.toNativeFamilyData.game k).σ
  PH := row s.FH0 (V.toNativeFamilyData.game k).σ
  low_value := row_value _ _
  active_value := row_value _ _
  kernel := (V.toNativeFamilyData.game k).σ
  markov := inferInstance
  low_kernel := rfl
  active_kernel := rfl
  reference_version := reference_kernel s hs _ _
  upper_shape := upper_shape s hs V k

lemma original_value (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    (data s hs V k hk).original.F = valueLaw P :=
  (data s hs V k hk).original_value

lemma original_lower_kernel (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k)
    (v : ℝ) (hv : v < P.vA-P.w) :
    (data s hs V k hk).original.σ v = (V.toNativeFamilyData.game k).σ v :=
  (data s hs V k hk).lower_kernel v hv

lemma joint_reference (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
      (data s hs V k hk).PL (data s hs V k hk).PA (data s hs V k hk).PH =
      (V.source.P (V.toNativeFamilyData.index k) : Measure (ℝ × JointAction 2)) := by
  change populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
    (row (lowValue (P := P)) (V.toNativeFamilyData.game k).σ)
    (row (activeValue (P := P)) (V.toNativeFamilyData.game k).σ)
    (row s.FH0 (V.toNativeFamilyData.game k).σ) = _
  rw [population_row s,← NativeSource.input_original_values s hs,
    ← V.toNativeFamilyData.original_F k,V.toNativeFamilyData.joint_original k]
  rfl

lemma base_reference_eq (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    (data s hs V k hk).baseReference = V.toNativeFamilyData.baseGame k := by
  have hp : populationLaw (lowMass P.theta) partialMass (activeMass P.theta)
      P.low_mass_pos.le (by norm_num [partialMass]) P.active_mass_pos.le (mass_sum P.theta)
      (data s hs V k hk).PL (data s hs V k hk).PA (data s hs V k hk).PH =
      V.source.P (V.toNativeFamilyData.index k) := by
    apply Subtype.ext
    exact joint_reference s hs V k hk
  change ClosedUpperPriority.nativeGame (context s hs V k)
    (PopulationGame.game _ _ _ s.scalar.eta s.scalar.eta_pos.le s.scalar.eta_lt_one s.scalar.U)
    s.scalar.R = _
  rw [hp,NativeClosedCarrier.game_eq _ _ _ s.scalar.floor_pos.le]
  rfl

lemma reference_eq (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    (data s hs V k hk).reference = V.toNativeFamilyData.game k := by
  change ConditionalVersions.withStrategy (data s hs V k hk).baseReference
    (V.toNativeFamilyData.game k).σ = _
  rw [base_reference_eq s hs V k hk]
  rfl

end FCAppendix.Affine.Tail04.NativeVersionedSource
