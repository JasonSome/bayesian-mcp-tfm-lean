import FCAppendix.Affine.Tail04.OrderedAtomBetaControl
import FCAppendix.Affine.Tail04.OrderedAtomActiveAtomless
import FCAppendix.Affine.Tail04.OrderedSourceFiniteStartingPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomStartingPoint
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open OrderedOriginalNoisySequence NativeNoisySource SourceMovingScalarGuards OrderedSourceFiniteStartingPoint
open OrderedAtomClusterLaws OrderedAtomContraction OrderedAtomActiveAtomless
open OrderedAtomBetaControl SourceActiveErrorRates SourceMomentRectangle SourceMenuPopulation MenuError

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)

section Fixed
variable {N : ℕ} (Z : StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw (N+1))

local notation "D" => OrderedSourceFiniteStartingPoint.data P ξ Up u k width
  hξ hξh hu hRUp hUp hw (N+1) Z.range
local notation "tN" => cutoff (N+1)
local notation "htN" => Z.range.cutoff_gt_M

lemma low_lt_partial (hlow : P.d0<1-ξ) : P.d0< (D).R := by
  change P.d0< Central.R ξ
  unfold Central.R
  linarith

lemma physical_lt_floor : (D).B< Central.B ξ+1 :=
  (D).hUF.trans_lt (lt_add_of_pos_right _ (by norm_num))

include Z in
lemma rare_guard : (1-(D).ξ)*(D).B+(D).ξ*(D).B*((N+2:ℕ)*
    (tailMass P tN/(partialMass+tailMass P tN)))≤ (D).R := by
  have h := Z.range.owner_receipt_guard
  have hc : (N:ℝ)+1+1=(N:ℝ)+2 := by ring
  simpa only [OrderedSourceFiniteStartingPoint.data,SourceNoisyData.data,Data.B,commonPhysical,
    noise,tailMass,upperMass,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hc] using h

lemma source_cap : (D).c=twoCapacity (99/200) N := by
  change iidCapacity (99/200) (N+1)=twoCapacity (99/200) N
  simp only [iidCapacity,twoCapacity,Nat.cast_add,Nat.cast_one]
  congr 2
  ring

include Z in
lemma remaining_positive : 0< N := by
  simpa only [Nat.add_sub_cancel] using Z.range.two_fixed_positive

lemma physical_cap_ge_one : 1≤ (D).B := by
  change 1≤ (D).U*(1+(D).eps)
  nlinarith [(D).hU,mul_nonneg ((by norm_num : (0:ℝ)≤1).trans (D).hU) (D).heps.le]

include Z in
lemma cap_room : (D).B≤ Central.B ξ-(k/2)/tN := by
  have h := Z.range.flag_endpoint_gap
  change k/(2*tN)≤ Central.B ξ-(D).B at h
  have he : k/(2*tN)=(k/2)/tN := by ring
  rw [he] at h
  linarith

include P ξ Up u width hξ hξh hu hRUp hUp hw Z in
lemma physical_below_flag (hk : 0< k) : (D).B< (D).F := by
  have h := cap_room P ξ Up u k width hξ hξh hu hRUp hUp hw Z
  have hpos : 0<(k/2)/tN := div_pos (half_pos hk) (P.M_pos.trans htN)
  change (D).B< Central.B ξ
  linarith

include ξ in
lemma flag_endpoint_le_two : (D).F≤2 := by
  change Central.B ξ≤2
  unfold Central.B
  linarith

theorem beta_control (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ) :
    ConditionalBetaControl D P tN htN
      (low_lt_partial P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)
      (Central.B ξ+1) (physical_lt_floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z) N
      Z.low.joint (fun _ : ℝ => Central.B ξ+1) measurable_const Z.sequence
      (sourceError P ξ N) := by
  apply original_conditional_beta_control D P tN htN
    (low_lt_partial P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)
    (Central.B ξ+1) (physical_lt_floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z) N
    Z.low.joint (fun _ : ℝ => Central.B ξ+1) measurable_const
    (fun _ _ => le_rfl) Z.sequence
      (source_cap P ξ Up u k width hξ hξh hu hRUp hUp hw Z)
      (remaining_positive P ξ Up u k width hξ hξh hu hRUp hUp hw Z)
      hξh rfl rfl (fun reg => by cases reg <;> rfl)
  · exact Z.range.budget_le_one
  · exact Z.range.bulk_below_nominal
  · exact Z.range.partial_guard
  · exact Z.range.moment_guard
  · exact Z.range.upper_mass_guard
  · exact hwγ
  · have hroom : ∀ reg,32/(N:ℝ)≤radius (D).ξ (centerMoment P reg) :=
      Z.range.two_fixed_room
    simpa only [Nat.add_sub_cancel] using hroom
  · exact rare_guard P ξ Up u k width hξ hξh hu hRUp hUp hw Z

end Fixed

theorem eventually_active_atomless (hk : 0< k) (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ Z : StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw (N+1),
      ∀ bulkCut tailCut : ℝ,bulkCut<1+u → tailCut< cap ξ k (N+1) →
      (∀ j,(ProbabilityMeasure.toMeasure (Z.sequence.law j 0).1) {x | bulkCut<(x.2:ℝ)}=0) →
      (∀ᶠ j in atTop,(ProbabilityMeasure.toMeasure (Z.sequence.law j 1).1) {x | tailCut<(x.2:ℝ)}=0) →
      let D := OrderedSourceFiniteStartingPoint.data P ξ Up u k width
        hξ hξh hu hRUp hUp hw (N+1) Z.range
      NullSingletonClass (baseRealLaw D P (cutoff (N+1)) Z.range.cutoff_gt_M Z.sequence.limit : Measure ℝ) ∧
      NullSingletonClass (Sequence.realBaseLaw 0 Z.sequence.limit : Measure ℝ) ∧
      NullSingletonClass (Sequence.realBaseLaw 1 Z.sequence.limit : Measure ℝ) := by
  have hr := (tendsto_add_atTop_nat 1).eventually
    (SourceActiveErrorRates.eventually_strict P hξ hξh hw hk)
  filter_upwards [hr] with N hstrict
  intro Z bulkCut tailCut hbulk htail hB hT
  let D := OrderedSourceFiniteStartingPoint.data P ξ Up u k width
    hξ hξh hu hRUp hUp hw (N+1) Z.range
  let ht := Z.range.cutoff_gt_M
  have hs := hstrict (D).B (cap_room P ξ Up u k width hξ hξh hu hRUp hUp hw Z)
  simp only [Nat.add_sub_cancel] at hs
  have hc := common_atomless D P (cutoff (N+1)) ht
    (low_lt_partial P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)
    (Central.B ξ+1) (physical_lt_floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z) N
    Z.low.joint (fun _ : ℝ => Central.B ξ+1) measurable_const (fun _ _ => le_rfl) Z.sequence
      (remaining_positive P ξ Up u k width hξ hξh hu hRUp hUp hw Z)
      hξh rfl Z.range.budget_le_one
      (physical_cap_ge_one P ξ Up u k width hξ hξh hu hRUp hUp hw Z) le_rfl
      (physical_below_flag P ξ Up u k width hξ hξh hu hRUp hUp hw Z hk)
      (flag_endpoint_le_two P ξ Up u k width hξ hξh hu hRUp hUp hw Z)
      (rare_guard P ξ Up u k width hξ hξh hu hRUp hUp hw Z)
      (sourceError_nonneg P ξ N) hs
      (beta_control P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hwγ)
      hbulk htail hB hT
  exact ⟨hc,component_atomless D P (cutoff (N+1)) ht Z.sequence.limit hc⟩

end FCAppendix.Affine.Tail04.OrderedAtomStartingPoint
