import FCAppendix.Affine.Tail04.NativeVersionedProposers

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

lemma normalized_value (k : ℕ) : (normalizedGame s hs V k).F = valueLaw P :=
  (data s hs V (k+200) (large s hs V k)).original_value

lemma normalized_joint_bid_atomless (k : ℕ) (y : ℝ) :
    ((normalizedGame s hs V k).F ⊗ₘ (normalizedGame s hs V k).σ) {x | x.2.bid=y} = 0 := by
  change ((data s hs V (k+200) (large s hs V k)).original.F ⊗ₘ
    (data s hs V (k+200) (large s hs V k)).original.σ) _ = 0
  rw [(data s hs V (k+200) (large s hs V k)).original_joint]
  have hL := row_bid_atomless s hs V (lowValue (P := P)) (low_ac s) (k+200) y
  have hA := row_bid_atomless s hs V (activeValue (P := P)) (active_ac s) (k+200) y
  have hH := (P.originalFixedUpperJoint_properties (V.toNativeFamilyData.M (k+200))
    (large s hs V k) s.scalar.R s.scalar.floor_pos s.scalar.floor_below_upper).2.2.2 y
  simp only [populationJoint,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
  change ENNReal.ofReal (lowMass P.theta)*
      (row (lowValue (P := P)) (V.toNativeFamilyData.game (k+200)).σ : Measure (ℝ × JointAction 2)) _ +
    ENNReal.ofReal partialMass*
      (row (activeValue (P := P)) (V.toNativeFamilyData.game (k+200)).σ : Measure (ℝ × JointAction 2)) _ +
    ENNReal.ofReal (activeMass P.theta)*
      (P.originalFixedUpperJoint (V.toNativeFamilyData.M (k+200)) (large s hs V k) s.scalar.R
        s.scalar.floor_pos s.scalar.floor_below_upper : Measure (ℝ × JointAction 2)) {x | x.2.bid=y} = 0
  rw [hL,hA,hH]
  simp only [mul_zero,zero_add]

lemma normalized_bid_atomless (k : ℕ) : NullSingletonClass (Bayes.realBidLaw (normalizedGame s hs V k)) := by
  refine ⟨fun y => ?_⟩
  rw [Bayes.realBidLaw_eq_action_map,Measure.map_apply
    (show Measurable (fun x : ℝ × JointAction 2 => x.2.bid) from
      (measurable_bid 2).comp measurable_snd) (measurableSet_singleton y)]
  exact normalized_joint_bid_atomless s hs V k y

lemma normalized_visible_atomless (k : ℕ) : VisibleAtomless (normalizedGame s hs V k) := by
  intro j y
  have hz : userLaw (normalizedGame s hs V k) {z : UserDraw 2 | z.1.2.bid=y}=0 := by
    have he : {z : UserDraw 2 | z.1.2.bid=y}=
        {x : ℝ × JointAction 2 | x.2.bid=y} ×ˢ univ := by
      ext z
      simp
    rw [he,userLaw,Measure.prod_prod,normalized_joint_bid_atomless s hs V k y,zero_mul]
  exact measure_mono_null (fun _ hx => hx.2) hz

end FCAppendix.Affine.Tail04.NativeVersionedSource
