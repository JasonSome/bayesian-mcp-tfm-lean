import FCAppendix.Affine.Tail04.OrderedSourceActiveCountData

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceActiveSpecified
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceFiniteStartingPoint
open SourceMovingScalarGuards SourceMomentRectangle SourceMenuPopulation MenuError
open OrderedSourceRestrictedNative OrderedSourceActiveCountData ActiveFixedValueVersions

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {N : ℕ} (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)

def bulkCondition : ℝ×JointAction 2→ Prop :=
  condition P ξ (1+u) (by linarith) (P.vA-P.w) (P.vA+P.w)
    (lambda A hlow) (rate P ξ N)

def tailCondition : ℝ×JointAction 2→ Prop :=
  condition P ξ A.D.U A.D.hU P.M (cutoff N) (lambda A hlow) (rate P ξ N)

lemma measurable_conditions : MeasurableSet {x | bulkCondition A hlow x ∧ tailCondition A hlow x} :=
  (measurableSet_condition P ξ (1+u) (by linarith) _ _ _ _).inter
    (measurableSet_condition P ξ A.D.U A.D.hU _ _ _ _)

theorem original_conditions (hwγ : width≤ γ ξ) :
    ∀ᵐx ∂(A.native hlow).F⊗ₘ(A.native hlow).σ,
      bulkCondition A hlow x ∧ tailCondition A hlow x := by
  apply original_joint_ae A hlow
  · apply (ae_map_iff (measurable_fst.subtype_val.prodMk
      ((measurable_lowBroadcast P.d0).comp measurable_snd)).aemeasurable
      (measurable_conditions A hlow)).mpr
    exact Eventually.of_forall fun x=> by
      constructor <;> intro hv <;>
        exfalso <;> dsimp [bulkCondition,tailCondition,condition] at hv <;>
        linarith [x.1.2.2,hv.1,P.low_partial_gap,P.partial_active_gap,P.active_tail_gap,P.w_pos]
  · filter_upwards [bandJoint_support (bidLo_pos A.D 2).le 1 (by norm_num)
      (originalValueLaw P (cutoff N) A.point.range.cutoff_gt_M 2) (A.sequence.limit 2)] with x hx
    constructor <;> intro hv <;> exfalso <;>
      dsimp [bulkCondition,tailCondition,condition,valueLo,valueHi] at hv hx <;>
      linarith [hx.1.2,hv.1,P.partial_active_gap,P.active_tail_gap,P.w_pos]
  · filter_upwards [band_regret A hlow hwγ 0 (by decide)] with x hx
    constructor
    · apply (condition_iff P ξ (1+u) (by linarith) _ _ _ _ x).mpr
      intro _
      exact ⟨hx.2.1,hx.2.2.1,hx.2.2.2⟩
    · intro hv
      exfalso
      have hvB : x.1≤ P.vA+P.w:=hx.1.2
      linarith [hv.1,P.active_tail_gap]
  · filter_upwards [band_regret A hlow hwγ 1 (by decide)] with x hx
    constructor
    · intro hv
      exfalso
      have hvT : P.M≤ x.1:=hx.1.1
      linarith [hv.2,P.active_tail_gap]
    · apply (condition_iff P ξ A.D.U A.D.hU _ _ _ _ x).mpr
      intro _
      exact ⟨hx.2.1,hx.2.2.1,hx.2.2.2⟩
  · apply (ae_map_iff (measurable_id.prodMk
      (measurable_upperAction A.upperBid A.upperBid_measurable)).aemeasurable
      (measurable_conditions A hlow)).mpr
    filter_upwards [P.originalMovingUpperLaw_support (cutoff N)] with v hv
    constructor <;> intro hp <;> exfalso <;>
      dsimp [bulkCondition,tailCondition,condition] at hp <;>
      linarith [hp.2,A.point.range.cutoff_gt_M,P.active_tail_gap]

def bulkSpecified : FiniteGame (N+1) 2 A.D.c NativeLocalPolicy.Seed :=
  ActiveFixedValueVersions.game P ξ (1+u) (by linarith)
    (A.forget.specified hlow) (P.vA-P.w) (P.vA+P.w) (lambda A hlow) (rate P ξ N)

def specified : FiniteGame (N+1) 2 A.D.c NativeLocalPolicy.Seed :=
  ActiveFixedValueVersions.game P ξ A.D.U A.D.hU
    (bulkSpecified A hlow) P.M (cutoff N) (lambda A hlow) (rate P ξ N)

lemma bulk_condition_before (hwγ : width≤ γ ξ) :
    ∀ᵐx ∂(A.forget.specified hlow).F⊗ₘ(A.forget.specified hlow).σ,bulkCondition A hlow x := by
  rw [A.forget.specified_joint hlow]
  exact (original_conditions A hlow hwγ).mono fun _ hx=> hx.1

lemma bulk_joint (hwγ : width≤ γ ξ) :
    (bulkSpecified A hlow).F⊗ₘ(bulkSpecified A hlow).σ=
      (A.native hlow).F⊗ₘ(A.native hlow).σ := by
  rw [bulkSpecified,ActiveFixedValueVersions.joint_eq _ _ _ _ _ _ _ _ _
    (bulk_condition_before A hlow hwγ),A.forget.specified_joint hlow]

lemma tail_condition_before (hwγ : width≤ γ ξ) :
    ∀ᵐx ∂(bulkSpecified A hlow).F⊗ₘ(bulkSpecified A hlow).σ,tailCondition A hlow x := by
  rw [bulk_joint A hlow hwγ]
  exact (original_conditions A hlow hwγ).mono fun _ hx=> hx.2

theorem specified_joint (hwγ : width≤ γ ξ) :
    (specified A hlow).F⊗ₘ(specified A hlow).σ=(A.native hlow).F⊗ₘ(A.native hlow).σ := by
  rw [specified,ActiveFixedValueVersions.joint_eq _ _ _ _ _ _ _ _ _
    (tail_condition_before A hlow hwγ),bulk_joint A hlow hwγ]

theorem specified_problem (hwγ : width≤ γ ξ) (i : Fin (N+1)) :
    problem (specified A hlow) i=problem (A.native hlow) i := by
  rw [specified,ActiveFixedValueVersions.problem_eq _ _ _ _ _ _ _ _ _
    (tail_condition_before A hlow hwγ),bulkSpecified,
    ActiveFixedValueVersions.problem_eq _ _ _ _ _ _ _ _ _
      (bulk_condition_before A hlow hwγ),A.forget.specified_problem hlow]

lemma specified_value : (specified A hlow).F=valueLaw P := rfl

lemma specified_bulk (v : ℝ) (hv : v∈P.bulkValues) :
    ∀ᵐa ∂(specified A hlow).σ v,a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) (1+u) ∧
      ∀b : Icc (1:ℝ) (1+u),
        SourceMenuIdentity.menuUtility P ξ (lambda A hlow).1 (lambda A hlow).2 v b≤
          SourceMenuIdentity.menuUtility P ξ (lambda A hlow).1 (lambda A hlow).2 v a.bid+
            2*error ξ (rate P ξ N) v := by
  have hvt : v∉Icc P.M (cutoff N) := fun h=> by linarith [h.1,hv.2,P.active_tail_gap]
  rw [show (specified A hlow).σ v=(bulkSpecified A hlow).σ v from
    outside P ξ A.D.U A.D.hU (bulkSpecified A hlow) _ _ _ _ v hvt]
  exact fixed_value_support P ξ (1+u) (by linarith) hξ
    (A.forget.specified hlow) _ _ _ _ (rate_nonnegative P hξ N) v hv

lemma specified_tail (v : ℝ) (hv : v∈Icc P.M (cutoff N)) :
    ∀ᵐa ∂(specified A hlow).σ v,a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) A.D.U ∧
      ∀b : Icc (1:ℝ) A.D.U,
        SourceMenuIdentity.menuUtility P ξ (lambda A hlow).1 (lambda A hlow).2 v b≤
          SourceMenuIdentity.menuUtility P ξ (lambda A hlow).1 (lambda A hlow).2 v a.bid+
            2*error ξ (rate P ξ N) v :=
  fixed_value_support P ξ A.D.U A.D.hU hξ
    (bulkSpecified A hlow) _ _ _ _ (rate_nonnegative P hξ N) v hv

theorem specified_lower_count (hwγ : width≤ γ ξ) (v : ℝ)
    (hv : v∈Icc (0:ℝ) P.d0∪P.partialValues) :
    conditionalTypeCountLaw (specified A hlow) (Nat.succ_pos N) v=
      conditionalTypeCountLaw (A.forget.specified hlow) (Nat.succ_pos N) v := by
  have hb : v∉P.bulkValues := by
    intro h
    rcases hv with hv|hv
    · linarith [hv.2,h.1,P.low_partial_gap,P.partial_active_gap,P.w_pos]
    · linarith [hv.2,h.1,P.partial_active_gap]
  have ht : v∉Icc P.M (cutoff N) := by
    intro h
    rcases hv with hv|hv
    · linarith [hv.2,h.1,P.low_partial_gap,P.partial_active_gap,P.active_tail_gap,P.w_pos]
    · linarith [hv.2,h.1,P.partial_active_gap,P.active_tail_gap,P.w_pos]
  rw [specified,conditional_eq_outside _ _ _ _ _ _ _ _ _
    (tail_condition_before A hlow hwγ) (Nat.succ_pos N) v ht,
    bulkSpecified,conditional_eq_outside _ _ _ _ _ _ _ _ _
      (bulk_condition_before A hlow hwγ) (Nat.succ_pos N) v hb]

end FCAppendix.Affine.Tail04.OrderedSourceActiveSpecified
