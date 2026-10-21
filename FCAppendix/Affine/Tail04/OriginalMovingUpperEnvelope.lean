import FCAppendix.Affine.Tail04.SourceValuePartition
import FCAppendix.Affine.Tail04.OriginalRankTail

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalMovingUpperEnvelope
open MeasureTheory ProbabilityTheory Set Game Bayes
open Existence.RankEnvelope OriginalValues

variable (P : ValueParameters) (t : ℝ) (ht : P.M≤ t)

def mass : ℝ := activeMass P.theta*P.zeta*powerTail P.M 10 t

include ht in
lemma mass_pos : 0< mass P t := by
  unfold mass powerTail
  exact mul_pos (mul_pos P.active_mass_pos P.zeta_pos)
    (Real.rpow_pos_of_pos (div_pos (P.M_pos.trans_le ht) P.M_pos) _)

lemma measure_mass_le_one : (P.movingUpperMeasure t).real univ≤1 := by
  change (((valueLaw P).restrict (Ioi t)) univ).toReal≤1
  rw [Measure.restrict_apply_univ]
  exact measureReal_le_one

include t ht in
lemma mass_le_one : mass P t≤1 := by
  unfold mass
  rw [←P.movingUpperMeasure_mass t ht]
  exact measure_mass_le_one P t

def law : ProbabilityMeasure ℝ :=
  ⟨P.originalMovingUpperLaw t,P.originalMovingUpperLaw_probability t⟩

instance law_atomless : NullSingletonClass (law P t : Measure ℝ) :=
  P.originalMovingUpperLaw_atomless t

lemma law_support : ∀ᵐ v ∂(law P t : Measure ℝ),t≤ v :=
  (P.originalMovingUpperLaw_support t).mono (fun _ hv=> hv.le)

include ht in
lemma weighted_law : ENNReal.ofReal (mass P t) • (law P t : Measure ℝ)=
    P.movingUpperMeasure t := P.weighted_originalMovingUpperLaw t ht

def q (m c : ℕ) : ℝ→ℝ := rank (P.movingUpperMeasure t) (m-1) c 2
def b (m c : ℕ) (H : ℝ) : ℝ→ℝ := bid (q P t m c) t H
def U (m c : ℕ) (H : ℝ) : ℝ→ℝ := utility (q P t m c) t H
def E (m c : ℕ) (H : ℝ) : ℝ := error (q P t m c) t H

variable (m c : ℕ) (hm : 2≤ m) (hc : 1≤ c) (hcm : c< m)

include hc in
lemma rank_pos (v : ℝ) : 0< q P t m c v :=
  Existence.RankEnvelope.rank_pos (P.movingUpperMeasure t) (m-1) c hc
    (by norm_num) (measure_mass_le_one P t) v

lemma rank_le_one (v : ℝ) : q P t m c v≤1 :=
  (rank_bounds (P.movingUpperMeasure t) (m-1) c (by norm_num)
    (measure_mass_le_one P t) v).2

include hm hc hcm in
lemma rank_monotone : Monotone (q P t m c) := by
  have he : m-2+1=m-1 := by omega
  simpa only [q,he] using
    (Existence.RankEnvelope.rank_monotone (P.movingUpperMeasure t) (r:=m-2)
      hc (by omega) (by norm_num) (measure_mass_le_one P t))

include ht hc hcm in
theorem rank_integrals :
    IntegrableOn (fun v=>1-q P t m c v) (Ioi t) ∧
    IntegrableOn (fun v=> v*(1-q P t m c v)) (Ioi t) ∧
    (∫ v in Ioi t,1-q P t m c v)≤ rankTailConstant (m-1) c (mass P t)*t/(10*(c:ℝ)-1) ∧
    (∫ v in Ioi t,v*(1-q P t m c v))≤
      rankTailConstant (m-1) c (mass P t)*t^2/(10*(c:ℝ)-2) :=
  original_pareto_rank_integrals (P.movingUpperMeasure t) (m-1) c (mass P t) t hc
    (by omega) ⟨(mass_pos P t ht).le,mass_le_one P t ht⟩ (P.M_pos.trans_le ht)
    (P.movingUpperMeasure_relative t ht)

variable (H : ℝ) (hH : 0< H) (hHt : H< t)

include ht hm hc hcm hH hHt in
theorem envelope : UpperEnvelopeProperties (P.movingUpperMeasure t) (m-2) c
    (q P t m c) (b P t m c H) (U P t m c H) t H (E P t m c H) :=
  original_pareto_upper_envelope (P.movingUpperMeasure t) m c hm hc hcm
    (measure_mass_le_one P t) (mass P t) t H
    ⟨(mass_pos P t ht).le,mass_le_one P t ht⟩ (P.M_pos.trans_le ht) hH hHt
    (P.movingUpperMeasure_support t) (P.movingUpperMeasure_relative t ht)

include ht hm hc hcm hH hHt in
lemma continuous_bid : Continuous (b P t m c H) :=
  (envelope P t ht m c hm hc hcm H hH hHt).continuous_bid

include ht hm hc hcm hH hHt in
lemma bid_bounds (v : ℝ) (hv : t≤ v) : H≤ b P t m c H v ∧ b P t m c H v≤ v :=
  (envelope P t ht m c hm hc hcm H hH hHt).bid_bounds v hv

include ht hm hc hcm hH hHt in
lemma bid_floor : b P t m c H t=H :=
  (envelope P t ht m c hm hc hcm H hH hHt).floor

include ht hm hc hcm hH hHt in
lemma bid_law_atomless : NullSingletonClass ((law P t : Measure ℝ).map (b P t m c H)) := by
  letI := (envelope P t ht m c hm hc hcm H hH hHt).atomless
  constructor
  intro y
  have he : ((P.movingUpperMeasure t).map (b P t m c H)) {y}=0 := measure_singleton y
  rw [←weighted_law P t ht,Measure.map_smul,Measure.smul_apply,smul_eq_mul] at he
  exact (mul_eq_zero.mp he).resolve_left
    (ENNReal.ofReal_ne_zero_iff.mpr (mass_pos P t ht))

def joint : ProbabilityMeasure (ℝ×JointAction 2) :=
  Hybrid.upperJoint (law P t) (b P t m c H)
    (continuous_bid P t ht m c hm hc hcm H hH hHt).measurable

lemma joint_value : (joint P t ht m c hm hc hcm H hH hHt : Measure (ℝ×JointAction 2)).map Prod.fst=
    (law P t : Measure ℝ) := Hybrid.upperJoint_value_marginal _ _ _

lemma joint_bid : (joint P t ht m c hm hc hcm H hH hHt : Measure (ℝ×JointAction 2)).map
    (fun x=> x.2.bid)=(law P t : Measure ℝ).map (b P t m c H) := by
  apply Hybrid.upperJoint_bid_marginal
  filter_upwards [law_support P t] with v hv
  exact hH.le.trans (bid_bounds P t ht m c hm hc hcm H hH hHt v hv).1

lemma joint_support : ∀ᵐ x ∂(joint P t ht m c hm hc hcm H hH hHt : Measure (ℝ×JointAction 2)),
    H≤ x.2.bid ∧ x.2.routeCount=1 := by
  apply Hybrid.upperJoint_support
  filter_upwards [law_support P t] with v hv
  exact (bid_bounds P t ht m c hm hc hcm H hH hHt v hv).1

lemma joint_atomless (y : ℝ) :
    (joint P t ht m c hm hc hcm H hH hHt : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0 := by
  letI := bid_law_atomless P t ht m c hm hc hcm H hH hHt
  apply Hybrid.upperJoint_atomless
  filter_upwards [law_support P t] with v hv
  exact hH.le.trans (bid_bounds P t ht m c hm hc hcm H hH hHt v hv).1

include ht hc hcm hH hHt in
theorem finite_error : 0≤ E P t m c H ∧
    E P t m c H≤2*t*rankTailConstant (m-1) c (mass P t) :=
  original_pareto_error_bound (P.movingUpperMeasure t) (m-1) c (mass P t) t H
    hc (by omega) ⟨(mass_pos P t ht).le,mass_le_one P t ht⟩
    (P.M_pos.trans_le ht) hH.le hHt.le (P.movingUpperMeasure_relative t ht)

end FCAppendix.Affine.Tail04.OriginalMovingUpperEnvelope
