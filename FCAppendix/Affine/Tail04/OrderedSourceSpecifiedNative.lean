import FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor
import FCAppendix.Affine.Tail04.OrderedSourceActiveSpecified

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceSpecifiedNative
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceFiniteStartingPoint
open SourceMovingScalarGuards SourceMomentRectangle OrderedSourceRestrictedNative
open OrderedSourceActiveCountData

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {N : ℕ} (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)

lemma low_bid_atomless (y : ℝ) :
    (lowJoint P.originalLowLaw A.point.low.joint : Measure (ℝ×JointAction 2))
      {x | x.2.bid=y}=0 := by
  letI:=A.low_real_atomless
  have hb : Measurable (fun x : ℝ×JointAction 2=> x.2.bid):=
    (measurable_bid 2).comp measurable_snd
  have he:=congrArg (fun μ : Measure ℝ=> μ {y})
    (lowJoint_bid_marginal P.originalLowLaw A.point.low.joint)
  rw [Measure.map_apply hb (measurableSet_singleton y),measure_singleton] at he
  exact he

lemma band_bid_atomless (q : Fin 3) (y : ℝ) :
    (band A q : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0 := by
  letI:=A.species_real_atomless q
  let f := fun x : OrderedSourceFinitePayoffTests.Own A.D P (cutoff N) q=>
    ((x.1:ℝ),bandAction (bidLo_pos A.D q).le (if q=2 then 1 else 2)
      (by split_ifs <;> omega) x.2)
  have hf : Measurable f := measurable_fst.subtype_val.prodMk
    ((measurable_bandAction _ _ _).comp measurable_snd)
  have hb : Measurable (fun x : ℝ×JointAction 2=> x.2.bid):=
    (measurable_bid 2).comp measurable_snd
  change ((ProbabilityMeasure.toMeasure (Subtype.val (A.sequence.limit q))).map f) {x | x.2.bid=y}=0
  calc
    _=((ProbabilityMeasure.toMeasure (Subtype.val (A.sequence.limit q))).map (fun x=>(x.2:ℝ))) {y} := by
      rw [Measure.map_apply hf (measurableSet_eq_fun hb measurable_const),
        Measure.map_apply measurable_snd.subtype_val (measurableSet_singleton y)]
      rfl
    _=0 := measure_singleton y

variable (hlow : P.d0<1-ξ)
local notation "Γ" => A.native hlow
local notation "PH" => ProbabilityMeasure.toMeasure (upperJoint
  (OriginalMovingUpperEnvelope.law P (cutoff N)) A.upperBid A.upperBid_measurable)

theorem full_joint_bid_null (hH : ∀y,PH {x | x.2.bid=y}=0) (y : ℝ) :
    ((Γ).F⊗ₘ(Γ).σ) {x | x.2.bid=y}=0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  apply original_joint_ae A hlow (fun x=> x.2.bid≠y)
  · exact measure_eq_zero_iff_ae_notMem.mp (low_bid_atomless A y)
  · exact measure_eq_zero_iff_ae_notMem.mp (band_bid_atomless A 2 y)
  · exact measure_eq_zero_iff_ae_notMem.mp (band_bid_atomless A 0 y)
  · exact measure_eq_zero_iff_ae_notMem.mp (band_bid_atomless A 1 y)
  · exact measure_eq_zero_iff_ae_notMem.mp (hH y)

theorem full_bid_atomless (hH : ∀y,PH {x | x.2.bid=y}=0) :
    NullSingletonClass (((Γ).F⊗ₘ(Γ).σ).map (fun x=> x.2.bid)) := by
  constructor
  intro y
  have hb : Measurable (fun x : ℝ×JointAction 2=>x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  rw [Measure.map_apply hb (measurableSet_singleton y)]
  exact full_joint_bid_null A hlow hH y

theorem visible_atomless (hH : ∀y,PH {x | x.2.bid=y}=0) : VisibleAtomless Γ := by
  intro j y
  have hz : userLaw Γ {d : UserDraw 2 | d.1.2.bid=y}=0 := by
    have he : {d : UserDraw 2 | d.1.2.bid=y}=
        {x : ℝ×JointAction 2 | x.2.bid=y}×ˢuniv := by ext d;simp
    rw [he,userLaw,Measure.prod_prod,full_joint_bid_null A hlow hH y,zero_mul]
  exact measure_mono_null (fun _ hx=> hx.2) hz

local notation "Γs" => OrderedSourceActiveSpecified.specified A hlow
variable (hwγ : width≤ γ ξ)

include hwγ in
lemma specified_userLaw : userLaw Γs=userLaw Γ := by
  simp only [userLaw,OrderedSourceActiveSpecified.specified_joint A hlow hwγ]

include hwγ in
lemma specified_userProfileLaw : userProfileLaw Γs=userProfileLaw Γ := by
  simp only [userProfileLaw,specified_userLaw A hlow hwγ]

include hwγ in
lemma specified_observedListLaw (j : Fin 2) : observedListLaw Γs j=observedListLaw Γ j := by
  simp only [observedListLaw,specified_userProfileLaw A hlow hwγ]

def posterior : PosteriorSystem Γs where
  posterior:=(A.posterior hlow).posterior
  markov:=(A.posterior hlow).markov
  on_path j:=by
    rw [specified_userProfileLaw A hlow hwγ,specified_observedListLaw A hlow hwγ]
    exact (A.posterior hlow).on_path j
  feasible:=(A.posterior hlow).feasible

theorem proposer_optimal : PosteriorProposerOptimal Γs (posterior A hlow hwγ) :=
  A.proposer_optimal hlow

include hwγ in
theorem specified_full_bid_atomless (hH : ∀y,PH {x | x.2.bid=y}=0) :
    NullSingletonClass (((Γs).F⊗ₘ(Γs).σ).map (fun x=> x.2.bid)) := by
  rw [OrderedSourceActiveSpecified.specified_joint A hlow hwγ]
  exact full_bid_atomless A hlow hH

include hwγ in
theorem specified_visible_atomless (hH : ∀y,PH {x | x.2.bid=y}=0) : VisibleAtomless Γs := by
  intro j y
  rw [specified_userLaw A hlow hwγ]
  exact visible_atomless A hlow hH j y

theorem all_labels_of_components
    (hP : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 2)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hB : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 0)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hT : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 1)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hH : ∀ᵐx ∂PH,∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2) :
    ∀ᵐx ∂(Γ).F⊗ₘ(Γ).σ,∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2 :=
  original_joint_ae A hlow _ (A.low_all_labels hlow) hP hB hT hH

theorem users_of_components
    (hP : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 2)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hB : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 0)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hT : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 1)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hH : ∀ᵐx ∂PH,∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2) : UsersOptimal Γ := by
  intro i
  exact Measure.ae_ae_of_ae_compProd
    ((all_labels_of_components A hlow hP hB hT hH).mono (fun _ hx=> hx i))

include hwγ in
theorem specified_all_labels_of_components
    (hP : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 2)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hB : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 0)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hT : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 1)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hH : ∀ᵐx ∂PH,∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2) :
    ∀ᵐx ∂(Γs).F⊗ₘ(Γs).σ,∀i : Fin (N+1),(problem Γs i).BestResponse x.1 x.2 := by
  rw [OrderedSourceActiveSpecified.specified_joint A hlow hwγ]
  filter_upwards [all_labels_of_components A hlow hP hB hT hH] with x hx
  intro i
  rw [OrderedSourceActiveSpecified.specified_problem A hlow hwγ i]
  exact hx i

include hwγ in
theorem specified_equilibrium_of_components
    (hP : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 2)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hB : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 0)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hT : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 1)),∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2)
    (hH : ∀ᵐx ∂PH,∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2) :
    IsBayesianEquilibrium Γs := by
  refine ⟨?_,⟨posterior A hlow hwγ,proposer_optimal A hlow hwγ⟩⟩
  intro i
  exact Measure.ae_ae_of_ae_compProd
    ((specified_all_labels_of_components A hlow hwγ hP hB hT hH).mono (fun _ hx=> hx i))

end FCAppendix.Affine.Tail04.OrderedSourceSpecifiedNative

namespace FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor.Envelope
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open OriginalValues OriginalPopulation SourceMomentRectangle OrderedSourceRestrictedNative
open SourceMovingScalarGuards

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {hlow : P.d0<1-ξ} {N : ℕ}
  (E : Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N)

abbrev specified := OrderedSourceActiveSpecified.specified E.market hlow

lemma original_value : E.specified.F=valueLaw P := rfl

lemma original_joint (hwγ : width≤ γ ξ) :
    E.specified.F⊗ₘE.specified.σ=(E.market.native hlow).F⊗ₘ(E.market.native hlow).σ :=
  OrderedSourceActiveSpecified.specified_joint E.market hlow hwγ

lemma original_problem (hwγ : width≤ γ ξ) (i : Fin (N+1)) :
    problem E.specified i=problem (E.market.native hlow) i :=
  OrderedSourceActiveSpecified.specified_problem E.market hlow hwγ i

lemma upper_atoms (y : ℝ) :
    (upperJoint ⟨P.originalMovingUpperLaw (cutoff N),
      P.originalMovingUpperLaw_probability (cutoff N)⟩ E.market.upperBid
      E.market.upperBid_measurable : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0 :=
  final_upper_atomless P ξ Up u k width hξ hξh hu hRUp hUp hw E.point hlow E.ready y

theorem bid_atomless (hwγ : width≤ γ ξ) :
    NullSingletonClass ((E.specified.F⊗ₘE.specified.σ).map (fun x=> x.2.bid)) :=
  OrderedSourceSpecifiedNative.specified_full_bid_atomless E.market hlow hwγ E.upper_atoms

theorem visible_atomless (hwγ : width≤ γ ξ) : VisibleAtomless E.specified :=
  OrderedSourceSpecifiedNative.specified_visible_atomless E.market hlow hwγ E.upper_atoms

def posterior (hwγ : width≤ γ ξ) : PosteriorSystem E.specified :=
  OrderedSourceSpecifiedNative.posterior E.market hlow hwγ

theorem proposer_optimal (hwγ : width≤ γ ξ) :
    PosteriorProposerOptimal E.specified (E.posterior hwγ) :=
  OrderedSourceSpecifiedNative.proposer_optimal E.market hlow hwγ

theorem payoff_preserved (hwγ : width≤ γ ξ) (i : Fin (N+1)) (v : ℝ) (a : JointAction 2) :
    (problem E.specified i).payoff v a=(problem (E.market.native hlow) i).payoff v a := by
  rw [E.original_problem hwγ i]

end FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor.Envelope
