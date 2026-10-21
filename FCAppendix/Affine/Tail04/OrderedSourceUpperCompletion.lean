import FCAppendix.Affine.Tail04.OrderedSourceSpecifiedNative
import FCAppendix.Affine.Tail04.SourceUpperBudgets
import FCAppendix.Affine.Tail04.OrderedSourceNativeLowerFailure

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceUpperCompletion
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional Existence.RankEnvelope OriginalValues OriginalPopulation LowBody
open OrderedSourceFiniteStartingPoint SourceMovingScalarGuards OrderedSourceRestrictedNative
open SourceMomentRectangle SourceMenuPopulation OrderedSourceEndogenousFloor
open FiniteTailNoisyGame SourceTailNoisyFixedPoint

private lemma castMarketRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((n+1:ℝ)*p)≤q) : x+y*((((n+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {hlow : P.d0<1-ξ} {N : ℕ}
  (E : OrderedSourceEndogenousFloor.Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N)
local notation "A" => E.market
local notation "D" => OrderedSourceRestrictedNative.Market.D A
local notation "tN" => cutoff N
local notation "htN" => E.market.point.range.cutoff_gt_M
local notation "Γ" => OrderedSourceRestrictedNative.Market.native A hlow
local notation "qN" => SourceFloorRates.q P N
local notation "μH" => P.movingUpperMeasure tN
local notation "q" => OriginalMovingUpperEnvelope.q P tN (N+1) (FiniteTailNoisyGame.Data.c D)
local notation "R" => OrderedSourceRestrictedNative.Market.H A
local notation "bH" => OrderedSourceRestrictedNative.Market.upperBid A
local notation "V" => OrderedSourceEndogenousFloor.boundaryValue P ξ Up u k width
  hξ hξh hu hRUp hUp hw E.point hlow
local notation "a" => OrderedSourceEndogenousFloor.boundaryBid P ξ Up u k width
  hξ hξh hu hRUp hUp hw E.point hlow

include E in
lemma population_two : 2≤ N+1 := by have:=(A).point.range.rivals_positive;omega
lemma capacity_pos : 1≤ (D).c:=(A).point.range.capacity_positive
lemma capacity_lt : (D).c< N+1:=(A).point.range.capacity_less_population
lemma floor_gt_one : 1< R:=(D).hU.trans_lt E.ready.above_cap
lemma floor_pos : 0< R:=E.ready.positive
lemma floor_lt_cutoff : R< tN:=E.ready.below_cutoff

lemma actual_mean (i : Fin (N+1)) (y : ℝ) (hy : R≤ y) :
    meanAcceptProb Γ i y=bidRank μH ((N+1)-1) (D).c 2 (bid (rank μH ((N+1)-1) (D).c 2) tN R) y := by
  simpa only [Nat.add_sub_cancel,OrderedSourceEndogenousFloor.upperBid,
    OriginalMovingUpperEnvelope.b,OriginalMovingUpperEnvelope.q] using! OrderedSourceEndogenousFloor.final_mean
    P ξ Up u k width hξ hξh hu hRUp hUp hw E.point hlow E.ready i y hy

lemma actual_upper_integral : IntegrableOn (fun v=>1-rank μH ((N+1)-1) (D).c 2 v) (Ioi tN) :=
  (OriginalMovingUpperEnvelope.rank_integrals P tN (htN).le (N+1) (D).c
    (capacity_pos E) (capacity_lt E)).1

lemma actual_guard (bud : SourceUpperBudgets.Budget P ξ k N) :
    error (rank μH ((N+1)-1) (D).c 2) tN R<
      (D).eta*R*(1-2*(1-rank μH ((N+1)-1) (D).c 2 tN)) :=
  bud.hidden R (floor_gt_one E).le

def boundaryAction : JointAction 2 := bandAction (by norm_num) 2 le_rfl a

lemma boundaryAction_below : (boundaryAction E).bid< R:=(a).2.2.trans_lt E.ready.above_cap

lemma actual_boundary : (problem Γ 0).payoff tN (boundaryAction E)=V :=
  OrderedSourceEndogenousFloor.final_boundary_value P ξ Up u k width hξ hξh hu hRUp hUp hw
    E.point hlow E.ready 0

lemma actual_boundary_all (i : Fin (N+1)) :
    (problem Γ i).payoff tN (boundaryAction E)=(tN-R)*rank μH ((N+1)-1) (D).c 2 tN := by
  have hv : (problem Γ i).payoff tN (boundaryAction E)=V :=
    OrderedSourceEndogenousFloor.final_boundary_value P ξ Up u k width hξ hξh hu hRUp hUp hw
      E.point hlow E.ready i
  rw [hv]
  exact (SourceBoundaryCost.exact_match tN V qN
    (SourceFloorRates.q_pos P N (capacity_pos E)).ne').symm

variable (hk : 0< k) (huB : 1+u< Central.B ξ)
  (hUpMargin : Up≤ Central.R ξ+ξ/1000)
  (hsmall : SourceMomentRectangle.relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
  (hwγ : width≤ γ ξ)

include hk huB hUpMargin hsmall hwγ in
lemma active_failure (i : Fin (N+1)) (b : Icc (1:ℝ) (D).U) (r : Fin 3) :
    CanonicalFailure.movingCoefficient P ξ k/tN^2-
      SourceMovingMenuRates.rate (SourceCommonMenuError.commonCoefficient P ξ)
        (lowMass P.theta) P.bulkWeight N≤
      1-((problem Γ i).outcome (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) r)).success := by
  letI:=(A).common_compact_atomless
  exact OrderedSourceNativeLowerFailure.active_all_routes D P tN htN ((A).forget.low_gap hlow)
    R (A).upper_gap (A).point.low.joint (A).sequence.limit bH (A).upperBid_measurable
    (A).upper_floor N (castMarketRare (A).forget.rare) (NativeLowSourceIC.categories P tN (htN).le)
    (A).point.low rfl rfl (A).point.range.rivals_positive rfl
    (by intro reg;cases reg <;> rfl) rfl hξh rfl huB hUpMargin hsmall
    (A).point.range.upper_mass_guard hwγ k hk le_rfl i b r

include hk huB hUpMargin hsmall hwγ in
lemma boundary_slope (bud : SourceUpperBudgets.Budget P ξ k N) (i : Fin (N+1)) :
    ((problem Γ i).outcome (boundaryAction E)).success< rank μH ((N+1)-1) (D).c 2 tN := by
  have hf:=active_failure E hk huB hUpMargin hsmall hwγ i a 2
  change _≤1-((problem Γ i).outcome (boundaryAction E)).success at hf
  change ((problem Γ i).outcome (boundaryAction E)).success< qN
  linarith [bud.active]

include hk huB hUpMargin hsmall hwγ in
theorem lower_bestResponse (bud : SourceUpperBudgets.Budget P ξ k N)
    (i : Fin (N+1)) (v : ℝ) (hvt : v≤ tN) (act : JointAction 2)
    (hrestricted : ∀alt : JointAction 2,alt.bid< R→
      (problem Γ i).payoff v alt≤(problem Γ i).payoff v act) :
    (problem Γ i).BestResponse v act := by
  exact lower_bestResponse_after_upper_completion Γ (D).eta (D).heta0 (D).heta1 rfl rfl
    μH (population_two E) (capacity_pos E) (capacity_lt E)
    (OriginalMovingUpperEnvelope.measure_mass_le_one P tN) tN R (floor_pos E) (floor_lt_cutoff E)
    (P.movingUpperMeasure_support tN) ((actual_guard E) bud) (actual_mean E) i v hvt act
    (boundaryAction E) (boundaryAction_below E) ((actual_boundary_all E) i)
    (boundary_slope E hk huB hUpMargin hsmall hwγ bud i).le hrestricted

include hk huB hUpMargin hsmall hwγ in
theorem specified_lower_bestResponse (bud : SourceUpperBudgets.Budget P ξ k N)
    (i : Fin (N+1)) (v : ℝ) (hvt : v≤ tN) (act : JointAction 2)
    (hrestricted : ∀alt : JointAction 2,alt.bid< R→
      (problem E.specified i).payoff v alt≤(problem E.specified i).payoff v act) :
    (problem E.specified i).BestResponse v act := by
  rw [E.original_problem hwγ i] at hrestricted ⊢
  exact lower_bestResponse E hk huB hUpMargin hsmall hwγ bud i v hvt act hrestricted

theorem upper_bestResponse (bud : SourceUpperBudgets.Budget P ξ k N)
    (hboundary : ∀(i : Fin (N+1)) (act : JointAction 2),act.bid< R→
      (problem Γ i).payoff tN act≤ V)
    (hslopes : ∀(i : Fin (N+1)) (act : JointAction 2),act.bid< R→
      ((problem Γ i).outcome act).success≤
        1-(CanonicalFailure.movingCoefficient P ξ k/4)/tN^2)
    (i : Fin (N+1)) (v : ℝ) (hv : tN≤ v) :
    (problem Γ i).BestResponse v (Hybrid.upperAction bH v) := by
  apply native_original_upper_all_actions Γ (D).eta (D).heta0 (D).heta1 rfl rfl μH
    (population_two E) (capacity_pos E) (capacity_lt E)
    (OriginalMovingUpperEnvelope.measure_mass_le_one P tN) tN R
    (1-(CanonicalFailure.movingCoefficient P ξ k/4)/tN^2)
    (floor_pos E) (floor_lt_cutoff E) (P.movingUpperMeasure_support tN)
    (actual_upper_integral E) ((actual_guard E) bud) (actual_mean E) bud.lowerSlope
    ?_ hslopes i v hv
  intro j act ha
  have he:=(actual_boundary_all E) j
  have he':=(OrderedSourceEndogenousFloor.final_boundary_value P ξ Up u k width
    hξ hξh hu hRUp hUp hw E.point hlow E.ready j)
  have hb:=hboundary j act ha
  change (problem Γ j).payoff tN (boundaryAction E)=V at he'
  linarith

theorem upper_joint_bestResponse (bud : SourceUpperBudgets.Budget P ξ k N)
    (hboundary : ∀(i : Fin (N+1)) (act : JointAction 2),act.bid< R→
      (problem Γ i).payoff tN act≤ V)
    (hslopes : ∀(i : Fin (N+1)) (act : JointAction 2),act.bid< R→
      ((problem Γ i).outcome act).success≤
        1-(CanonicalFailure.movingCoefficient P ξ k/4)/tN^2) :
    ∀ᵐx ∂(Hybrid.upperJoint (OriginalMovingUpperEnvelope.law P tN) bH
      (A).upperBid_measurable : Measure (ℝ×JointAction 2)),
      ∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2 := by
  have hS : MeasurableSet {x : ℝ×JointAction 2 |
      ∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2} := by
    simpa only [Set.setOf_forall] using MeasurableSet.iInter (fun i=> measurableSet_bestResponse Γ i)
  apply (ae_map_iff (measurable_id.prodMk
    (measurable_upperAction bH (A).upperBid_measurable)).aemeasurable hS).mpr
  filter_upwards [OriginalMovingUpperEnvelope.law_support P tN] with v hv
  intro i
  exact upper_bestResponse E bud hboundary hslopes i v hv

theorem eventually_lower_bestResponse (P : ValueParameters) (ξ Up u k width : ℝ)
    (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
    (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)
    (hlow : P.d0<1-ξ) (hk : 0< k) (huB : 1+u< Central.B ξ)
    (hUpMargin : Up≤ Central.R ξ+ξ/1000)
    (hsmall : SourceMomentRectangle.relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
    (hwγ : width≤ γ ξ) :
    ∀ᶠN in atTop,∀E : OrderedSourceEndogenousFloor.Envelope P ξ Up u k width
      hξ hξh hu hRUp hUp hw hlow N,
      ∀(i : Fin (N+1)) (v : ℝ),v≤ cutoff N→∀act : JointAction 2,
        (∀alt : JointAction 2,alt.bid< E.market.H→
          (problem (E.market.native hlow) i).payoff v alt≤
            (problem (E.market.native hlow) i).payoff v act)→
        (problem (E.market.native hlow) i).BestResponse v act := by
  filter_upwards [SourceUpperBudgets.eventually_budget P hξ hξh hk] with N hN
  intro E i v hv act hrestricted
  exact lower_bestResponse E hk huB hUpMargin hsmall hwγ hN i v hv act hrestricted

theorem eventually_specified_lower_bestResponse (P : ValueParameters) (ξ Up u k width : ℝ)
    (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
    (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)
    (hlow : P.d0<1-ξ) (hk : 0< k) (huB : 1+u< Central.B ξ)
    (hUpMargin : Up≤ Central.R ξ+ξ/1000)
    (hsmall : SourceMomentRectangle.relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
    (hwγ : width≤ γ ξ) :
    ∀ᶠN in atTop,∀E : OrderedSourceEndogenousFloor.Envelope P ξ Up u k width
      hξ hξh hu hRUp hUp hw hlow N,
      ∀(i : Fin (N+1)) (v : ℝ),v≤ cutoff N→∀act : JointAction 2,
        (∀alt : JointAction 2,alt.bid< E.market.H→
          (problem E.specified i).payoff v alt≤(problem E.specified i).payoff v act)→
        (problem E.specified i).BestResponse v act := by
  filter_upwards [SourceUpperBudgets.eventually_budget P hξ hξh hk] with N hN
  intro E i v hv act hrestricted
  exact specified_lower_bestResponse E hk huB hUpMargin hsmall hwγ hN i v hv act hrestricted

end FCAppendix.Affine.Tail04.OrderedSourceUpperCompletion
