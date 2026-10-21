import FCAppendix.Affine.Tail04.OrderedSourceRestrictedNative
import FCAppendix.Affine.Tail04.SourceFloorRates
import FCAppendix.Affine.Tail04.OrderedSourceUpperNative
import FCAppendix.Affine.Tail04.OrderedZeroSourceCommonPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedOriginalNoisySequence
open OrderedSourceFiniteStartingPoint SourceMovingScalarGuards OrderedSourceRestrictedNative
open SourceMomentRectangle SourceMenuPopulation SourceMultiplierRectangle
open SourceBulkAnalyticAdapter SourceTailTaylor SourceTailCapGap SourceBoundaryCost
open MenuError SourceMenuIdentity CompactSourceBidLaws

private lemma castMarketRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((n+1:ℝ)*p)≤q) : x+y*((((n+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)

section Point
variable {N : ℕ} (Z : AtomlessPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N)
local notation "D" => OrderedSourceFiniteStartingPoint.data P ξ Up u k width
  hξ hξh hu hRUp hUp hw N Z.point.range
local notation "tN" => cutoff N
local notation "htN" => Z.point.range.cutoff_gt_M

lemma provisional_gap : (D).U< Central.B ξ+1 :=
  Z.point.range.base_below_nominal.trans (lt_add_of_pos_right _ (by norm_num))

def provisional : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N :=
  complete P ξ Up u k width hξ hξh hu hRUp hUp hw Z (Central.B ξ+1)
    (provisional_gap P ξ Up u k width hξ hξh hu hRUp hUp hw Z)
    (fun _=> Central.B ξ+1) measurable_const (fun _ _=> le_rfl)

variable (hlow : P.d0<1-ξ)
local notation "A0" => provisional P ξ Up u k width hξ hξh hu hRUp hUp hw Z

def boundaryBid : Icc (1:ℝ) (D).U :=
  Classical.choose ((A0).active_maximizer hlow 0 tN)

def boundaryValue : ℝ :=
  (problem ((A0).native hlow) 0).payoff tN
    (bandAction (by norm_num) 2 le_rfl
      (boundaryBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow))

local notation "a" => boundaryBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
local notation "V" => boundaryValue P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow

lemma boundary_max (b : Icc (1:ℝ) (D).U) :
    (problem ((A0).native hlow) 0).payoff tN (bandAction (by norm_num) 2 le_rfl b)≤ V :=
  Classical.choose_spec ((A0).active_maximizer hlow 0 tN) b

lemma boundary_value_all (i : Fin (N+1)) :
    (problem ((A0).native hlow) i).payoff tN (bandAction (by norm_num) 2 le_rfl a)=V := by
  unfold boundaryValue
  rw [(A0).active_payoff hlow i,(A0).active_payoff hlow 0]

lemma boundary_max_all (i : Fin (N+1)) (b : Icc (1:ℝ) (D).U) :
    (problem ((A0).native hlow) i).payoff tN (bandAction (by norm_num) 2 le_rfl b)≤ V := by
  rw [(A0).active_payoff hlow i,←(A0).active_payoff hlow 0]
  exact boundary_max P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow b

def multiplier (reg : Bool) : ℝ :=
  ZeroSourceCommonMenuError.lambda D P tN htN Z.point.low.joint Z.point.sequence.limit
    (A0).upperBid (A0).upperBid_measurable ((A0).forget.low_gap hlow) (A0).H (A0).upper_gap
    (A0).upper_floor N (castMarketRare (A0).forget.rare) reg

local notation "lam" => multiplier P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow

lemma multiplier_mem {ρ : ℝ} {Λ : Set (ℝ×ℝ)}
    (huB : 1+u< Central.B ξ) (hrect : MomentInvariant P ξ ρ Λ)
    (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ) : (lam false,lam true)∈Λ := by
  exact ZeroSourceMultiplierRectangle.actual_mem D P tN htN Z.point.low.joint
    Z.point.sequence.limit (A0).upperBid (A0).upperBid_measurable ((A0).forget.low_gap hlow)
    (A0).H (A0).upper_gap (A0).upper_floor N (castMarketRare (A0).forget.rare) rfl
    (by intro reg;cases reg <;> rfl) huB hrect hρ

lemma multiplier_bounds (huB : 1+u< Central.B ξ)
    (hUpMargin : Up≤ Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000) (reg : Bool) :
    (1-ξ)*Central.B ξ≤ lam reg ∧ lam reg≤1 := by
  exact ZeroSourceMultiplierRectangle.actual_nominal_bounds D P tN htN Z.point.low.joint
    Z.point.sequence.limit (A0).upperBid (A0).upperBid_measurable ((A0).forget.low_gap hlow)
    (A0).H (A0).upper_gap (A0).upper_floor N (castMarketRare (A0).forget.rare) rfl
    (by intro reg;cases reg <;> rfl) huB hξh rfl hUpMargin hsmall
    Z.point.range.upper_mass_guard reg

theorem actual_error (huB : 1+u< Central.B ξ)
    (hUpMargin : Up≤ Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
    (hwγ : width≤ γ ξ) (i : Fin (N+1)) (b : Icc (1:ℝ) (D).U) :
    |(problem ((A0).native hlow) i).payoff tN (bandAction (by norm_num) 2 le_rfl b)-
      menuUtility P ξ (lam false) (lam true) tN b|≤ SourceFloorRates.error P ξ N := by
  letI : NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal
      (Subtype.val (OrderedNativeZeroNoiseSource.active D P tN htN Z.point.sequence.limit)))) :=
    (A0).common_compact_atomless
  exact OrderedZeroSourceCommonPayoff.actual_error D P tN htN ((A0).forget.low_gap hlow)
    (A0).H (A0).upper_gap Z.point.low.joint Z.point.sequence.limit (A0).upperBid
    (A0).upperBid_measurable (A0).upper_floor N (castMarketRare (A0).forget.rare)
    (NativeLowSourceIC.categories P tN (htN).le) Z.point.low rfl rfl
    Z.point.range.rivals_positive rfl (by intro reg;cases reg <;> rfl) rfl hξh rfl
    huB hUpMargin hsmall Z.point.range.upper_mass_guard hwγ rfl i tN
    (P.M_pos.trans htN).le b

theorem cost_bounds {ρ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hk0 : 0< k) (hmin : 0< Amin) (hk : k<1/(2*Amax))
    (huB : 1+u< Central.B ξ) (hUpMargin : Up≤ Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000) (hwγ : width≤ γ ξ)
    (hrect : MomentInvariant P ξ ρ Λ)
    (hleading : ∀l∈Λ,Amin≤ leadingA P ξ l.1 l.2 ∧ leadingA P ξ l.1 l.2≤ Amax)
    (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ)
    (bud : SourceFloorRates.Budgets P ξ Amin Amax k N) :
    Central.B ξ-1/(4*Amin*(tN-Central.B ξ))-SourceFloorRates.error P ξ N≤ tN-V ∧
      tN-V≤ Central.B ξ-1/(4*Amax*tN)+
        taylorConstant ξ (endpointRadius Amin)/tN^2+SourceFloorRates.error P ξ N := by
  have hA:=hleading _ (multiplier_mem P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
    huB hrect hρ)
  have hA0:=multiplier_bounds P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
    huB hUpMargin hsmall false
  have hA1:=multiplier_bounds P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
    huB hUpMargin hsmall true
  exact finite_max_cost_bounds P hξ hξh.le bud.above_endpoint hmin hA.1 hA.2 hk0 hk
    rfl bud.comparison_room hA0.1 hA0.2 hA1.1 hA1.2
    (fun b=> (problem ((A0).native hlow) 0).payoff tN (bandAction (by norm_num) 2 le_rfl b))
    a (boundary_max P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) rfl
    (actual_error P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
      huB hUpMargin hsmall hwγ 0)

def floor : ℝ := matchedFloor tN V (SourceFloorRates.q P N)

local notation "R" => floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow

structure Ready : Prop where
  above_cap : (D).U< R
  below_nominal : R< Central.B ξ
  endpoint_below_cutoff : Central.B ξ< tN

lemma Ready.positive (h : Ready P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) : 0< R :=
  ((by norm_num : (0:ℝ)<1).trans_le (D).hU).trans h.above_cap

lemma Ready.below_cutoff (h : Ready P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) : R< tN :=
  h.below_nominal.trans h.endpoint_below_cutoff

theorem ready {ρ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hk0 : 0< k) (hmin : 0< Amin) (hmax : 0< Amax) (hk : k<1/(2*Amax))
    (huB : 1+u< Central.B ξ) (hUpMargin : Up≤ Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000) (hwγ : width≤ γ ξ)
    (hrect : MomentInvariant P ξ ρ Λ)
    (hleading : ∀l∈Λ,Amin≤ leadingA P ξ l.1 l.2 ∧ leadingA P ξ l.1 l.2≤ Amax)
    (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ)
    (bud : SourceFloorRates.Budgets P ξ Amin Amax k N) :
    Ready P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow := by
  have hcost:=cost_bounds P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
    hk0 hmin hk huB hUpMargin hsmall hwγ hrect hleading hρ bud
  have ht : 0< tN:=P.M_pos.trans htN
  have hq : 0< SourceFloorRates.q P N :=
    SourceFloorRates.q_pos P N Z.point.range.capacity_positive
  have hq1 := (SourceFloorRates.q_bounds P N).2
  have hinv : 0≤1/SourceFloorRates.q P N-1 := by
    have hh : (1:ℝ)≤1/SourceFloorRates.q P N :=
      (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hq1)
    linarith
  have hterm:=mul_nonneg ht.le hinv
  have hbase : 1≤ Central.B ξ-k/tN:=(D).hU
  have hVt : V≤ tN := by linarith [hcost.1,bud.lower]
  have hV0 : 0≤ V := by linarith [hcost.2,bud.upper,bud.above_endpoint]
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  have hr:=floor_localization hB bud.above_endpoint hmin hmax hq hq1 hV0 hVt
    hcost bud.lower bud.upper
  exact ⟨hr.1,hr.2,bud.above_endpoint⟩

def upperBid : ℝ→ℝ := OriginalMovingUpperEnvelope.b P tN (N+1) (D).c R

variable (hr : Ready P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)

include hr in
lemma upper_measurable : Measurable
    (upperBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) :=
  OriginalMovingUpperEnvelope.continuous_bid P tN (htN).le (N+1) (D).c
    (by have:=Z.point.range.rivals_positive;omega) Z.point.range.capacity_positive
    Z.point.range.capacity_less_population R hr.positive hr.below_cutoff |>.measurable

include hr in
lemma upper_floor (v : ℝ) (hv : tN< v) : R≤ upperBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow v :=
  (OriginalMovingUpperEnvelope.bid_bounds P tN (htN).le (N+1) (D).c
    (by have:=Z.point.range.rivals_positive;omega) Z.point.range.capacity_positive
    Z.point.range.capacity_less_population R hr.positive hr.below_cutoff v hv.le).1

def finalMarket : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N :=
  complete P ξ Up u k width hξ hξh hu hRUp hUp hw Z R hr.above_cap
    (upperBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)
    (upper_measurable P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr)
    (upper_floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr)

local notation "Af" => finalMarket P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr
local notation "Γf" => OrderedSourceRestrictedNative.Market.native Af hlow

@[simp] lemma final_same_point : (Af).point=Z.point := rfl
@[simp] lemma final_floor : (Af).H=R := rfl

theorem final_active_payoff (i j : Fin (N+1)) (v : ℝ) (b : Icc (1:ℝ) (D).U) :
    (problem Γf i).payoff v (bandAction (by norm_num) 2 le_rfl b)=
      (problem ((A0).native hlow) j).payoff v (bandAction (by norm_num) 2 le_rfl b) := by
  rw [(Af).active_payoff hlow i,(A0).active_payoff hlow j]
  rfl

theorem final_boundary_value (i : Fin (N+1)) :
    (problem Γf i).payoff tN (bandAction (by norm_num) 2 le_rfl a)=V := by
  rw [final_active_payoff P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr i 0]
  rfl

theorem final_boundary_max (i : Fin (N+1)) (b : Icc (1:ℝ) (D).U) :
    (problem Γf i).payoff tN (bandAction (by norm_num) 2 le_rfl b)≤ V := by
  rw [final_active_payoff P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr i 0]
  exact boundary_max P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow b

lemma final_game_eq : Γf=OrderedSourceUpperNative.game D P tN htN ((Af).forget.low_gap hlow)
    R hr.above_cap hr.below_cutoff Z.point.low.joint Z.point.sequence.limit N
    (by have:=Z.point.range.rivals_positive;omega) Z.point.range.capacity_positive
    Z.point.range.capacity_less_population (castMarketRare (Af).forget.rare) := rfl

theorem final_rank (i : Fin (N+1)) (j : Fin 2) (y : ℝ) (hy : R≤ y) :
    ∀ᵐω ∂backgroundLaw Γf,Accepts Γf i y j ω↔rivals i (aboveAt j y) ω< (D).c := by
  rw [final_game_eq P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr]
  exact OrderedSourceUpperNative.actual_rank D P tN htN ((Af).forget.low_gap hlow) R hr.above_cap
    hr.below_cutoff Z.point.low.joint Z.point.sequence.limit N
    (by have:=Z.point.range.rivals_positive;omega) Z.point.range.capacity_positive
    Z.point.range.capacity_less_population (castMarketRare (Af).forget.rare) i j y hy

theorem final_mean (i : Fin (N+1)) (y : ℝ) (hy : R≤ y) :
    meanAcceptProb Γf i y=Existence.RankEnvelope.bidRank (P.movingUpperMeasure tN) N (D).c 2
      (upperBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) y := by
  rw [final_game_eq P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr]
  exact OrderedSourceUpperNative.actual_mean D P tN htN ((Af).forget.low_gap hlow) R hr.above_cap
    hr.below_cutoff Z.point.low.joint Z.point.sequence.limit N
    (by have:=Z.point.range.rivals_positive;omega) Z.point.range.capacity_positive
    Z.point.range.capacity_less_population (castMarketRare (Af).forget.rare) i y hy

theorem final_upper_attainment (i : Fin (N+1)) (v : ℝ) (hv : tN≤ v) :
    (problem Γf i).payoff v
      (Hybrid.upperAction (upperBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) v)=
        OriginalMovingUpperEnvelope.U P tN (N+1) (D).c R v := by
  rw [final_game_eq P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr]
  exact OrderedSourceUpperNative.actual_attainment D P tN htN ((Af).forget.low_gap hlow) R hr.above_cap
    hr.below_cutoff Z.point.low.joint Z.point.sequence.limit N
    (by have:=Z.point.range.rivals_positive;omega) Z.point.range.capacity_positive
    Z.point.range.capacity_less_population (castMarketRare (Af).forget.rare) i v hv

theorem boundary_match (i : Fin (N+1)) :
    (problem Γf i).payoff tN
      (Hybrid.upperAction (upperBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) tN)=
      (problem Γf i).payoff tN (bandAction (by norm_num) 2 le_rfl a) := by
  rw [final_upper_attainment P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr i tN le_rfl,
    final_boundary_value P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr i]
  change Existence.RankEnvelope.utility _ tN R tN=V
  rw [Existence.RankEnvelope.utility_at_floor]
  exact exact_match tN V (SourceFloorRates.q P N)
    (SourceFloorRates.q_pos P N Z.point.range.capacity_positive).ne'

theorem final_upper_atomless (y : ℝ) :
    (ProbabilityMeasure.toMeasure (Hybrid.upperJoint (OriginalMovingUpperEnvelope.law P tN)
      (upperBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)
      (upper_measurable P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr)))
        {x | x.2.bid=y}=0 :=
  OriginalMovingUpperEnvelope.joint_atomless P tN (htN).le (N+1) (D).c
    (by have:=Z.point.range.rivals_positive;omega) Z.point.range.capacity_positive
    Z.point.range.capacity_less_population R hr.positive hr.below_cutoff y

end Point

variable (hlow : P.d0<1-ξ)

structure Envelope (N : ℕ) where
  point : AtomlessPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N
  ready : Ready P ξ Up u k width hξ hξh hu hRUp hUp hw point hlow

namespace Envelope
variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {hlow : P.d0<1-ξ} {N : ℕ}
  (E : Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N)

abbrev market : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N :=
  finalMarket P ξ Up u k width hξ hξh hu hRUp hUp hw E.point hlow E.ready

end Envelope

theorem eventually_construct {ρ κ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hu0 : 0< u) (hκ : 0< κ) (hmin : 0< Amin)
    (hklo : 1/(4*Amin)< k) (hkhi : k<1/(2*Amax))
    (hwγ : width≤ γ ξ) (hvalue : Up<2-P.w) (huB : 1+u< Central.B ξ)
    (hUpMargin : Up< Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)< ξ/1000)
    (hgap : 2*Ample.binaryKL (99/200) (1-partialMass/2)<
      jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200))
    (hrect : MomentInvariant P ξ ρ Λ) (hder : BulkDerivativeBound P ξ κ Λ)
    (hleading : ∀l∈Λ,Amin≤ leadingA P ξ l.1 l.2 ∧ leadingA P ξ l.1 l.2≤ Amax)
    (hρ : relativeError P.zeta u (Central.B ξ)< ρ) :
    ∀ᶠ N in atTop,Nonempty
      (Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow (N+1)) := by
  have hk0 : 0< k := (by positivity : 0<1/(4*Amin)).trans hklo
  have hmax : 0< Amax := by
    have hd := one_div_pos.mp (hk0.trans hkhi)
    linarith
  have hp:=OrderedSourceRestrictedNative.eventually_points P ξ Up u k width hξ hξh hu hRUp hUp hw
    hu0 hk0 hκ hmin hkhi hlow hwγ hvalue huB hUpMargin hsmall hgap hrect hder hleading hρ
  have hb:=(tendsto_add_atTop_nat 1).eventually
    (SourceFloorRates.eventually_budgets P hξ hmin hmax hklo)
  filter_upwards [hp,hb] with N hP hB
  obtain ⟨Z⟩:=hP
  exact ⟨⟨Z,ready P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hk0 hmin hmax hkhi
    huB hUpMargin.le hsmall.le hwγ hrect hleading hρ.le hB⟩⟩

theorem exists_family {ρ κ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hu0 : 0< u) (hκ : 0< κ) (hmin : 0< Amin)
    (hklo : 1/(4*Amin)< k) (hkhi : k<1/(2*Amax))
    (hwγ : width≤ γ ξ) (hvalue : Up<2-P.w) (huB : 1+u< Central.B ξ)
    (hUpMargin : Up< Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)< ξ/1000)
    (hgap : 2*Ample.binaryKL (99/200) (1-partialMass/2)<
      jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200))
    (hrect : MomentInvariant P ξ ρ Λ) (hder : BulkDerivativeBound P ξ κ Λ)
    (hleading : ∀l∈Λ,Amin≤ leadingA P ξ l.1 l.2 ∧ leadingA P ξ l.1 l.2≤ Amax)
    (hρ : relativeError P.zeta u (Central.B ξ)< ρ) :
    ∃K : ℕ,∃_E : ∀j,Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow (K+j+1),
      Tendsto (fun j=> K+j+1) atTop atTop := by
  obtain ⟨K,hK⟩:=eventually_atTop.mp
    (eventually_construct P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hu0 hκ hmin
      hklo hkhi hwγ hvalue huB hUpMargin hsmall hgap hrect hder hleading hρ)
  refine ⟨K,fun j=> Classical.choice (hK (K+j) (Nat.le_add_right K j)),?_⟩
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using tendsto_add_atTop_nat (K+1)

end FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor
