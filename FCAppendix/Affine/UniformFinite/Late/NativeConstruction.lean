import FCAppendix.Affine.UniformFinite.Early.To06
import FCAppendix.Affine.UniformFinite.Late.Construction
import FCAppendix.Affine.UniformFinite.Late.NativeRemoveFloor
import FCAppendix.Affine.UniformFinite.Late.NativeDeviation
import FCAppendix.Affine.UniformFinite.Late.NativeNamedRoutes
import FCAppendix.Affine.UniformFinite.Late.NativeConditionalTraces

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open Uniform05

namespace FiniteLowerConstruction
variable {i : Row} {M : ℕ} {R : ℝ}

def nativeGame (F : FiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    FiniteGame M 2 (Uniform07.capacity M) unitInterval :=
  letI : NeZero M := F.restricted.marketNeZero
  Late.StrictOriginal.game F.restricted H

def nativeBelief (F : FiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) : PosteriorSystem (F.nativeGame H) :=
  letI : NeZero M := F.restricted.marketNeZero
  Late.StrictOriginal.belief F.restricted H

theorem native_proposer_optimal (F : FiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal (Uniform07.capacity M)
        (beliefReceipts (F.nativeGame H).A
          (posteriorCountBelief (F.nativeGame H) (F.nativeBelief H) j L) L)
        ((F.nativeGame H).policy j L s).val := by
  letI : NeZero M := F.restricted.marketNeZero
  exact Late.StrictOriginal.game_proposer_optimal F.restricted H F.upper_floor

theorem native_lower_kernel (F : FiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (v : Value i) :
    (F.nativeGame H).σ v=(F.restricted.sigma v).map
      (fun q=> OriginalPopulation.lowerAction i (v,q)) := by
  letI : NeZero M := F.restricted.marketNeZero
  exact Late.StrictOriginal.game_lower_kernel F.restricted H v

variable {N : ℕ}

theorem native_positive_broadcast_payoff (F : FiniteLowerConstruction i (N+1) R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin (N+1)) (v : ℝ)
    (act : JointAction 2) (hr : act.routeCount=2) (hU : act.bid≤ cap i)
    (hb : 0< act.bid) :
    (problem (F.nativeGame H) a).payoff v act=
      rawUtility i N F.restricted.law v act.bid := by
  let own : Bid i:=⟨act.bid,act.bid_nonneg,hU⟩
  rw [NativeIC.broadcast_eq act hr own rfl]
  change (problem (Late.StrictOriginal.game F.restricted H) a).payoff v
    (Hybrid.lowBroadcast own)=_
  rw [Late.StrictOriginal.broadcast_payoff_capped F.restricted H F.upper_floor a v own,
    NativeIndexed.utility_positive_eq_raw i N F.restricted.law a v own hb]
  rfl

theorem native_incumbent_payoff (F : FiniteLowerConstruction i (N+1) R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin (N+1))
    (p : Value i×unitInterval) (hp : 0<(baseBid i p:ℝ)) :
    (problem (F.nativeGame H) a).payoff p.1 (OriginalPopulation.lowerAction i p)=
      rawUtility i N F.restricted.law p.1 (baseBid i p) :=
  F.native_positive_broadcast_payoff H a p.1 (OriginalPopulation.lowerAction i p)
    rfl (baseBid i p).property.2 hp

end FiniteLowerConstruction

structure NativeRestrictionRemoval {i : Row} {M : ℕ} {R : ℝ}
    (F : FiniteLowerConstruction i M R) (H : OriginalPopulation.UpperPriorityLaw i R) : Prop where
  incumbent_nonnegative : ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),∀a : Fin M,
    0≤(problem (F.nativeGame H) a).payoff p.1 (OriginalPopulation.lowerAction i p)
  broadcast_IC : ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),
    ∀a : Fin M,∀act : JointAction 2,act.routeCount=2→ act.bid< R→
      (problem (F.nativeGame H) a).payoff p.1 act≤
        (problem (F.nativeGame H) a).payoff p.1 (OriginalPopulation.lowerAction i p)
  below_floor_IC : ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),
    ∀a : Fin M,∀act : JointAction 2,act.bid< floorBid i p.1→
      (problem (F.nativeGame H) a).payoff p.1 act<
        (problem (F.nativeGame H) a).payoff p.1 (OriginalPopulation.lowerAction i p)
  above_cap_IC : ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),
    ∀a : Fin M,∀act : JointAction 2,cap i< act.bid→ act.bid< R→
      (problem (F.nativeGame H) a).payoff p.1 act≤
        (problem (F.nativeGame H) a).payoff p.1 (OriginalPopulation.lowerAction i p)

namespace NativeRestrictionRemoval
variable {i : Row} {N : ℕ} {R : ℝ}

theorem of_actual_floor (F : FiniteLowerConstruction i (N+1) R)
    (H : OriginalPopulation.UpperPriorityLaw i R)
    (hfloor : ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),
      ∀a : Fin (N+1),∀act : JointAction 2,act.bid< floorBid i p.1→
        (problem (F.nativeGame H) a).payoff p.1 act<
          (problem (F.nativeGame H) a).payoff p.1 (OriginalPopulation.lowerAction i p)) :
    NativeRestrictionRemoval F H := by
  have hsource : ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),
      0≤ rawUtility i N F.restricted.law p.1 (baseBid i p) := by
    change ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),
      0≤rawUtility i N (restrictedLaw i (0,F.restricted.pi)) p.1 (baseBid i p)
    simpa only [Nat.add_sub_cancel] using
      Late.restricted_incumbent_nonnegative i (N+1-1) F.restricted.pi F.restricted.restricted_IC
  have hnonneg : ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),∀a : Fin (N+1),
      0≤(problem (F.nativeGame H) a).payoff p.1 (OriginalPopulation.lowerAction i p) := by
    filter_upwards [F.restricted.common_conull_contract,hsource] with p hp hn
    intro a
    rw [F.native_incumbent_payoff H a p hp.2.1]
    exact hn
  have hrestricted:=F.restricted.actual_common_conull_restricted_IC H F.upper_floor
  have hbroadcast : ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),
      ∀a : Fin (N+1),∀act : JointAction 2,act.routeCount=2→ act.bid< R→
        (problem (F.nativeGame H) a).payoff p.1 act≤
          (problem (F.nativeGame H) a).payoff p.1 (OriginalPopulation.lowerAction i p) := by
    filter_upwards [F.restricted.common_conull_contract,hrestricted,F.all_broadcast_IC,
      hfloor,hnonneg] with p hp hr hs hf hn
    intro a act hroute hbR
    by_cases hU : cap i< act.bid
    · change (problem (Late.StrictOriginal.game F.restricted H) a).payoff p.1 act≤ _
      rw [Late.StrictOriginal.exceptional_broadcast_payoff F.restricted H F.upper_floor
        a p.1 act hU hbR hroute,F.native_incumbent_payoff H a p hp.2.1]
      have h:=hs act.bid act.bid_nonneg hbR
      simpa only [Late.extendedRawUtility,if_pos hU,Nat.add_sub_cancel] using h
    · have hcap : act.bid≤ cap i:=le_of_not_gt hU
      by_cases hlow : act.bid< floorBid i p.1
      · exact (hf a act hlow).le
      · by_cases hvalue : act.bid≤(p.1:ℝ)
        · change (problem (Late.StrictOriginal.game F.restricted H) a).payoff p.1 act≤
            (problem (Late.StrictOriginal.game F.restricted H) a).payoff p.1
              (OriginalPopulation.lowerAction i p)
          rw [Late.StrictOriginal.payoff_capped F.restricted H F.upper_floor a p.1 act hcap,
            Late.StrictOriginal.payoff_capped F.restricted H F.upper_floor a p.1
              (OriginalPopulation.lowerAction i p) (baseBid i p).property.2]
          exact hr.2.2 a act hroute ⟨le_of_not_gt hlow,le_min hvalue hcap⟩
        · have hpos : 0< act.bid:=p.1.property.1.trans_lt (lt_of_not_ge hvalue)
          rw [F.native_positive_broadcast_payoff H a p.1 act hroute hcap hpos]
          exact (Late.rawUtility_overbid i N F.restricted.law p.1.property.1
            (lt_of_not_ge hvalue)).trans (hn a)
  refine ⟨hnonneg,hbroadcast,hfloor,?_⟩
  filter_upwards [F.restricted.common_conull_contract,F.above_cap_routes,hbroadcast,hnonneg]
    with p hp hc hb hn
  intro a act hU hbR
  by_cases hz : act.routeCount=0
  · rw [NativeRoutes.zero_route_payoff (F.nativeGame H) a p.1 act hz]
    exact hn a
  · by_cases hsingle : act.routeCount=1
    · change (problem (Late.StrictOriginal.game F.restricted H) a).payoff p.1 act≤ _
      rw [Late.StrictOriginal.exceptional_singleton_payoff F.restricted H F.upper_floor
        a p.1 act hU hbR hsingle,F.native_incumbent_payoff H a p hp.2.1]
      simpa only [Nat.add_sub_cancel] using (hc act.bid hU hbR).2
    · have hfull : act.routeCount=2:=by have h:=act.routeCount_le;omega
      exact hb a act hfull hbR

end NativeRestrictionRemoval

structure NativeFiniteLowerConstruction (i : Row) (M : ℕ) (R : ℝ) where
  finite : FiniteLowerConstruction i M R
  actual : ∀H : OriginalPopulation.UpperPriorityLaw i R,NativeRestrictionRemoval finite H

namespace NativeFiniteLowerConstruction
variable {i : Row} {M : ℕ} {R : ℝ}

theorem market_pos (W : NativeFiniteLowerConstruction i M R) : 0< M :=
  lt_of_lt_of_le (by norm_num : (0:ℕ)<2) W.finite.restricted.cluster.market_two_le

def game (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    FiniteGame M 2 (Uniform07.capacity M) unitInterval := W.finite.nativeGame H

def belief (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) : PosteriorSystem (W.game H) :=
  W.finite.nativeBelief H

theorem proposer_optimal (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal (Uniform07.capacity M)
        (beliefReceipts (W.game H).A
          (posteriorCountBelief (W.game H) (W.belief H) j L) L)
        ((W.game H).policy j L s).val := W.finite.native_proposer_optimal H

theorem value_law (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    (W.game H).F=OriginalPopulation.uniformValue := rfl

theorem lower_kernel (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (v : Value i) :
    (W.game H).σ v=(W.finite.restricted.sigma v).map
      (fun q=> OriginalPopulation.lowerAction i (v,q)) := W.finite.native_lower_kernel H v

def typeLaw (W : NativeFiniteLowerConstruction i M R) (a : Fin M) (v : Value i) : CountLaw 2 :=
  letI : NeZero M:=W.finite.restricted.marketNeZero
  OriginalPopulation.indexedTypeLaw W.finite.restricted a v

theorem typeOutcome_eq (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin M) (v : Value i) :
    typeOutcome (W.game H) a v=W.typeLaw a v := by
  letI : NeZero M:=W.finite.restricted.marketNeZero
  exact Late.StrictOriginal.typeOutcome_original W.finite.restricted H W.finite.upper_floor a v

def typeTraceLaw (W : NativeFiniteLowerConstruction i M R) (a : Fin M)
    (v : Value i) : FiniteLaw (Bool × Bool) :=
  letI : NeZero M := W.finite.restricted.marketNeZero
  OriginalPopulation.indexedTypeTraceLaw W.finite.restricted a v

theorem actual_typeTraceLaw (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin M) (v : Value i) :
    NativeRoutes.actualTypeTraceLaw (W.game H) a v = W.typeTraceLaw a v := by
  letI : NeZero M := W.finite.restricted.marketNeZero
  exact Late.StrictOriginal.game_actualTypeTraceLaw W.finite.restricted H W.finite.upper_floor a v

theorem typeTraceLaw_fixed_kernel (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin M) (v : Value i)
    (f : Bool × Bool → ℝ) :
    (W.typeTraceLaw a v).expect f =
      ∫act, ∫ω, f (NativeRoutes.sampleTrace (W.game H) a act ω)
        ∂sampleLaw (W.game H) ∂(W.game H).σ v := by
  rw [← W.actual_typeTraceLaw H a v, NativeRoutes.actualTypeTraceLaw_expect]

theorem typeTraceLaw_broadcast_kernel (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin M) (v : Value i)
    (f : Bool × Bool → ℝ) :
    (W.typeTraceLaw a v).expect f =
      ∫act, (NativeRoutes.traceOutcome (W.game H) a act.bid).expect f ∂(W.game H).σ v := by
  letI : NeZero M := W.finite.restricted.marketNeZero
  have h := Late.StrictOriginal.game_typeTraceLaw W.finite.restricted H W.finite.upper_floor a v
  change NativeRoutes.typeTraceLaw (W.game H) a v = W.typeTraceLaw a v at h
  rw [← h, NativeRoutes.typeTraceLaw_expect]

theorem typeTraceLaw_count (W : NativeFiniteLowerConstruction i M R)
    (a : Fin M) (v : Value i) :
    (W.typeTraceLaw a v).map NativeCounts.traceCount = W.typeLaw a v := by
  letI : NeZero M := W.finite.restricted.marketNeZero
  exact OriginalPopulation.indexedTypeTraceLaw_count W.finite.restricted a v

def typeRecipientLaw (W : NativeFiniteLowerConstruction i M R) (a : Fin M)
    (j : Fin 2) (v : Value i) : CountLaw 2 :=
  (W.typeTraceLaw a v).map (NativeProfile.recipientCount j)

theorem actual_typeRecipientLaw (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin M)
    (j : Fin 2) (v : Value i) :
    NativeRoutes.actualTypeRecipientLaw (W.game H) a j v = W.typeRecipientLaw a j v := by
  rw [NativeRoutes.actualTypeRecipientLaw, W.actual_typeTraceLaw H a v]
  rfl

theorem typeRecipientLaw_actual_experiment (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin M)
    (j : Fin 2) (v : Value i) (f : Fin 3 → ℝ) :
    (W.typeRecipientLaw a j v).expect f =
      ∫act, ∫ω, f (NativeProfile.recipientCount j (NativeRoutes.sampleTrace (W.game H) a act ω))
        ∂sampleLaw (W.game H) ∂(W.game H).σ v := by
  rw [← W.actual_typeRecipientLaw H a j v, NativeRoutes.actualTypeRecipientLaw_expect]

theorem typeRecipientLaw_fixed_kernel (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin M)
    (j : Fin 2) (v : Value i) (f : Fin 3 → ℝ) :
    (W.typeRecipientLaw a j v).expect f =
      ∫act, (NativeRoutes.namedOutcome (W.game H) a act.bid j).expect f ∂(W.game H).σ v := by
  letI : NeZero M := W.finite.restricted.marketNeZero
  have h := Late.StrictOriginal.game_typeRecipientLaw W.finite.restricted H W.finite.upper_floor a j v
  change NativeRoutes.typeRecipientLaw (W.game H) a j v = W.typeRecipientLaw a j v at h
  rw [← h, NativeRoutes.typeRecipientLaw_expect]

theorem typeTraceLaw_original_integral (W : NativeFiniteLowerConstruction i M R)
    (a : Fin M) (f : Bool × Bool → ℝ) :
    letI : NeZero M := W.finite.restricted.marketNeZero
    (∫v, (W.typeTraceLaw a v).expect f ∂lowerMeasure i) =
      ∫p, (NativeProfile.indexedTraceLaw i W.finite.restricted.law a (baseBid i p)).expect f
        ∂(W.finite.restricted.pi.1 : Measure (Value i × unitInterval)) := by
  letI : NeZero M := W.finite.restricted.marketNeZero
  exact OriginalPopulation.indexedTypeTraceLaw_original_integral W.finite.restricted a f

def averagedTypeLaw (W : NativeFiniteLowerConstruction i M R) (v : Value i) : CountLaw 2 :=
  letI : NeZero M:=W.finite.restricted.marketNeZero
  FiniteLaw.uniformAverage W.market_pos (fun a : Fin M=> W.typeLaw a v)

theorem conditionalTypeCountLaw_eq (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) (v : Value i) :
    conditionalTypeCountLaw (W.game H) W.market_pos v=W.averagedTypeLaw v := by
  letI : NeZero M:=W.finite.restricted.marketNeZero
  exact Late.StrictOriginal.game_conditionalTypeCountLaw W.finite.restricted H W.finite.upper_floor v

theorem common_conull_contract (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀ᵐp∂(W.finite.restricted.pi.1 : Measure (Value i×unitInterval)),
      0<(p.1:ℝ) ∧ 0<(baseBid i p:ℝ) ∧
      (baseBid i p:ℝ)≤ cap i-capSlack i ∧
      (1-chi)*(baseBid i p:ℝ)*Lprob i M/2≤(p.1:ℝ)-(baseBid i p:ℝ) ∧
      ∀a : Fin M,
        0≤(problem (W.game H) a).payoff p.1 (OriginalPopulation.lowerAction i p) ∧
        (∀act : JointAction 2,act.routeCount=2→ act.bid< R→
          (problem (W.game H) a).payoff p.1 act≤
            (problem (W.game H) a).payoff p.1 (OriginalPopulation.lowerAction i p)) ∧
        (∀act : JointAction 2,act.bid< floorBid i p.1→
          (problem (W.game H) a).payoff p.1 act<
            (problem (W.game H) a).payoff p.1 (OriginalPopulation.lowerAction i p)) ∧
        (∀act : JointAction 2,cap i< act.bid→ act.bid< R→
          (problem (W.game H) a).payoff p.1 act≤
            (problem (W.game H) a).payoff p.1 (OriginalPopulation.lowerAction i p)) := by
  filter_upwards [W.finite.restricted.common_conull_contract,(W.actual H).incumbent_nonnegative,
    (W.actual H).broadcast_IC,(W.actual H).below_floor_IC,(W.actual H).above_cap_IC]
    with p hp hn hb hf hc
  exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,fun a=>⟨hn a,hb a,hf a,hc a⟩⟩

theorem conditional_broadcast_IC (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐq∂W.finite.restricted.sigma v,
      ∀a : Fin M,∀act : JointAction 2,act.routeCount=2→ act.bid< R→
        (problem (W.game H) a).payoff v act≤
          (problem (W.game H) a).payoff v (OriginalPopulation.lowerAction i (v,q)) := by
  have h:=(W.actual H).broadcast_IC
  have hdis : lowerMeasure i⊗ₘW.finite.restricted.sigma=
      (W.finite.restricted.pi.1 : Measure (Value i×unitInterval)) := W.finite.restricted.disintegration
  rw [← hdis] at h
  exact Measure.ae_ae_of_ae_compProd h

theorem native_kernel_contract (W : NativeFiniteLowerConstruction i M R)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐinc∂(W.game H).σ v,
      inc.routeCount=2 ∧ inc.bid∈Icc (floorBid i v) (hiBid i v) ∧
      inc.bid≤ cap i-capSlack i ∧
      ∀a : Fin M,
        0≤(problem (W.game H) a).payoff v inc ∧
        (∀act : JointAction 2,act.routeCount=2→ act.bid< R→
          (problem (W.game H) a).payoff v act≤(problem (W.game H) a).payoff v inc) ∧
        (∀act : JointAction 2,act.bid< floorBid i v→
          (problem (W.game H) a).payoff v act<(problem (W.game H) a).payoff v inc) ∧
        (∀act : JointAction 2,cap i< act.bid→ act.bid< R→
          (problem (W.game H) a).payoff v act≤(problem (W.game H) a).payoff v inc) := by
  have hj:=W.common_conull_contract H
  have hdis : lowerMeasure i⊗ₘW.finite.restricted.sigma=
      (W.finite.restricted.pi.1 : Measure (Value i×unitInterval)) := W.finite.restricted.disintegration
  rw [← hdis] at hj
  have hc:=Measure.ae_ae_of_ae_compProd hj
  filter_upwards [hc] with v hv
  have hvpos : 0<(v:ℝ):=hv.exists.choose_spec.1
  rw [W.lower_kernel H v,(NativeIC.lowerAction_embedding v hvpos).ae_map_iff]
  filter_upwards [hv] with q hq
  exact ⟨rfl,baseBid_bounds i (v,q),hq.2.2.1,hq.2.2.2.2⟩

end NativeFiniteLowerConstruction

theorem eventually_native_uniform_lower_construction (i : Row) :
    ∀ᶠM : ℕ in atTop,∀R : ℝ,cap i< R→ Nonempty (NativeFiniteLowerConstruction i M R) := by
  obtain ⟨N0,hN0⟩:=eventually_atTop.mp (Late.NativeFloor.eventually_strict_no_below_floor i)
  filter_upwards [eventually_finite_lower_construction i,eventually_ge_atTop (N0+1)]
    with M hF hM
  intro R hR
  let F:=Classical.choice (hF R hR)
  cases M with
  | zero => exact False.elim (by have h:=F.restricted.cluster.market_two_le;omega)
  | succ N =>
    refine ⟨⟨F,?_⟩⟩
    intro H
    apply NativeRestrictionRemoval.of_actual_floor F H
    exact hN0 N (by omega) F.restricted R H hR

theorem exists_eventual_uniform_lower_construction (i : Row) :
    ∃M0 : ℕ,∀M : ℕ,M0≤ M→∀R : ℝ,cap i< R→
      Nonempty (NativeFiniteLowerConstruction i M R) :=
  eventually_atTop.mp (eventually_native_uniform_lower_construction i)

end FCAppendix.Affine.UniformFinite
