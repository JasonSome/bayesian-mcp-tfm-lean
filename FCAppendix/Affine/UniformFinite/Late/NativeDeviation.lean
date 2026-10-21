import FCAppendix.Affine.UniformFinite.Late.ExceptionalIdentity
import FCAppendix.Affine.UniformFinite.Late.OnPathConditional
import FCAppendix.Affine.UniformFinite.NativeRoutes

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05 SourceContinuity
open scoped BigOperators

namespace ExceptionalCounts

theorem utility_actualCountLaw (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (v own : ℝ) (hown : cap i< own) :
    CountLaw.utility (actualCountLaw i N G own) v own 0
      (Schedule.affine 2 (eta i) (eta_range i).1.le (eta_range i).2.le)
      (Schedule.once 2)=Exceptional.rawUtility i N G v own := by
  rw [CountLaw.utility,actualCountLaw_expect i N G own hown]
  simp only [← pairPayoff_as_count,Exceptional.rawUtility,Exceptional.rowPayoff,focalBids_zero]

theorem pairCount_load {M : ℕ} (a : Fin M) (P : Allocation M) :
    ((pairCount a P).val:ℝ)=routeIndicator 0 a P+routeIndicator 1 a P := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    norm_num [pairCount,routeIndicator,WeightedSampling.indicator,h0,h1]

theorem singleton_actualCountLaw (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (v own : ℝ) (hown : cap i< own) :
    (v-own)*CountLaw.load (actualCountLaw i N G own)/2=
      Exceptional.oneRouteRawUtility i N G v own := by
  have hi (j : Fin 2) : Integrable
      (fun x : NativeCounts.Sample i N=>(v-own)*routeIndicator j 0 (draw i G own x))
      (NativeCounts.law i N G) :=
    Integrable.of_bound (((measurable_of_countable
      (fun P : Allocation (N+1)=>(v-own)*routeIndicator j 0 P)).comp
        (measurable_draw i G own)).aestronglyMeasurable) (|v-own|)
      (ae_of_all _ (fun x=> by
        rw [Real.norm_eq_abs,abs_mul,
          abs_of_nonneg (Exceptional.routeIndicator_bounds j 0 _).1]
        exact mul_le_of_le_one_right (abs_nonneg _) (Exceptional.routeIndicator_bounds j 0 _).2))
  rw [CountLaw.load,actualCountLaw,FiniteLaw.expect_ofMeasure,← integral_const_mul]
  have he (x : NativeCounts.Sample i N) :
      (v-own)*((pairCount 0 (draw i G own x)).val:ℝ)=
        (v-own)*routeIndicator 0 0 (draw i G own x)+
          (v-own)*routeIndicator 1 0 (draw i G own x) := by
    rw [pairCount_load]
    ring
  simp_rw [he]
  rw [integral_add (hi 0) (hi 1),named_recipient_utility i N G 0 v own hown,
    named_recipient_utility i N G 1 v own hown]
  rfl

end ExceptionalCounts

namespace StrictOriginal
variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

omit [NeZero M] in

theorem deviated_original_list (a : Fin M) (u : JointAction 2) (hu : u.bid≤ cap i)
    (ω : Bayes.Sample M 2 unitInterval)
    (hω : ω.1.1∈Strict.strongProfiles M (cap i) R) (j : Fin 2) :
    Strict.OriginalList (cap i) R (observe (deviated a u ω) j) := by
  intro k b he
  have hhere : j∈(deviated a u ω).recipients k := by
    by_contra hn
    simp only [observe,if_neg hn] at he
    cases he
  have hb : ((deviated a u ω).action k).bid=b := by
    apply Option.some.inj
    simpa only [observe,if_pos hhere] using he
  by_cases hka : k=a
  · subst k
    rw [deviated_bid_self] at hb
    exact Or.inl (hb ▸ hu)
  · rw [deviated_bid_other a k hka] at hb
    rcases hω k with hk|hk
    · exact Or.inl (hb ▸ hk.1)
    · exact Or.inr (hb ▸ hk.1)

theorem focalCount_capped (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (ω : Bayes.Sample M 2 unitInterval)
    (hω : ω.1.1∈Strict.strongProfiles M (cap i) R)
    (a : Fin M) (u : JointAction 2) (hu : u.bid≤ cap i) :
    focalCount (game E H) a u ω=focalCount (OriginalPopulation.game E H) a u ω := by
  have halloc : allocation (deviated a u ω) (game E H).policy ω.1.2=
      allocation (deviated a u ω) (OriginalPopulation.game E H).policy ω.1.2 := by
    funext j
    exact policy_on_original_list E H hR j _ (deviated_original_list a u hu ω hω j) (ω.1.2 j)
  apply Fin.ext
  change (accepted (deviated a u ω) (game E H).policy ω.1.2 a).card=
    (accepted (deviated a u ω) (OriginalPopulation.game E H).policy ω.1.2 a).card
  simp only [accepted,halloc]

theorem focalCount_capped_common (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐω∂sampleLaw (game E H),∀a : Fin M,∀u : JointAction 2,u.bid≤ cap i→
      focalCount (game E H) a u ω=focalCount (OriginalPopulation.game E H) a u ω := by
  have hp : ∀ᵐω∂sampleLaw (game E H),ω.1.1∈Strict.strongProfiles M (cap i) R :=
    ((measurePreserving_fst (μ:=userProfileLaw (game E H))
      (ν:=Measure.pi (fun _ : Fin 2=>(game E H).seedLaw))).comp
        (measurePreserving_fst (μ:=backgroundLaw (game E H))
          (ν:=permLaw 2))).quasiMeasurePreserving.ae (game_profile_support E H)
  exact hp.mono (fun ω hω a u hu=> focalCount_capped E H hR ω hω a u hu)

theorem outcome_capped (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (u : JointAction 2) (hu : u.bid≤ cap i) :
    (problem (game E H) a).outcome u=(problem (OriginalPopulation.game E H) a).outcome u := by
  apply FiniteLaw.ext_expect
  intro f
  rw [problem_outcome,CountLaw.expect_ofMeasure,problem_outcome,CountLaw.expect_ofMeasure]
  have hμ : sampleLaw (OriginalPopulation.game E H)=sampleLaw (game E H) := rfl
  rw [hμ]
  apply integral_congr_ae
  filter_upwards [focalCount_capped_common E H hR] with ω hω
  rw [hω a u hu]

theorem payoff_capped (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (v : ℝ) (u : JointAction 2) (hu : u.bid≤ cap i) :
    (problem (game E H) a).payoff v u=(problem (OriginalPopulation.game E H) a).payoff v u := by
  change ((problem (game E H) a).outcome u).utility v u.bid 0
    (Schedule.affine 2 (eta i) (eta_range i).1.le (eta_range i).2.le) (Schedule.once 2)=_
  rw [outcome_capped E H hR a u hu]
  rfl

theorem broadcast_outcome_capped (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (own : Bid i) :
    (problem (game E H) a).outcome (Hybrid.lowBroadcast own)=
      NativeProfile.indexedLaw i E.law a own := by
  rw [outcome_capped E H hR a _ own.property.2,
    OriginalPopulation.game_broadcast_outcome E H hR a own]

theorem broadcast_payoff_capped (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (v : ℝ) (own : Bid i) :
    (problem (game E H) a).payoff v (Hybrid.lowBroadcast own)=
      NativeIndexed.utility i E.law a v own := by
  rw [payoff_capped E H hR a v _ own.property.2,NativeIndexed.game_payoff E H hR a v own]

theorem typeOutcome_original (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (v : Value i) :
    typeOutcome (game E H) a v=OriginalPopulation.indexedTypeLaw E a v := by
  exact game_typeOutcome E H hR a v

theorem exceptional_outcome_indexed (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (u : JointAction 2) (hU : cap i< u.bid) (hu : u.bid< R)
    (hr : u.routeCount=2) :
    (problem (game E H) a).outcome u=ExceptionalProfile.indexedLaw i E.law a u.bid := by
  have hs:=game_profile_support E H
  have hp:=OriginalPopulation.game_numeric_profiles E H hR
  change (problem (Strict.constructedGame i E.law (OriginalPopulation.seedLaw E)
    (OriginalPopulation.primitiveGame E H) R) a).outcome u=_
  rw [OriginalPopulation.seedLaw_eq_native]
  exact ExceptionalProfile.native_outcome_indexed i E.law
    (OriginalPopulation.primitiveGame E H) rfl hR hs hp a u hU hu hr

variable {N : ℕ}

theorem exceptional_outcome (E : ExactRestrictedLaw i (N+1))
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin (N+1)) (u : JointAction 2) (hU : cap i< u.bid) (hu : u.bid< R)
    (hr : u.routeCount=2) :
    (problem (game E H) a).outcome u=ExceptionalCounts.actualCountLaw i N E.law u.bid := by
  rw [exceptional_outcome_indexed E H hR a u hU hu hr,
    ExceptionalProfile.indexedLaw_eq_actual i E.law a u.bid hU]

theorem exceptional_broadcast_payoff (E : ExactRestrictedLaw i (N+1))
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin (N+1)) (v : ℝ) (u : JointAction 2)
    (hU : cap i< u.bid) (hu : u.bid< R) (hr : u.routeCount=2) :
    (problem (game E H) a).payoff v u=Exceptional.rawUtility i N E.law v u.bid := by
  change ((problem (game E H) a).outcome u).utility v u.bid 0
    (Schedule.affine 2 (eta i) (eta_range i).1.le (eta_range i).2.le) (Schedule.once 2)=_
  rw [exceptional_outcome E H hR a u hU hu hr,
    ExceptionalCounts.utility_actualCountLaw i N E.law v u.bid hU]

theorem exceptional_singleton_payoff (E : ExactRestrictedLaw i (N+1))
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin (N+1)) (v : ℝ) (u : JointAction 2)
    (hU : cap i< u.bid) (hu : u.bid< R) (hr : u.routeCount=1) :
    (problem (game E H) a).payoff v u=Exceptional.oneRouteRawUtility i N E.law v u.bid := by
  let full : JointAction 2:=⟨u.bid,u.bid_nonneg,2,le_rfl⟩
  rw [NativeRoutes.singleton_payoff_eq_broadcast_load (game E H) a v u full hr rfl rfl,
    exceptional_outcome E H hR a full hU hu rfl]
  change (v-0-u.bid)*CountLaw.load (ExceptionalCounts.actualCountLaw i N E.law u.bid)/2=_
  rw [sub_zero,ExceptionalCounts.singleton_actualCountLaw i N E.law v u.bid hU]

end StrictOriginal
end FCAppendix.Affine.UniformFinite.Late
