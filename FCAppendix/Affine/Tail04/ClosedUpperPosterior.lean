import FCAppendix.Affine.Tail04.ClosedUpperPriority
import FCAppendix.Affine.Hybrid.ClassifiedReceipts

noncomputable section
namespace FCAppendix.Affine.Tail04.ClosedUpperPriority
open MeasureTheory ProbabilityTheory Set Filter Game Bayes Classical
open scoped BigOperators

def closedProfiles (m : ℕ) (R : ℝ) : Set (UserProfile m 2) :=
  {d | ∀ i, ((d i).1.2.bid< R ∧ (d i).1.2.routeCount=2) ∨
    (R≤(d i).1.2.bid ∧ (d i).1.2.routeCount=1)}

theorem measurableSet_closedProfiles (m : ℕ) (R : ℝ) :
    MeasurableSet (closedProfiles m R) := by
  simp only [closedProfiles,setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have ha : Measurable (fun d : UserProfile m 2 => (d i).1.2) :=
    (measurable_pi_apply i).fst.snd
  have hb := (measurable_bid 2).comp ha
  have hr := (measurable_routeCount 2).comp ha
  exact ((measurableSet_lt hb measurable_const).inter
    (measurableSet_eq_fun hr measurable_const)).union
      ((measurableSet_le measurable_const hb).inter
        (measurableSet_eq_fun hr measurable_const))

def encodedAction (R : ℝ) (a : JointAction 2) : JointAction 2 :=
  ⟨encodeBid R a.bid,encodeBid_nonnegative R a.bid a.bid_nonneg,
    a.routeCount,a.routeCount_le⟩

def encodedProfile {m : ℕ} (R : ℝ) (d : UserProfile m 2) : UserProfile m 2 :=
  fun i => (((d i).1.1,encodedAction R (d i).1.2),(d i).2)

theorem observe_encodedProfile {m : ℕ} (R : ℝ) (d : UserProfile m 2) (j : Fin 2) :
    observe (drawsRealization (encodedProfile R d)) j=
      encodeList R (observe (drawsRealization d) j) := by
  funext i
  simp only [observe,drawsRealization,encodedProfile,encodedAction,encodeList]
  split_ifs <;> rfl

theorem encodedProfile_classified {m : ℕ} {R : ℝ} (d : UserProfile m 2)
    (hd : d∈closedProfiles m R) : encodedProfile R d∈Hybrid.classifiedProfiles m R := by
  intro i
  rcases hd i with hlow | hupp
  · left
    change encodeBid R (d i).1.2.bid≤ R ∧ (d i).1.2.routeCount=2
    rw [encodeBid_lower R _ hlow.1]
    exact ⟨hlow.1.le,hlow.2⟩
  · right
    change R< encodeBid R (d i).1.2.bid ∧ (d i).1.2.routeCount=1
    rw [encodeBid_upper R _ hupp.1]
    exact ⟨by linarith [hupp.1],hupp.2⟩

def closedContext {m : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList m) : Hybrid.ClassifiedContext m :=
  Hybrid.observedContext R j (encodeList R L)

def closedLowerList {m : ℕ} (R : ℝ) (L : LocalList m) : LocalList m :=
  Hybrid.broadcastPart R (encodeList R L)

theorem closedContext_common {m : ℕ} {R : ℝ} (d : UserProfile m 2)
    (hd : d∈closedProfiles m R) (j l : Fin 2) :
    closedContext R j (observe (drawsRealization d) j)=
      closedContext R l (observe (drawsRealization d) l) := by
  unfold closedContext
  rw [←observe_encodedProfile,←observe_encodedProfile,
    Hybrid.observedContext_eq_actual _ (encodedProfile_classified d hd) j,
    Hybrid.observedContext_eq_actual _ (encodedProfile_classified d hd) l]

theorem closedLowerList_common {m : ℕ} {R : ℝ} (d : UserProfile m 2)
    (hd : d∈closedProfiles m R) (j l : Fin 2) :
    closedLowerList R (observe (drawsRealization d) j)=
      closedLowerList R (observe (drawsRealization d) l) := by
  unfold closedLowerList
  rw [←observe_encodedProfile,←observe_encodedProfile]
  exact Hybrid.broadcastPart_common _ (encodedProfile_classified d hd) j l

theorem closedLowerList_some {m : ℕ} {R b : ℝ} (L : LocalList m) (i : Fin m)
    (hi : L i=some b) (hb : b< R) : closedLowerList R L i=some b := by
  apply Hybrid.broadcastPart_some _ i _ hb.le
  simp only [encodeList,hi,Option.map_some,encodeBid_lower R b hb]

def closedAction (R : ℝ) : Option ℝ → JointAction 2
  | none => ⟨max R 0,le_max_right _ _,1,by omega⟩
  | some b => ⟨max b 0,le_max_right _ _,if b< R then 2 else 1,by split_ifs <;> omega⟩

theorem measurable_closedAction (R : ℝ) : Measurable (closedAction R) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  intro S hS
  change MeasurableSet ((fun b : ℝ => (max b 0,if b< R then (2:ℕ) else 1)) ⁻¹' S)
  exact (((measurable_id.max measurable_const).prodMk
    (Measurable.ite measurableSet_Iio measurable_const measurable_const))) hS

def closedProfile (m : ℕ) (R : ℝ) (j : Fin 2) (L : LocalList m) : UserProfile m 2 :=
  fun i => ((0,closedAction R (L i)),Hybrid.classifiedOrdering j (L i))

theorem measurable_closedProfile (m : ℕ) (R : ℝ) (j : Fin 2) :
    Measurable (closedProfile m R j) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_const.prodMk
    ((measurable_closedAction R).comp (measurable_pi_apply i))).prodMk
      ((Hybrid.measurable_classifiedOrdering j).comp (measurable_pi_apply i))

theorem observe_closedProfile {m : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) : observe (drawsRealization (closedProfile m R j L)) j=L := by
  funext i
  cases he : L i with
  | none => simp [observe,drawsRealization,closedProfile,closedAction,
      Hybrid.classifiedOrdering,he,Hybrid.firstK_routeTo]
  | some b =>
    have hb : 0≤ b := by simpa only [NonnegativeList,he,entryBid] using hL i
    by_cases hbR : b< R
    · simp [observe,drawsRealization,closedProfile,closedAction,Hybrid.classifiedOrdering,
        he,hbR,Hybrid.firstK_full_two,max_eq_left hb]
    · simp [observe,drawsRealization,closedProfile,closedAction,Hybrid.classifiedOrdering,
        he,hbR,Hybrid.firstK_routeTo,max_eq_left hb]

theorem closedProfile_mem {m : ℕ} {R : ℝ} (hR : 0≤ R)
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    closedProfile m R j L∈closedProfiles m R := by
  intro i
  cases he : L i with
  | none =>
    right
    change R≤(closedAction R (L i)).bid ∧ (closedAction R (L i)).routeCount=1
    simp only [he,closedAction,max_eq_left hR]
    exact ⟨le_rfl,trivial⟩
  | some b =>
    have hb : 0≤ b := by simpa only [NonnegativeList,he,entryBid] using hL i
    by_cases hbR : b< R
    · left
      simp [closedProfile,closedAction,he,hbR,max_eq_left hb]
    · right
      simp [closedProfile,closedAction,he,hbR,max_eq_left hb,le_of_not_gt hbR]

def closedFallback (m : ℕ) (R : ℝ) (j : Fin 2) : Kernel (LocalList m) (UserProfile m 2) :=
  Kernel.deterministic (closedProfile m R j) (measurable_closedProfile m R j)

instance closedFallback_markov (m : ℕ) (R : ℝ) (j : Fin 2) :
    IsMarkovKernel (closedFallback m R j) := by
  unfold closedFallback
  infer_instance

theorem closedFallback_feasible {m : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂closedFallback m R j L,observe (drawsRealization d) j=L := by
  rw [closedFallback,Kernel.deterministic_apply]
  apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
  exact observe_closedProfile R j L ((feasibleObservedList_iff_nonnegative j L).mp hL)

section Native
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def closedPosterior (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐ d ∂userProfileLaw Γ,d∈closedProfiles m R) : PosteriorSystem Γ :=
  posteriorWithFallback Γ (measurableSet_closedProfiles m R) hfull
    (closedFallback m R) (closedFallback_feasible R)

theorem closedPosterior_support (Γ : FiniteGame m 2 c Seed) (R : ℝ) (hR : 0≤ R)
    (hfull : ∀ᵐ d ∂userProfileLaw Γ,d∈closedProfiles m R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂(closedPosterior Γ R hfull).posterior j L,
      observe (drawsRealization d) j=L ∧ d∈closedProfiles m R := by
  change ∀ᵐ d ∂posteriorWithFallbackKernel Γ (measurableSet_closedProfiles m R)
    (closedFallback m R) j L,_
  by_cases hgood : L∈goodPosteriorLists Γ (closedProfiles m R) j
  · simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_pos hgood]
    exact ae_iff.mpr hgood
  · simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_neg hgood,
      closedFallback,Kernel.deterministic_apply]
    apply (ae_dirac_iff ((measurableSet_eq_lists (measurable_observe_draws j) measurable_const).inter
      (measurableSet_closedProfiles m R))).mpr
    have hnonneg := (feasibleObservedList_iff_nonnegative j L).mp hL
    exact ⟨observe_closedProfile R j L hnonneg,closedProfile_mem hR j L hnonneg⟩

theorem closedPosterior_infeasible (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐ d ∂userProfileLaw Γ,d∈closedProfiles m R)
    (j : Fin 2) (L : LocalList m) (hL : ¬FeasibleObservedList j L) :
    (closedPosterior Γ R hfull).posterior j L=
      Measure.dirac (closedProfile m R j L) := by
  have hnot : L∉goodPosteriorLists Γ (closedProfiles m R) j := by
    intro hgood
    have hs : ∀ᵐ d ∂regularUserPosterior Γ j L,
        observe (drawsRealization d) j=L ∧ d∈closedProfiles m R := ae_iff.mpr hgood
    obtain ⟨d,hd⟩ := hs.exists
    exact hL ⟨d,hd.1⟩
  change posteriorWithFallbackKernel Γ (measurableSet_closedProfiles m R)
    (closedFallback m R) j L=_
  simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_neg hnot,
    closedFallback,Kernel.deterministic_apply]

theorem closedProfiles_of_joint (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hjoint : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ, (x.2.bid< R ∧ x.2.routeCount=2) ∨
      (R≤ x.2.bid ∧ x.2.routeCount=1)) :
    ∀ᵐ d ∂userProfileLaw Γ,d∈closedProfiles m R := by
  have hu : ∀ᵐ d ∂userLaw Γ, (d.1.2.bid< R ∧ d.1.2.routeCount=2) ∨
      (R≤ d.1.2.bid ∧ d.1.2.routeCount=1) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hjoint
  exact ae_all_iff.mpr (fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae hu)

variable (C : Hybrid.ContextPolicy m c Seed) (Γ : FiniteGame m 2 c Seed) (R : ℝ)
local notation "G" => nativeGame C Γ R

theorem closedPosterior_lower_mean (hR : 0≤ R)
    (hfull : ∀ᵐ d ∂userProfileLaw G,d∈closedProfiles m R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : b< R) :
    Hybrid.posteriorOtherMean G (closedPosterior G R hfull) j L i=
      Hybrid.contextAcceptance G C.select (Hybrid.otherProposer j) (closedContext R j L) i := by
  rw [Hybrid.posteriorOtherMean_eq_profile_integral]
  have hstat : ∀ᵐ d ∂(closedPosterior G R hfull).posterior j L,
      (∫ s : Fin 2 → Seed,((otherInclusionCount G j i (d,s)).val:ℝ)
        ∂Measure.pi (fun _ : Fin 2 => (G).seedLaw))=
      Hybrid.contextAcceptance G C.select (Hybrid.otherProposer j) (closedContext R j L) i := by
    filter_upwards [closedPosterior_support G R hR hfull j L hL] with d hd
    have hctx : closedContext R (Hybrid.otherProposer j)
        (observe (drawsRealization d) (Hybrid.otherProposer j))=closedContext R j L := by
      rw [closedContext_common d hd.2 (Hybrid.otherProposer j) j,hd.1]
    have hlow : closedLowerList R (observe (drawsRealization d) (Hybrid.otherProposer j)) i≠none := by
      rw [closedLowerList_common d hd.2 (Hybrid.otherProposer j) j,hd.1,
        closedLowerList_some L i hi hb]
      simp
    have heq (s : Fin 2 → Seed) : ((otherInclusionCount G j i (d,s)).val:ℝ)=
        if i∈C.select (Hybrid.otherProposer j) (closedContext R j L)
          (s (Hybrid.otherProposer j)) then 1 else 0 := by
      rw [Hybrid.otherInclusionCount_two]
      have hf := C.factors R (Hybrid.otherProposer j)
        (encodeList R (observe (drawsRealization d) (Hybrid.otherProposer j)))
        (s (Hybrid.otherProposer j)) i hlow
      change (i∈selection C R (Hybrid.otherProposer j)
        (observe (drawsRealization d) (Hybrid.otherProposer j)) (s (Hybrid.otherProposer j)) ↔
          i∈C.select (Hybrid.otherProposer j)
            (closedContext R (Hybrid.otherProposer j)
              (observe (drawsRealization d) (Hybrid.otherProposer j)))
                (s (Hybrid.otherProposer j))) at hf
      rw [hctx] at hf
      simp only [allocation,nativeGame,localPolicy,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      simp only [hf]
    rw [integral_congr_ae (Eventually.of_forall heq)]
    let f : Seed → ℝ := fun s =>
      if i∈C.select (Hybrid.otherProposer j) (closedContext R j L) s then 1 else 0
    have hm : Measurable f := Measurable.ite
      (((C.measurable (Hybrid.otherProposer j)).comp (measurable_const.prodMk measurable_id))
        (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i∈S}))
      measurable_const measurable_const
    have hp := measurePreserving_eval (fun _ : Fin 2 => (G).seedLaw) (Hybrid.otherProposer j)
    change (∫ s : Fin 2 → Seed,f (s (Hybrid.otherProposer j))
      ∂Measure.pi (fun _ => (G).seedLaw))=∫ s,f s ∂(G).seedLaw
    calc
      _ = ∫ s,f s ∂(Measure.pi (fun _ : Fin 2 => (G).seedLaw)).map
          (fun s => s (Hybrid.otherProposer j)) :=
        (integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable).symm
      _ = _ := by rw [hp.map_eq]
  calc
    _ = ∫ _d,Hybrid.contextAcceptance G C.select (Hybrid.otherProposer j)
        (closedContext R j L) i ∂(closedPosterior G R hfull).posterior j L := integral_congr_ae hstat
    _ = _ := by simp

theorem closed_upper_other_absent (d : UserProfile m 2) (hd : d∈closedProfiles m R)
    (j : Fin 2) (i : Fin m) (b : ℝ)
    (hi : observe (drawsRealization d) j i=some b) (hb : R≤ b) :
    observe (drawsRealization d) (Hybrid.otherProposer j) i=none := by
  have hj : j∈(drawsRealization d).recipients i := by
    by_contra hn
    simp only [observe,if_neg hn] at hi
    cases hi
  have hbid : (d i).1.2.bid=b := by
    change ((drawsRealization d).action i).bid=b
    apply Option.some.inj
    simpa only [observe,if_pos hj] using hi
  have hr : (d i).1.2.routeCount=1 := by
    rcases hd i with hlow | hupp
    · rw [hbid] at hlow
      exact False.elim (not_lt_of_ge hb hlow.1)
    · exact hupp.2
  have hc : ((drawsRealization d).recipients i).card=1 := by
    rw [(drawsRealization d).chosen_size]
    exact hr
  obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hc
  have hlj : l=j := by
    rw [hl] at hj
    exact (Finset.mem_singleton.mp hj).symm
  rw [hlj] at hl
  simp only [observe,hl,Finset.mem_singleton,Hybrid.otherProposer_ne,if_false]

theorem closedPosterior_upper_mean (hR : 0≤ R)
    (hfull : ∀ᵐ d ∂userProfileLaw G,d∈closedProfiles m R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : R≤ b) :
    Hybrid.posteriorOtherMean G (closedPosterior G R hfull) j L i=0 := by
  rw [Hybrid.posteriorOtherMean_eq_profile_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [closedPosterior_support G R hR hfull j L hL] with d hd
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro s
  have hobs : observe (drawsRealization d) j i=some b := by rw [hd.1,hi]
  have hnone := closed_upper_other_absent R d hd.2 j i b hobs hb
  have hnot : i∉allocation (drawsRealization d) (G).policy s (Hybrid.otherProposer j) := by
    intro hin
    exact (((G).policy (Hybrid.otherProposer j) (observe (drawsRealization d) (Hybrid.otherProposer j))
      (s (Hybrid.otherProposer j))).property.2 i hin) hnone
  change ((otherInclusionCount G j i (d,s)).val:ℝ)=0
  rw [Hybrid.otherInclusionCount_two,if_neg hnot]
  norm_num

end Native

section Replacement
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (C : Hybrid.ContextPolicy m c Seed) (Γ Γ' : FiniteGame m 2 c Seed) (R : ℝ)
local notation "G" => nativeGame C Γ R
local notation "G'" => nativeGame C Γ' R

theorem closedPosterior_infeasible_count_eq
    (hseed : Γ.seedLaw=Γ'.seedLaw)
    (hfull : ∀ᵐ d ∂userProfileLaw G,d∈closedProfiles m R)
    (hfull' : ∀ᵐ d ∂userProfileLaw G',d∈closedProfiles m R)
    (j : Fin 2) (L : LocalList m) (hL : ¬FeasibleObservedList j L) (i : Fin m) :
    posteriorCountBelief G (closedPosterior G R hfull) j L i=
      posteriorCountBelief G' (closedPosterior G' R hfull') j L i := by
  have hback : posteriorBackground G (closedPosterior G R hfull) j L=
      posteriorBackground G' (closedPosterior G' R hfull') j L := by
    unfold posteriorBackground
    rw [closedPosterior_infeasible G R hfull j L hL,
      closedPosterior_infeasible G' R hfull' j L hL]
    change (Measure.dirac (closedProfile m R j L)).prod
      (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))=
      (Measure.dirac (closedProfile m R j L)).prod
        (Measure.pi (fun _ : Fin 2 => Γ'.seedLaw))
    rw [hseed]
  unfold posteriorCountBelief
  simp only [hback]
  rfl

theorem closedPosterior_receipts_invariant (hR : 0≤ R)
    (hseed : Γ.seedLaw=Γ'.seedLaw)
    (hfull : ∀ᵐ d ∂userProfileLaw G,d∈closedProfiles m R)
    (hfull' : ∀ᵐ d ∂userProfileLaw G',d∈closedProfiles m R)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hA' : Γ'.A=Schedule.affine 2 η hη0 hη1)
    (j : Fin 2) (L : LocalList m) :
    beliefReceipts (G).A (posteriorCountBelief G (closedPosterior G R hfull) j L) L=
      beliefReceipts (G').A (posteriorCountBelief G' (closedPosterior G' R hfull') j L) L := by
  funext i
  cases hi : L i with
  | none => simp only [beliefReceipts,hi]
  | some b =>
    simp only [beliefReceipts,hi]
    by_cases hL : FeasibleObservedList j L
    · rw [Hybrid.posterior_affine_receipt G _ η hη0 hη1 hA,
        Hybrid.posterior_affine_receipt G' _ η hη0 hη1 hA']
      by_cases hb : b< R
      · rw [closedPosterior_lower_mean C Γ R hR hfull j L hL i b hi hb,
          closedPosterior_lower_mean C Γ' R hR hfull' j L hL i b hi hb]
        change b*(1-(1-η)/2*(∫s,if i∈C.select (Hybrid.otherProposer j)
          (closedContext R j L) s then (1:ℝ) else 0 ∂Γ.seedLaw))=
          b*(1-(1-η)/2*(∫s,if i∈C.select (Hybrid.otherProposer j)
            (closedContext R j L) s then (1:ℝ) else 0 ∂Γ'.seedLaw))
        rw [hseed]
      · rw [closedPosterior_upper_mean C Γ R hR hfull j L hL i b hi (le_of_not_gt hb),
          closedPosterior_upper_mean C Γ' R hR hfull' j L hL i b hi (le_of_not_gt hb)]
    · rw [closedPosterior_infeasible_count_eq C Γ Γ' R hseed hfull hfull' j L hL i]
      have hAA : (G).A=(G').A := hA.trans hA'.symm
      rw [hAA]

theorem closedPosterior_proposers_transfer (hR : 0≤ R)
    (hseed : Γ.seedLaw=Γ'.seedLaw)
    (hfull : ∀ᵐ d ∂userProfileLaw G,d∈closedProfiles m R)
    (hfull' : ∀ᵐ d ∂userProfileLaw G',d∈closedProfiles m R)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hA' : Γ'.A=Schedule.affine 2 η hη0 hη1)
    (hopt : PosteriorProposerOptimal G (closedPosterior G R hfull)) :
    PosteriorProposerOptimal G' (closedPosterior G' R hfull') := by
  intro j L s
  have he := closedPosterior_receipts_invariant C Γ Γ' R hR hseed hfull hfull'
    η hη0 hη1 hA hA' j L
  rw [←he]
  exact hopt j L s

theorem closedPosterior_feasible_proposers_transfer (hR : 0≤ R)
    (hseed : Γ.seedLaw=Γ'.seedLaw)
    (hfull : ∀ᵐ d ∂userProfileLaw G,d∈closedProfiles m R)
    (hfull' : ∀ᵐ d ∂userProfileLaw G',d∈closedProfiles m R)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hA' : Γ'.A=Schedule.affine 2 η hη0 hη1)
    (hopt : ∀ j L,FeasibleObservedList j L → ∀ s,
      Finite.Optimal c
        (beliefReceipts (G).A (posteriorCountBelief G (closedPosterior G R hfull) j L) L)
        ((G).policy j L s).val) :
    ∀ j L,FeasibleObservedList j L → ∀ s,
      Finite.Optimal c
        (beliefReceipts (G').A (posteriorCountBelief G' (closedPosterior G' R hfull') j L) L)
        ((G').policy j L s).val := by
  intro j L hL s
  rw [←closedPosterior_receipts_invariant C Γ Γ' R hR hseed hfull hfull' η hη0 hη1 hA hA' j L]
  exact hopt j L hL s

end Replacement

section Population
variable {m c : ℕ} (C : Hybrid.ContextPolicy m c unitInterval)

theorem population_closedProfiles
    (U R s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    ∀ᵐ d ∂userProfileLaw
      (populationGame C U R s a h hs ha hh hsum PL PA PH η hη0 hη1),
      d∈closedProfiles m R := by
  apply closedProfiles_of_joint
  rw [populationGame_joint_law C U R s a h hs ha hh hsum PL PA PH η hη0 hη1]
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure (hL.mono (fun _ hx => Or.inl hx)) _,
      Measure.ae_smul_measure (hA.mono (fun _ hx => Or.inl hx)) _⟩,
        Measure.ae_smul_measure (hH.mono (fun _ hx => Or.inr hx)) _⟩

end Population
end FCAppendix.Affine.Tail04.ClosedUpperPriority
