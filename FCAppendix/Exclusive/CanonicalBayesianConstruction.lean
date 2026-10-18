import FCAppendix.Exclusive.BroadcastConstruction
import FCAppendix.Exclusive.BayesianKernel
import FCAppendix.Proposer.LotterySupport

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction

open MeasureTheory ProbabilityTheory Game Set Filter Exclusive

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def broadcastProfiles (m n : ℕ) : Set (UserProfile m n) :=
  {d | ∀ i, (d i).1.2.routeCount = 0 ∨ (d i).1.2.routeCount = n}

theorem measurableSet_broadcastProfiles (m n : ℕ) :
    MeasurableSet (broadcastProfiles m n) := by
  simp only [broadcastProfiles, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hm : Measurable (fun d : UserProfile m n => (d i).1.2.routeCount) :=
    (measurable_routeCount n).comp
      (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))
  exact (measurableSet_eq_fun hm measurable_const).union
    (measurableSet_eq_fun hm measurable_const)

def commonListPosterior (Γ : FiniteGame m n c Seed)
    (hroute : ∀ᵐ d ∂userProfileLaw Γ, d ∈ broadcastProfiles m n) : PosteriorSystem Γ :=
  posteriorWithFallback Γ (measurableSet_broadcastProfiles m n) hroute
    (fun _ => broadcastFallback m n) broadcastFallback_feasible

theorem commonListPosterior_common (Γ : FiniteGame m n c Seed)
    (hroute : ∀ᵐ d ∂userProfileLaw Γ, d ∈ broadcastProfiles m n)
    (j : Fin n) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂(commonListPosterior Γ hroute).posterior j L,
      ∀ l, observe (drawsRealization d) l = L := by
  classical
  change ∀ᵐ d ∂posteriorWithFallbackKernel Γ (measurableSet_broadcastProfiles m n)
    (fun _ => broadcastFallback m n) j L, _
  by_cases hg : L ∈ goodPosteriorLists Γ (broadcastProfiles m n) j
  · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_pos hg]
    have hp : ∀ᵐ d ∂regularUserPosterior Γ j L,
        observe (drawsRealization d) j = L ∧ d ∈ broadcastProfiles m n := ae_iff.mpr hg
    filter_upwards [hp] with d hd
    intro l
    exact (observe_eq_of_zero_or_full_routes d hd.2 l j).trans hd.1
  · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_neg hg,
      broadcastFallback, Kernel.deterministic_apply, ae_dirac_eq]
    exact fun l => observe_completedProfile l L
      ((feasibleObservedList_iff_nonnegative j L).mp hL)

theorem canonical_policy_bayesian_optimal
    (Γ : FiniteGame m (k+1) c Seed) (hn : 2 ≤ k+1) (B : PosteriorSystem Γ)
    (hcommon : ∀ j L, FeasibleObservedList j L →
      ∀ᵐ d ∂B.posterior j L, ∀ l, observe (drawsRealization d) l = L)
    (hlaw : ∀ j L, seedLottery Γ j L = canonicalLottery (k+1) hn c (listBids L)) :
    ExclusivePosteriorOptimalAE Γ B := by
  classical
  intro j L hL
  let μ := canonicalLottery (k+1) hn c (listBids L)
  have hsym : SymmetricAtList Γ L μ := fun l => hlaw l L
  have hr : exclusiveReceipts (posteriorCountBelief Γ B j L) L =
      fun i => listBids L i*(1-canonicalMarginal (k+1) hn c (listBids L) i)^k := by
    funext i
    cases he : L i with
    | none => simp [exclusiveReceipts, he, listBids, readBid]
    | some b =>
      rw [exclusiveReceipts_some _ _ _ _ he]
      have hx := posterior_exclusive_receipt Γ B j L (hcommon j L hL) μ hsym i b
      simpa only [μ, canonicalLottery_marginal, listBids, he, readBid] using hx
  apply FiniteLaw.ae_property_of_ofMeasure Γ.seedLaw
    (fun s => (Γ.policy j L s).val) (measurable_policy_at_list Γ j L) μ (hlaw j L)
    (fun S => Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j L) L) S)
  intro S hS
  rw [hr]
  simpa only [Nat.add_sub_cancel] using
    canonicalLottery_support_optimal (k+1) hn c (listBids L) S hS

end FCAppendix.Bayes.ExclusiveConstruction
