import FCAppendix.Exclusive.CanonicalGame
import FCAppendix.Exclusive.MarkerConstructionSource

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem sourcePosterior_common_of_not_eligible (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (cutoff : ℝ) (hroom : n-1 ≤ m-n*c)
    (Q : Set (UserProfile m n)) (hQmeas : MeasurableSet Q)
    (hQfull : ∀ᵐ d ∂userProfileLaw Γ, d ∈ Q)
    (hQbroadcast : ∀ d ∈ Q, d ∈ broadcastProfiles m n)
    (j : Fin n) (L : LocalList m) (hL : FeasibleObservedList j L)
    (helig : ¬ Marker.SourceEligible hm cutoff L n c) :
    let B := posteriorWithFallback Γ hQmeas hQfull
      (fun j => Marker.sourceFallbackKernel (c := c) hm j cutoff)
      (fun j L hL => Marker.sourceFallbackKernel_feasible hm j cutoff hroom L hL)
    ∀ᵐ d ∂B.posterior j L, ∀ l, observe (drawsRealization d) l = L := by
  classical
  change ∀ᵐ d ∂posteriorWithFallbackKernel Γ hQmeas
    (fun j => Marker.sourceFallbackKernel (c := c) hm j cutoff) j L, _
  by_cases hg : L ∈ goodPosteriorLists Γ Q j
  · simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_pos hg]
    have hp : ∀ᵐ d ∂regularUserPosterior Γ j L,
        observe (drawsRealization d) j = L ∧ d ∈ Q := ae_iff.mpr hg
    filter_upwards [hp] with d hd
    intro l
    exact (observe_eq_of_zero_or_full_routes d (hQbroadcast d hd.2) l j).trans hd.1
  · simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_neg hg,
      Marker.sourceFallbackKernel,Set.mem_setOf_eq,if_neg helig,broadcastFallback,
      Kernel.deterministic_apply,ae_dirac_eq]
    exact fun l => observe_completedProfile l L
      ((feasibleObservedList_iff_nonnegative j L).mp hL)

theorem source_seedLottery_of_not_eligible (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ L, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback L s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids L))
    (hpolicy : ∀ j L s, (Γ.policy j L s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback L s).val)
    (j : Fin n) (L : LocalList m) (helig : ¬ Marker.SourceEligible hm cutoff L n c) :
    seedLottery Γ j L = canonicalLottery n hn c (listBids L) := by
  classical
  have he : (fun s => (Γ.policy j L s).val) = fun s => (fallback L s).val := by
    funext s
    rw [hpolicy]
    simp only [Marker.sourceContinuation,dif_neg helig]
  unfold seedLottery
  convert hcanonical L using 1
  congr 1

theorem constructed_source_proposer_optimal (Γ : FiniteGame m (k+1) c Seed)
    (hm : 0 < m) (hn : 2 ≤ k+1) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ L, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback L s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery (k+1) hn c (listBids L))
    (hpolicy : ∀ j L s, (Γ.policy j L s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback L s).val)
    (hroom : (k+1)-1 ≤ m-(k+1)*c)
    (Q : Set (UserProfile m (k+1))) (hQmeas : MeasurableSet Q)
    (hQfull : ∀ᵐ d ∂userProfileLaw Γ, d ∈ Q)
    (hQbroadcast : ∀ d ∈ Q, d ∈ broadcastProfiles m (k+1))
    (hQhigh : ∀ d ∈ Q, ∀ i, (d i).1.2.routeCount=0 ∨ cutoff ≤ (d i).1.2.bid) :
    let B := posteriorWithFallback Γ hQmeas hQfull
      (fun j => Marker.sourceFallbackKernel (c := c) hm j cutoff)
      (fun j L hL => Marker.sourceFallbackKernel_feasible hm j cutoff hroom L hL)
    ExclusivePosteriorOptimalAE Γ B := by
  classical
  let B := posteriorWithFallback Γ hQmeas hQfull
    (fun j => Marker.sourceFallbackKernel (c := c) hm j cutoff)
    (fun j L hL => Marker.sourceFallbackKernel_feasible hm j cutoff hroom L hL)
  change ExclusivePosteriorOptimalAE Γ B
  intro j L hL
  by_cases helig : Marker.SourceEligible hm cutoff L (k+1) c
  · exact Eventually.of_forall fun s => Marker.constructed_marker_optimal Γ hm hn hc
      cutoff fallback hpolicy hroom Q hQmeas hQfull hQhigh j L helig hL s
  · let mu := canonicalLottery (k+1) hn c (listBids L)
    have hsym : SymmetricAtList Γ L mu := fun l =>
      source_seedLottery_of_not_eligible Γ hm hn hc cutoff fallback hfallback hcanonical
        hpolicy l L helig
    have hcommon : ∀ᵐ d ∂B.posterior j L, ∀ l, observe (drawsRealization d) l = L :=
      sourcePosterior_common_of_not_eligible Γ hm cutoff hroom Q hQmeas hQfull
        hQbroadcast j L hL helig
    have hr : exclusiveReceipts (posteriorCountBelief Γ B j L) L =
        fun i => listBids L i*(1-canonicalMarginal (k+1) hn c (listBids L) i)^k := by
      funext i
      cases he : L i with
      | none => simp [exclusiveReceipts,he,listBids,readBid]
      | some b =>
        rw [exclusiveReceipts_some _ _ _ _ he]
        have hx := posterior_exclusive_receipt Γ B j L hcommon mu hsym i b
        simpa only [mu,canonicalLottery_marginal,listBids,he,readBid] using hx
    apply FiniteLaw.ae_property_of_ofMeasure Γ.seedLaw (fun s => (Γ.policy j L s).val)
      (measurable_policy_at_list Γ j L) mu (hsym j)
      (fun S => Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j L) L) S)
    intro S hS
    rw [hr]
    simpa only [Nat.add_sub_cancel] using
      canonicalLottery_support_optimal (k+1) hn c (listBids L) S hS

end FCAppendix.Bayes.ExclusiveConstruction
