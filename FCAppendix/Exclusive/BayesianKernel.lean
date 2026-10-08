import FCAppendix.Exclusive.EquilibriumKernel
import FCAppendix.Exclusive.OnceBayes
import FCAppendix.PayOnce.VisibleDummyKernel

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def ExclusiveOptimalOnPath (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) : Prop :=
  ∀ j, ∀ᵐ ℓ ∂observedListLaw Γ j, ∀ᵐ s ∂Γ.seedLaw,
    Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ)
      (Γ.policy j ℓ s).val

theorem exclusiveOptimalOnPath_of_feasible (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalAE Γ B) :
    ExclusiveOptimalOnPath Γ B := by
  intro j
  filter_upwards [B.ae_observation Γ j] with ℓ hℓ
  obtain ⟨d, hd⟩ := hℓ.exists
  exact hB j ℓ ⟨d, hd⟩

theorem posterior_exclusive_receipt (Γ : FiniteGame m (k + 1) c Seed)
    (B : PosteriorSystem Γ) (j : Fin (k + 1)) (ℓ : LocalList m)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ)
    (i : Fin m) (b : ℝ) :
    b * (posteriorCountBelief Γ B j ℓ i).prob (fun r => r.val = 0) =
      b * (1 - Proposer.marginal μ i) ^ k := by
  rw [posteriorCountBelief_binomial Γ B j ℓ hcommon μ hμ i]
  exact Exclusive.exclusive_receipt k (Proposer.marginal μ i) b
    (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i)

theorem visible_exclusiveEquilibrium_of_posterior_ae
    (Γ : FiniteGame m (k + 1) c Seed) (B : PosteriorSystem Γ)
    (j : Fin (k + 1)) (ℓ : LocalList m)
    (hopt : ∀ᵐ s ∂Γ.seedLaw, Finite.Optimal c
      (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    Exclusive.ExclusiveEquilibrium (k + 1) c (visibleBid ℓ) (visibleLottery ℓ μ) := by
  classical
  have hr : (fun i : VisibleUser ℓ => exclusiveReceipts
        (posteriorCountBelief Γ B j ℓ) ℓ i.val) =
      fun i => visibleBid ℓ i * (1 - Proposer.marginal (visibleLottery ℓ μ) i) ^ k := by
    funext i
    simp only [exclusiveReceipts, visibleEntry ℓ i, visibleLottery_marginal]
    exact posterior_exclusive_receipt Γ B j ℓ hcommon μ hμ i.val (visibleBid ℓ i)
  have hsupp : ∀ S, (visibleLottery ℓ μ).mass S ≠ 0 →
      Finite.Optimal c (fun i => visibleBid ℓ i *
        (1 - Proposer.marginal (visibleLottery ℓ μ) i) ^ k) S := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := visibleLottery_support ℓ μ S hS
    have ht : (seedLottery Γ j ℓ).mass T ≠ 0 := by rwa [hμ j]
    obtain ⟨s, hs, hsopt⟩ := seedLottery_support_exists_ae Γ j ℓ T ht _ hopt
    rw [← hr, ← hs]
    exact optimal_visibleSet ℓ (Γ.policy j ℓ s).val _
      (Γ.policy j ℓ s).property.2 hsopt
  refine ⟨fun S hS => (hsupp S hS).1, ?_⟩
  intro ν hν
  rw [Exclusive.exclusive_payoff_eq, Exclusive.exclusive_payoff_eq]
  simp only [Nat.add_sub_cancel]
  rw [← Proposer.revenue_marginals, ← Proposer.revenue_marginals]
  unfold Proposer.revenue
  apply (visibleLottery ℓ μ).const_le_expect_of_support
  intro S hS
  apply ν.expect_le_const_of_support
  intro T hT
  exact (hsupp S hS).2 T (hν T hT)

theorem ae_visible_exclusiveEquilibrium_of_routes
    (Γ : FiniteGame m (k + 1) c Seed) (B : PosteriorSystem Γ)
    (hB : ExclusiveOptimalOnPath Γ B) (j : Fin (k + 1))
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      x.2.routeCount = 0 ∨ x.2.routeCount = k + 1)
    (hsym : ∀ᵐ ℓ ∂observedListLaw Γ j, SymmetricAtList Γ ℓ (seedLottery Γ j ℓ)) :
    ∀ᵐ ℓ ∂observedListLaw Γ j,
      Exclusive.ExclusiveEquilibrium (k + 1) c (visibleBid ℓ)
        (visibleLottery ℓ (seedLottery Γ j ℓ)) := by
  have hc := B.ae_commonLists Γ j (ae_commonLists_of_zero_or_full_routes Γ hroute j)
  filter_upwards [hc, hsym, hB j] with ℓ hℓ hs hb
  exact visible_exclusiveEquilibrium_of_posterior_ae Γ B j ℓ hb hℓ _ hs

theorem posterior_exclusive_kernel (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (B : PosteriorSystem Γ) (j : Fin (k + 1)) (ℓ : LocalList m)
    (hopt : ∀ᵐ s ∂Γ.seedLaw, Finite.Optimal c
      (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val)
    (hb : ∀ i : VisibleUser ℓ, 0 < visibleBid ℓ i)
    (hc : c < Fintype.card (VisibleUser ℓ))
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ i : VisibleUser ℓ,
        Proposer.marginal μ i.val = Exclusive.demand (k + 1) (visibleBid ℓ i) lam) ∧
      (∑ i : VisibleUser ℓ, Exclusive.demand (k + 1) (visibleBid ℓ i) lam) = c := by
  obtain ⟨lam, hlam, hcoord, hroot⟩ := Exclusive.equilibrium_kernel (k + 1) (by omega)
    (visibleBid ℓ) hb c hc (visibleLottery ℓ μ)
    (visible_exclusiveEquilibrium_of_posterior_ae Γ B j ℓ hopt hcommon μ hμ)
  exact ⟨lam, hlam, fun i => (visibleLottery_marginal ℓ μ i).symm.trans (hcoord i), hroot⟩

theorem sum_seed_marginal_visible (Γ : FiniteGame m n c Seed)
    (j : Fin n) (ℓ : LocalList m) :
    (∑ i : VisibleUser ℓ, Proposer.marginal (visibleLottery ℓ (seedLottery Γ j ℓ)) i) =
      ∑ i, Proposer.marginal (seedLottery Γ j ℓ) i := by
  classical
  simp_rw [visibleLottery_marginal]
  have h := Fintype.sum_subtype_add_sum_subtype (p := fun i => ℓ i ≠ none)
    (Proposer.marginal (seedLottery Γ j ℓ))
  have hz : (∑ i : {i : Fin m // ¬ ℓ i ≠ none},
      Proposer.marginal (seedLottery Γ j ℓ) i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact seedLottery_marginal_absent Γ j ℓ i.val (not_not.mp i.property)
  simp only [hz, add_zero] at h
  convert h using 1
  congr 1
  ext i
  simp

noncomputable def exclusiveProfileMarginal (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (i : Fin m) : ℝ := (profileCountLaw Γ d i).load / n

theorem measurable_exclusiveProfileMarginal (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (fun d => exclusiveProfileMarginal Γ d i) := by
  simpa only [exclusiveProfileMarginal, CountLaw.load] using
    (measurable_profile_expect Γ i (fun r => (r.val : ℝ))).div_const (n : ℝ)

theorem exclusiveProfileMarginal_bounds (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (d : UserProfile m n) (i : Fin m) :
    0 ≤ exclusiveProfileMarginal Γ d i ∧ exclusiveProfileMarginal Γ d i ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨div_nonneg (CountLaw.load_nonneg _) hnR.le, ?_⟩
  exact (div_le_one hnR).mpr (CountLaw.load_le_n _)

theorem exclusiveProfileMarginal_eq_seed (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (d : UserProfile m n) (ℓ : LocalList m)
    (hcommon : ∀ j, observe (drawsRealization d) j = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) (i : Fin m) :
    exclusiveProfileMarginal Γ d i = Proposer.marginal μ i := by
  unfold exclusiveProfileMarginal
  rw [profileCountLaw_binomial Γ d ℓ hcommon μ hμ i, IndependentCounts.binomial_load]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)

theorem ae_exclusive_profile_laws (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (B : PosteriorSystem Γ) (hB : ExclusiveOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k + 1))
    (j : Fin (k + 1)) :
    ∀ᵐ d ∂userProfileLaw Γ,
      (∀ i, profileCountLaw Γ d i = IndependentCounts.binomial (k + 1)
        (exclusiveProfileMarginal Γ d i)
        (exclusiveProfileMarginal_bounds Γ (by omega) d i).1
        (exclusiveProfileMarginal_bounds Γ (by omega) d i).2) ∧
      (∑ i, exclusiveProfileMarginal Γ d i) =
        (min c (Fintype.card (VisibleUser (observe (drawsRealization d) j))) : ℕ) ∧
      (∀ i, (d i).1.2.routeCount = 0 → exclusiveProfileMarginal Γ d i = 0) := by
  classical
  have hr := hroute.mono fun _ hx => hx.imp_right And.right
  have hcommon := ae_commonLists_of_zero_or_full_routes Γ hr j
  have hgame := ae_visible_exclusiveEquilibrium_of_routes Γ B hB j hr (hsym j)
  have hgameD := ae_of_ae_map (measurable_observe_draws j).aemeasurable hgame
  have hsymD := ae_of_ae_map (measurable_observe_draws j).aemeasurable (hsym j)
  have huser := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw (k + 1))).quasiMeasurePreserving.ae hroute
  have hdraw : ∀ᵐ d ∂userProfileLaw Γ, ∀ i,
      (d i).1.2.routeCount = 0 ∨
        (0 < (d i).1.2.bid ∧ (d i).1.2.routeCount = k + 1) :=
    ae_all_iff.mpr fun i =>
      (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae huser
  filter_upwards [hcommon, hgameD, hsymD, hdraw] with d hd hg hs hrD
  let ℓ := observe (drawsRealization d) j
  let μ := seedLottery Γ j ℓ
  have hbid : ∀ i : VisibleUser ℓ, 0 < visibleBid ℓ i := by
    intro i
    rcases hrD i.val with hz | ⟨hb, hfull⟩
    · have hnone : ℓ i.val = none := by
        simp [ℓ, observe, drawsRealization, mem_firstK, hz]
      exact (i.property hnone).elim
    · have hentry : ℓ i.val = some (d i.val).1.2.bid := by
        simp [ℓ, observe, drawsRealization, mem_firstK, hfull]
        exact Nat.le_of_lt_succ ((d i.val).2 j).isLt
      simpa only [visibleBid, hentry, Option.getD_some] using hb
  have hp (i : Fin m) : exclusiveProfileMarginal Γ d i = Proposer.marginal μ i :=
    exclusiveProfileMarginal_eq_seed Γ (by omega) d ℓ hd μ hs i
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hlaw := profileCountLaw_binomial Γ d ℓ hd μ hs i
    exact hlaw.trans (CommonList.binomial_congr (k + 1) (hp i).symm _ _ _ _)
  · simp_rw [hp]
    rw [← sum_seed_marginal_visible Γ j ℓ]
    exact Exclusive.equilibrium_sum_marginal (k + 1) (by omega)
      (visibleBid ℓ) hbid c (visibleLottery ℓ μ) hg
  · intro i hi
    rw [hp i]
    apply seedLottery_marginal_absent Γ j ℓ i
    simp [ℓ, observe, drawsRealization, mem_firstK, hi]

end FCAppendix.Bayes
