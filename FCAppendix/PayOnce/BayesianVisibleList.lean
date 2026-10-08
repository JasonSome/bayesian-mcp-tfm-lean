import FCAppendix.PayOnce.BayesianCommonList

namespace FCAppendix
namespace Bayes

open MeasureTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

abbrev VisibleUser (ℓ : LocalList m) := {i : Fin m // ℓ i ≠ none}

noncomputable instance (ℓ : LocalList m) : Fintype (VisibleUser ℓ) := Fintype.ofFinite _

noncomputable def visibleSet (ℓ : LocalList m) (S : Finset (Fin m)) :
    Finset (VisibleUser ℓ) := by
  classical
  exact S.subtype (fun i => ℓ i ≠ none)

theorem mem_visibleSet (ℓ : LocalList m) (S : Finset (Fin m)) (i : VisibleUser ℓ) :
    i ∈ visibleSet ℓ S ↔ i.val ∈ S := by
  classical
  simp [visibleSet]

theorem visibleSet_map (ℓ : LocalList m) (S : Finset (Fin m))
    (hS : ∀ i ∈ S, ℓ i ≠ none) :
    (visibleSet ℓ S).map (Function.Embedding.subtype _) = S := by
  classical
  exact Finset.subtype_map_of_mem hS

theorem visibleSet_card (ℓ : LocalList m) (S : Finset (Fin m))
    (hS : ∀ i ∈ S, ℓ i ≠ none) : (visibleSet ℓ S).card = S.card := by
  have h := congrArg Finset.card (visibleSet_map ℓ S hS)
  simpa only [Finset.card_map] using h

noncomputable def visibleLottery (ℓ : LocalList m) (μ : FiniteLaw (Finset (Fin m))) :
    FiniteLaw (Finset (VisibleUser ℓ)) := μ.map (visibleSet ℓ)

theorem visibleLottery_support (ℓ : LocalList m) (μ : FiniteLaw (Finset (Fin m)))
    (S : Finset (VisibleUser ℓ)) (hS : (visibleLottery ℓ μ).mass S ≠ 0) :
    ∃ T, μ.mass T ≠ 0 ∧ visibleSet ℓ T = S := by
  classical
  by_contra! h
  apply hS
  simp only [visibleLottery, FiniteLaw.map]
  apply Finset.sum_eq_zero
  intro T _
  split_ifs with hT
  · by_contra hm
    exact h T hm hT
  · rfl

theorem visibleLottery_marginal (ℓ : LocalList m) (μ : FiniteLaw (Finset (Fin m)))
    (i : VisibleUser ℓ) :
    Proposer.marginal (visibleLottery ℓ μ) i = Proposer.marginal μ i.val := by
  classical
  rw [CommonList.marginal_eq_expect, CommonList.marginal_eq_expect]
  unfold visibleLottery
  rw [FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro S
  simp only [mem_visibleSet]

theorem optimal_visibleSet (ℓ : LocalList m) (S : Finset (Fin m)) (r : Fin m → ℝ)
    (hS : ∀ i ∈ S, ℓ i ≠ none) (hopt : Finite.Optimal c r S) :
    Finite.Optimal c (fun i : VisibleUser ℓ => r i.val) (visibleSet ℓ S) := by
  classical
  constructor
  · rw [visibleSet_card ℓ S hS]
    exact hopt.1
  · intro T hT
    have hcap : (T.map (Function.Embedding.subtype _)).card ≤ c := by simpa using hT
    have h := hopt.2 (T.map (Function.Embedding.subtype _)) hcap
    have hs : (∑ i ∈ visibleSet ℓ S, r i.val) = ∑ i ∈ S, r i := by
      exact Finset.sum_subtype_of_mem r hS
    rw [hs]
    simpa only [Finset.sum_map, Function.Embedding.subtype_apply] using h

noncomputable def visibleBid (ℓ : LocalList m) (i : VisibleUser ℓ) : ℝ := (ℓ i.val).getD 0

theorem visibleEntry (ℓ : LocalList m) (i : VisibleUser ℓ) :
    ℓ i.val = some (visibleBid ℓ i) := by
  unfold visibleBid
  cases he : ℓ i.val with
  | none => exact False.elim (i.property he)
  | some b => rfl

section PayOnce

variable {k : ℕ}

theorem seedLottery_support_exists_ae (Γ : FiniteGame m (k + 1) c Seed)
    (j : Fin (k + 1)) (ℓ : LocalList m) (S : Finset (Fin m))
    (hS : (seedLottery Γ j ℓ).mass S ≠ 0) (P : Seed → Prop) (hP : ∀ᵐ s ∂Γ.seedLaw, P s) :
    ∃ s, (Γ.policy j ℓ s).val = S ∧ P s := by
  have hmass : Γ.seedLaw {s | (Γ.policy j ℓ s).val = S} ≠ 0 := by
    intro hzero
    apply hS
    unfold seedLottery
    rw [FiniteLaw.ofMeasure_mass, hzero, ENNReal.toReal_zero]
  obtain ⟨s, hs, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass (ae_restrict_of_ae hP)
  exact ⟨s, hs, hp⟩

theorem visible_payOnceEquilibrium_of_posterior_ae (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (j : Fin (k + 1)) (ℓ : LocalList m)
    (hopt : ∀ᵐ s ∂Γ.seedLaw, Finite.Optimal c
      (beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    CommonList.PayOnceEquilibrium (k + 1) c (visibleBid ℓ) (visibleLottery ℓ μ) := by
  have hr : (fun i : VisibleUser ℓ => beliefReceipts Γ.A
        (posteriorCountBelief Γ B j ℓ) ℓ i.val) =
      fun i => visibleBid ℓ i * PayOnce.H (k + 1)
        (Proposer.marginal (visibleLottery ℓ μ) i) := by
    funext i
    simp only [beliefReceipts, visibleEntry ℓ i, visibleLottery_marginal]
    exact posterior_payOnce_receipt Γ hA B j ℓ hcommon μ hμ i.val (visibleBid ℓ i)
  have hsupp : ∀ S, (visibleLottery ℓ μ).mass S ≠ 0 →
      Finite.Optimal c (fun i => visibleBid ℓ i * PayOnce.H (k + 1)
        (Proposer.marginal (visibleLottery ℓ μ) i)) S := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := visibleLottery_support ℓ μ S hS
    have ht : (seedLottery Γ j ℓ).mass T ≠ 0 := by rwa [hμ j]
    obtain ⟨s, hs, hoptS⟩ := seedLottery_support_exists_ae Γ j ℓ T ht _ hopt
    rw [← hr, ← hs]
    exact optimal_visibleSet ℓ (Γ.policy j ℓ s).val _ (Γ.policy j ℓ s).property.2 hoptS
  apply (CommonList.payOnceEquilibrium_iff (k + 1) (by omega) c
    (visibleBid ℓ) (visibleLottery ℓ μ)).mpr
  refine ⟨fun S hS => (hsupp S hS).1, ?_⟩
  intro ν hν
  unfold Proposer.revenue
  apply (visibleLottery ℓ μ).const_le_expect_of_support
  intro S hS
  apply ν.expect_le_const_of_support
  intro T hT
  exact (hsupp S hS).2 T (hν T hT)

theorem visible_payOnceEquilibrium_of_posterior (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimal Γ B) (j : Fin (k + 1)) (ℓ : LocalList m)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    CommonList.PayOnceEquilibrium (k + 1) c (visibleBid ℓ) (visibleLottery ℓ μ) :=
  visible_payOnceEquilibrium_of_posterior_ae Γ hA B j ℓ
    (Filter.Eventually.of_forall (hB j ℓ)) hcommon μ hμ

def PosteriorProposerOptimalOnPath (Γ : FiniteGame m (k + 1) c Seed)
    (B : PosteriorSystem Γ) : Prop :=
  ∀ j, ∀ᵐ ℓ ∂observedListLaw Γ j, ∀ᵐ s ∂Γ.seedLaw,
    Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ)
      (Γ.policy j ℓ s).val

theorem ae_visible_payOnceEquilibrium_of_routes (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalOnPath Γ B) (j : Fin (k + 1))
    (hroute : ∀ᵐ p ∂(Γ.F ⊗ₘ Γ.σ), p.2.routeCount = 0 ∨ p.2.routeCount = k + 1)
    (hsym : ∀ᵐ ℓ ∂observedListLaw Γ j, SymmetricAtList Γ ℓ (seedLottery Γ j ℓ)) :
    ∀ᵐ ℓ ∂observedListLaw Γ j,
      CommonList.PayOnceEquilibrium (k + 1) c (visibleBid ℓ)
        (visibleLottery ℓ (seedLottery Γ j ℓ)) := by
  have hc := B.ae_commonLists Γ j (ae_commonLists_of_zero_or_full_routes Γ hroute j)
  filter_upwards [hc, hsym, hB j] with ℓ hℓ hs hb
  exact visible_payOnceEquilibrium_of_posterior_ae Γ hA B j ℓ hb hℓ _ hs

theorem posterior_visibleList_kernel (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (ℓ : LocalList m) (hc : c ≤ Fintype.card (VisibleUser ℓ))
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimal Γ B) (j : Fin (k + 1))
    (hb : ∀ i : VisibleUser ℓ, 0 < visibleBid ℓ i)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    ∃ L, 0 < L ∧
      (∀ i : VisibleUser ℓ, Proposer.marginal μ i.val = CommonList.kernel (k + 1) (visibleBid ℓ i) L) ∧
      ∑ i : VisibleUser ℓ, CommonList.kernel (k + 1) (visibleBid ℓ i) L = c := by
  obtain ⟨L, hL, hcoord, hsum⟩ := CommonList.equilibrium_kernel (k + 1) (by omega)
    (visibleBid ℓ) hb c hc (visibleLottery ℓ μ)
    (visible_payOnceEquilibrium_of_posterior Γ hA B hB j ℓ hcommon μ hμ)
  exact ⟨L, hL, fun i => (visibleLottery_marginal ℓ μ i).symm.trans (hcoord i), hsum⟩

theorem posterior_visibleList_small (Γ : FiniteGame m (k + 1) c Seed)
    (ℓ : LocalList m) (hc : Fintype.card (VisibleUser ℓ) ≤ c)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (j : Fin (k + 1))
    (hopt : ∀ᵐ s ∂Γ.seedLaw, Finite.Optimal c
      (beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val)
    (hb : ∀ i : VisibleUser ℓ, 0 < visibleBid ℓ i)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ)
    (i : VisibleUser ℓ) : Proposer.marginal μ i.val = 1 := by
  have he := (CommonList.payOnceEquilibrium_small_list_iff (k + 1) (by omega)
    (visibleBid ℓ) hb c hc (visibleLottery ℓ μ)).mp
    (visible_payOnceEquilibrium_of_posterior_ae Γ hA B j ℓ hopt hcommon μ hμ)
  rw [← visibleLottery_marginal ℓ μ i, he, CommonList.marginal_dirac]
  simp

end PayOnce
end Bayes
end FCAppendix
