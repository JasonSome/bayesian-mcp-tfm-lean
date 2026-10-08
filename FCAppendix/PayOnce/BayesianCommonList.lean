import FCAppendix.Game.CommonListSeeds

namespace FCAppendix
namespace Bayes

open MeasureTheory Game
open scoped BigOperators

variable {m k c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem posterior_payOnce_receipt (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (j : Fin (k + 1)) (ℓ : LocalList m)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) (i : Fin m) (b : ℝ) :
    Finite.conditionalReceipt Γ.A (posteriorCountBelief Γ B j ℓ i) b =
      b * PayOnce.H (k + 1) (Proposer.marginal μ i) := by
  rw [hA, posteriorCountBelief_binomial Γ B j ℓ hcommon μ hμ i]
  unfold Finite.conditionalReceipt
  simp only [Schedule.once, successIndicator, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceIte, mul_one]
  rw [← PayOnce.balanced_receipt k (Proposer.marginal μ i)
    (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i),
    ← FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_congr
  intro r
  ring

theorem payOnceEquilibrium_of_posterior (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimal Γ B) (j : Fin (k + 1))
    (ℓ : LocalList m) (b : Fin m → ℝ) (hℓ : ∀ i, ℓ i = some (b i))
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    CommonList.PayOnceEquilibrium (k + 1) c b μ := by
  have hr : beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ =
      fun i => b i * PayOnce.H (k + 1) (Proposer.marginal μ i) := by
    funext i
    simp only [beliefReceipts, hℓ i]
    exact posterior_payOnce_receipt Γ hA B j ℓ hcommon μ hμ i (b i)
  have hfeas : CommonList.Feasible c μ := by
    rw [← hμ j]
    exact seedLottery_feasible Γ j ℓ
  have hopt : ∀ S, μ.mass S ≠ 0 →
      Finite.Optimal c (fun i => b i * PayOnce.H (k + 1) (Proposer.marginal μ i)) S := by
    intro S hS
    have hs : (seedLottery Γ j ℓ).mass S ≠ 0 := by rwa [hμ j]
    obtain ⟨s, rfl⟩ := seedLottery_support_exists Γ j ℓ S hs
    simpa only [hr] using hB j ℓ s
  apply (CommonList.payOnceEquilibrium_iff (k + 1) (by omega) c b μ).mpr
  refine ⟨hfeas, ?_⟩
  intro ν hν
  unfold Proposer.revenue
  apply μ.const_le_expect_of_support
  intro S hS
  apply ν.expect_le_const_of_support
  intro T hT
  exact (hopt S hS).2 T (hν T hT)

theorem posterior_commonList_kernel (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : c ≤ m) (hA : Γ.A = Schedule.once (k + 1))
    (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimal Γ B)
    (j : Fin (k + 1)) (ℓ : LocalList m) (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (hℓ : ∀ i, ℓ i = some (b i))
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    ∃ L, 0 < L ∧ (∀ i, Proposer.marginal μ i = CommonList.kernel (k + 1) (b i) L) ∧
      ∑ i, CommonList.kernel (k + 1) (b i) L = c :=
  CommonList.equilibrium_kernel (k + 1) (by omega) b hb c (by simpa using hc) μ
    (payOnceEquilibrium_of_posterior Γ hA B hB j ℓ b hℓ hcommon μ hμ)

theorem ae_payOnceEquilibrium_of_commonLists (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimal Γ B) (j : Fin (k + 1))
    (hcommon : ∀ᵐ d ∂userProfileLaw Γ,
      ∀ l, observe (drawsRealization d) l = observe (drawsRealization d) j)
    (hsym : ∀ᵐ ℓ ∂observedListLaw Γ j, SymmetricAtList Γ ℓ (seedLottery Γ j ℓ)) :
    ∀ᵐ ℓ ∂observedListLaw Γ j, ∀ b : Fin m → ℝ,
      (∀ i, ℓ i = some (b i)) →
        CommonList.PayOnceEquilibrium (k + 1) c b (seedLottery Γ j ℓ) := by
  filter_upwards [B.ae_commonLists Γ j hcommon, hsym] with ℓ hℓ hsymℓ
  intro b hb
  exact payOnceEquilibrium_of_posterior Γ hA B hB j ℓ b hb hℓ _ hsymℓ

end Bayes
end FCAppendix
