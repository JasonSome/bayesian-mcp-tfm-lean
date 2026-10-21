import FCAppendix.AppendixRepair.GeneralLow.NormalizedContinuation
import FCAppendix.AppendixRepair.GeneralLow.DirectGame

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.Implementation
open MeasureTheory ProbabilityTheory Game Bayes Set Filter
open HigherPolicy HigherPosterior HigherReceipts Continuation
open scoped BigOperators

variable {m c : ℕ}

def game (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
    (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) : FiniteGame m 2 c unitInterval :=
  { Γ with
    policy := DirectGame.localPolicy C d ξ hξ hξ1 c
      (NormalizedContinuation.selector Γ C d (1-ξ) R hfull H.selector)
    policy_measurable := DirectGame.measurable_selection C d ξ hξ hξ1 c
      (NormalizedContinuation.selector Γ C d (1-ξ) R hfull H.selector) }

def belief (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
    (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) :
    PosteriorSystem (game Γ C d ξ R hξ hξ1 hfull H) :=
  NormalizedContinuation.rebasePosterior Γ (game Γ C d ξ R hξ hξ1 hfull H) rfl
    (NormalizedContinuation.posterior Γ C d (1-ξ) R hfull H)

theorem joint_law (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
    (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) :
    (game Γ C d ξ R hξ hξ1 hfull H).F ⊗ₘ (game Γ C d ξ R hξ hξ1 hfull H).σ =
      Γ.F ⊗ₘ Γ.σ := rfl

theorem policy_high_factors (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
    (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) :
    HighFactors (game Γ C d ξ R hξ hξ1 hfull H) C d (1-ξ)
      (NormalizedContinuation.selector Γ C d (1-ξ) R hfull H.selector) := by
  intro j L hL z i hi
  exact DirectGame.selection_high_membership C d ξ hξ hξ1 c _ j L z i hL hi

theorem policy_low_membership (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
    (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) (j : Fin 2) (L : LocalList m) (z : unitInterval)
    (i : Fin m) (hL : CompatibleList C d (1-ξ) L) (hi : Information.tag C (L i) = 0) :
    i ∈ ((game Γ C d ξ R hξ hξ1 hfull H).policy j L z).val ↔
      i ∈ DirectGame.lowSelect C ξ hξ hξ1 c L z :=
  DirectGame.selection_low_membership C d ξ hξ hξ1 c _ j L z i hL hi

theorem belief_eq_original (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
    (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) (j : Fin 2) (L : LocalList m)
    (hL : L ∉ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j) :
    (belief Γ C d ξ R hξ hξ1 hfull H).posterior j L =
      (HigherPosterior.posterior Γ C d (1-ξ) R hfull).posterior j L := by
  simp only [belief, NormalizedContinuation.rebasePosterior,
    NormalizedContinuation.posterior, NormalizedContinuation.posteriorKernel,
    Kernel.piecewise_apply, if_neg hL]

theorem belief_eq_private_of_bad (Γ : FiniteGame m 2 c unitInterval)
    (C : Information.Classifier) (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) (j : Fin 2) (L : LocalList m)
    (hL : L ∈ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j) :
    (belief Γ C d ξ R hξ hξ1 hfull H).posterior j L =
      Measure.dirac (privateProfile j L) := by
  simp only [belief, NormalizedContinuation.rebasePosterior,
    NormalizedContinuation.posterior, NormalizedContinuation.posteriorKernel,
    Kernel.piecewise_apply, if_pos hL, NormalizedContinuation.privateKernel,
    Kernel.deterministic_apply]

theorem belief_eq_private_of_incompatible (Γ : FiniteGame m 2 c unitInterval)
    (C : Information.Classifier) (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) (j : Fin 2) (L : LocalList m)
    (hL : ¬ CompatibleList C d (1-ξ) L) :
    (belief Γ C d ξ R hξ hξ1 hfull H).posterior j L =
      Measure.dirac (privateProfile j L) := by
  by_cases hb : L ∈ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j
  · exact belief_eq_private_of_bad Γ C d ξ R hξ hξ1 hfull H j L hb
  · rw [belief_eq_original Γ C d ξ R hξ hξ1 hfull H j L hb]
    exact posterior_incompatible Γ C d (1-ξ) R hfull j L hL

end FCAppendix.Appendix08.GeneralLow.Implementation
