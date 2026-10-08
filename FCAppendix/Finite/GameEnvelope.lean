import FCAppendix.Finite.EnvelopeIntegral
import FCAppendix.Game.Bayesian

namespace FCAppendix
namespace Bayes

open MeasureTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem supported_success_subgradient (Γ : FiniteGame m n c Seed) (hΓ : UsersOptimal Γ)
    (i : Fin m) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂(Γ.σ v), ∀ w,
      (problem Γ i).envelope v + (w - v) * ((problem Γ i).outcome a).success ≤
        (problem Γ i).envelope w := by
  filter_upwards [hΓ i] with v hv
  filter_upwards [hv] with a ha
  exact (problem Γ i).supporting_line v a ha

theorem supported_success_monotone (Γ : FiniteGame m n c Seed) (hΓ : UsersOptimal Γ)
    (i : Fin m) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ w ∂Γ.F, v < w → ∀ᵐ a ∂(Γ.σ v), ∀ᵐ b ∂(Γ.σ w),
      ((problem Γ i).outcome a).success ≤ ((problem Γ i).outcome b).success := by
  filter_upwards [hΓ i] with v hv
  filter_upwards [hΓ i] with w hw hvw
  filter_upwards [hv] with a ha
  filter_upwards [hw] with b hb
  exact (problem Γ i).success_order v w hvw a b ha hb

end Bayes
end FCAppendix
