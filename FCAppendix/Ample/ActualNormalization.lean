import FCAppendix.Ample.UsedBidRanks
import FCAppendix.Ample.ActualNormalizationCore
import FCAppendix.Ample.ActualServiceTransfer

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

namespace FreeBaseAmpleSequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g rho : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g rho)
include h

theorem actual_uniform_acceptance :
    ∀ eps > 0, ∀ᶠ t in atTop, ∀ᵐ x ∂activeDrawLaw (Γ t),
      0 < x.2.routeCount →
        |actualMeanLoad (Γ t) x.2 / (x.2.routeCount : ℝ) - 1| ≤ eps := by
  obtain ⟨kappa, hkappa, hcopy⟩ := h.uniform_exponential
  have he : Tendsto (fun t => (n : ℝ) * exp (-kappa * M t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (exp_neg_population_tendsto_zero h.population_grows hkappa).const_mul (n : ℝ)
  have hnonneg : ∀ᶠ t in atTop, 0 ≤ (n : ℝ) * exp (-kappa * M t) :=
    Filter.Eventually.of_forall (fun t => mul_nonneg (Nat.cast_nonneg n) (exp_pos _).le)
  have hjoint := h.joint_copy_error_of_positive_copy_bound _ hnonneg
    (hcopy.mono (fun t ht i => (ht i).1))
  apply active_uniform_acceptance_of_joint_copy_error Γ
    (h.eventually_finite_guards.mono (fun t ht => by omega))
    (fun t => (n : ℝ) * exp (-kappa * M t)) he hjoint

theorem normalization_of_route_limit {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ActualNormalizationConclusion Γ g ell z := by
  obtain ⟨J, hc⟩ := h.common_rate_of_route_limit hp
  have hzpos : 0 < z := he.1.trans_lt hz
  have hrate := hc.deficit_rate z hzpos
  apply actual_normalization_from_used_failure Γ F g ell z
    (h.eventually_finite_guards.mono (fun t ht => by omega))
    h.common_values h.common_fee h.ppi h.free h.users he hz hrate.1
  · exact positive_rate_scale_zero h.population_grows hc.rate_pos hrate
  · exact h.used_failure_small_of_route_limit hp hzpos
  · exact h.actual_uniform_acceptance

end FreeBaseAmpleSequence
end FCAppendix.Bayes
