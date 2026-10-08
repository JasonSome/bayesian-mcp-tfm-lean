import FCAppendix.Ample.BoundaryUsedRanks
import FCAppendix.Ample.ActualNormalizationCore

noncomputable section
namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators
open Ample Ample.CompletionDraft Ample.DownstreamNormalizationCore

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g : ℝ}

namespace FreeBaseBoundarySequence
variable (h : FreeBaseBoundarySequence M C Γ B F g)
include h

theorem normalization {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ActualNormalizationConclusion Γ g ell z := by
  have hr := h.common_rate hp
  have hzpos : 0 < z := he.1.trans_lt hz
  have hJ : 0 < -log (pi n) := neg_pos.mpr
    (Real.log_neg hr.broadcast_pos hr.broadcast_lt_one)
  apply actual_normalization_from_used_failure Γ F g ell z
    (h.eventually_finite_guards.mono (fun t ht => by omega))
    h.common_values h.common_fee h.ppi h.free h.users he hz
    (hr.deficit_rate z hzpos).1
  · exact positive_rate_scale_zero h.population_grows hJ (hr.deficit_rate z hzpos)
  · exact h.used_failure_small hp hzpos
  · exact h.acceptance.acceptance

end FreeBaseBoundarySequence
end FCAppendix.Bayes.CompletionDraft
