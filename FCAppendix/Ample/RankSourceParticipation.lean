import FCAppendix.Ample.RankConditionalLaw
import FCAppendix.Ample.SlackParticipation

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)

theorem actual_rank_participation (F : Measure ℝ) (g : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g) (hn : 0 < n)
    (hguard : ∀ᶠ t in atTop, 0 < M t ∧ 0 < C t)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hpolicy : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j)
    (hu : ∀ t, UsersOptimal (Γ t))
    (hact : ∀ t, NonpositiveAbstention (Γ t))
    (hz : ∀ t, RejectsZeroBids (Γ t)) :
    (∀ᶠ t in atTop, positiveRouteMass (Γ t) (fun _ => True) = F.real (Ioi g)) ∧
    (∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      0 < x.2.routeCount → 0 < x.2.bid) ∧
    (∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      (0 < x.2.bid ∧ 0 < x.2.routeCount) ↔ (Γ t).g < x.1) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hguard] with t ht
    simpa only [hF t, hg t] using ppi_positiveParticipation_eq
      (Γ t) ht.1 hn ht.2 (hA t) (hatom t) (hpolicy t) (hu t) (hact t) (hz t)
  · filter_upwards [hguard] with t ht
    exact ppi_ae_routed_bid_pos (Γ t) ht.1 hn ht.2 (hA t) (hatom t)
      (hpolicy t) (hu t) (hact t) (hz t)
  · filter_upwards [hguard] with t ht
    exact ppi_ae_positive_draw_iff (Γ t) ht.1 hn ht.2 (hA t) (hatom t)
      (hpolicy t) (hu t) (hact t) (hz t)

end FCAppendix.Bayes
