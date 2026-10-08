import FCAppendix.Ample.SlackLoad
import FCAppendix.Ample.SlackFiniteService

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure StrictSlack {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (ρ a₁ a₂ η : ℝ) : Prop where
  singleton_pos : 0 < a₁
  multiroute_pos : 0 < a₂
  margin_pos : 0 < η
  eventual : ∀ᶠ t in atTop,
    a₁ ≤ ((Γ t).F ⊗ₘ (Γ t).σ).real {x | x.2.routeCount = 1} ∧
    a₂ ≤ ((Γ t).F ⊗ₘ (Γ t).σ).real {x | 2 ≤ x.2.routeCount} ∧
    a₁ ≤ positiveRouteMass (Γ t) (fun k => k = 1) ∧
    a₂ ≤ positiveRouteMass (Γ t) (fun k => 2 ≤ k) ∧
    submittedMarginal (Γ t) ≤ ρ - η

namespace FreeBaseAmpleSequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g ρ : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g ρ)
include h

theorem strict_slack :
    ∃ a₁ a₂ η : ℝ, StrictSlack Γ ρ a₁ a₂ η := by
  obtain ⟨a₁, ha₁, h₁⟩ := h.singleton_floor
  obtain ⟨a₂, ha₂, h₂⟩ := h.multiroute_floor
  obtain ⟨η, hη, hηevent⟩ := h.strict_submitted_margin
  refine ⟨a₁, a₂, η, ha₁, ha₂, hη, ?_⟩
  filter_upwards [h.eventually_finite_guards, h₁, h₂, hηevent]
    with t ht ht₁ ht₂ htη
  have hraw₁ := ppi_positiveRouteMass_eq_raw (Γ t) (by omega) h.proposers_pos ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t) (h.users t)
    (h.abstention t) (h.reject_zero t) (fun k => k = 1) (by intro k hk; omega)
  have hraw₂ := ppi_positiveRouteMass_eq_raw (Γ t) (by omega) h.proposers_pos ht.2.1
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t) (h.users t)
    (h.abstention t) (h.reject_zero t) (fun k => 2 ≤ k) (by intro k hk; omega)
  exact ⟨by simpa only [hraw₁] using ht₁,
    by simpa only [hraw₂] using ht₂, ht₁, ht₂, htη⟩

theorem uniform_exponential :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ t in atTop, ∀ i : Fin (M t),
      (∀ a : JointAction n, 0 < a.bid →
        ((problem (Γ t) i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
          n * exp (-κ * M t)) ∧
      (∀ w : ℝ, 0 < w → ∀ a : JointAction n,
        (problem (Γ t) i).BestResponse (w + (Γ t).g) a →
          a.bid ≤ 2 * w * exp (-κ * M t)) := by
  obtain ⟨η, hη, hmarg⟩ := h.strict_submitted_margin
  obtain ⟨κ, hκ, he⟩ := ppi_source_exponential_of_margin Γ h.proposers_pos
    h.population_grows h.capacity_ratio hη hmarg h.ppi h.free
    h.visible_atomless h.feasible_continuations
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [he] with t ht
  intro i
  exact ⟨(ht i).2.2.1, fun w hw a ha => ((ht i).2.2.2 w hw a ha).2⟩

theorem ample_slack :
    ∃ a₁ a₂ η κ : ℝ, StrictSlack Γ ρ a₁ a₂ η ∧ 0 < κ ∧
      ∀ᶠ t in atTop, ∀ i : Fin (M t),
        (∀ a : JointAction n, 0 < a.bid →
          ((problem (Γ t) i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
            n * exp (-κ * M t)) ∧
        (∀ w : ℝ, 0 < w → ∀ a : JointAction n,
          (problem (Γ t) i).BestResponse (w + (Γ t).g) a →
            a.bid ≤ 2 * w * exp (-κ * M t)) := by
  obtain ⟨a₁, a₂, η, hs⟩ := h.strict_slack
  obtain ⟨κ, hκ, he⟩ := h.uniform_exponential
  exact ⟨a₁, a₂, η, κ, hs, hκ, he⟩

end FreeBaseAmpleSequence

theorem ample_slack_bayes
    (M C : ℕ → ℕ) (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) (g ρ : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hFatom : ∀ v : ℝ, F {v} = 0)
    (hM : Tendsto M atTop atTop)
    (hC : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 ρ))
    (ham : F.real (Ioi g) < (n : ℝ) * ρ) (hint : ρ < F.real (Ioi g))
    (hu : ∀ t, UsersOptimal (Γ t))
    (hB : ∀ t, BayesReceiptOptimalOnPath (Γ t) (B t))
    (hj : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j)
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hfree : ∀ t, FreeDuplicateBase (Γ t))
    (hact : ∀ t, NonpositiveAbstention (Γ t))
    (hz : ∀ t, RejectsZeroBids (Γ t)) :
    ∃ a₁ a₂ η κ : ℝ, StrictSlack Γ ρ a₁ a₂ η ∧ 0 < κ ∧
      ∀ᶠ t in atTop, ∀ i : Fin (M t),
        (∀ a : JointAction n, 0 < a.bid →
          ((problem (Γ t) i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
            n * exp (-κ * M t)) ∧
        (∀ w : ℝ, 0 < w → ∀ a : JointAction n,
          (problem (Γ t) i).BestResponse (w + (Γ t).g) a →
            a.bid ≤ 2 * w * exp (-κ * M t)) := by
  let h : FreeBaseAmpleSequence M C Γ B F g ρ :=
    ⟨hF, hg, hFatom, hM, hC, ham, hint, hu, hB, hj, hatom, hA, hfree, hact, hz⟩
  exact h.ample_slack

end FCAppendix.Bayes
