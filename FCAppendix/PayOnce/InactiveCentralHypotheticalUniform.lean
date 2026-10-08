import FCAppendix.PayOnce.InactiveCentralHypothetical

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def inactiveHypotheticalCentralObservables
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (F : Measure ℝ) (g ρ : ℝ) (t : ℕ) (i : Fin (M t)) (a : JointAction (k+1)) (x : ℝ) : Fin 3 → ℝ :=
  let s := inactiveGaussianScale M F (k+1) g ρ t
  ![(a.bid-inactiveValuePrice M C F (k+1) g t)/s,
    ((problem (Γ t) i).outcome a).success/s,
    (problem (Γ t) i).envelope (inactiveCentralValue M C F (k+1) g ρ x t)/s^2]

noncomputable def inactiveHypotheticalCentralLimit (F : Measure ℝ) (n : ℕ) (g ρ x : ℝ) : Fin 3 → ℝ :=
  ![inactiveCentralLimit F n g ρ x 0,inactiveCentralLimit F n g ρ x 1,
    inactiveCentralLimit F n g ρ x 3]

theorem continuous_inactiveHypotheticalCentralLimit (F : Measure ℝ) (n : ℕ) (g ρ : ℝ) (j : Fin 3) :
    Continuous (fun x => inactiveHypotheticalCentralLimit F n g ρ x j) := by
  fin_cases j <;> dsimp only [inactiveHypotheticalCentralLimit]
  · exact continuous_inactiveCentralLimit F n g ρ 0
  · exact continuous_inactiveCentralLimit F n g ρ 1
  · exact continuous_inactiveCentralLimit F n g ρ 3

theorem payOnce_inactive_central_hypothetical_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ x ∈ S, ∀ i : Fin (M t), ∀ a : JointAction (k+1),
      (problem (Γ t) i).BestResponse (inactiveCentralValue M C F (k+1) g ρ x t) a →
        ∀ j : Fin 3, |inactiveHypotheticalCentralObservables Γ F g ρ t i a x j-
          inactiveHypotheticalCentralLimit F (k+1) g ρ x j| < ε := by
  have hj (j : Fin 3) : ∀ᶠ t in atTop, ∀ x ∈ S,
      ∀ z : Fin (M t) × JointAction (k+1),
        (problem (Γ t) z.1).BestResponse (inactiveCentralValue M C F (k+1) g ρ x t) z.2 →
          |inactiveHypotheticalCentralObservables Γ F g ρ t z.1 z.2 x j-
            inactiveHypotheticalCentralLimit F (k+1) g ρ x j| < ε := by
    apply eventually_uniform_abs_lt_of_compact_labeled_sequences hS _ _ _
      (continuous_inactiveHypotheticalCentralLimit F (k+1) g ρ j).continuousOn ?_ hε
    intro φ hφ x x₀ _hx₀ _hxS z ha hx
    have hb := payOnce_inactive_central_hypothetical_bid (fun t => Γ (φ t)) (fun t => B (φ t))
      F g ρ (h.along φ hφ) hlocal x hx (fun t => (z t).1) (fun t => (z t).2) ha
    have hsu := payOnce_inactive_central_hypothetical_success_utility
      (fun t => Γ (φ t)) (fun t => B (φ t)) F g ρ (h.along φ hφ) hlocal x hx
      (fun t => (z t).1) (fun t => (z t).2) ha
    fin_cases j
    · simpa [inactiveHypotheticalCentralObservables,inactiveHypotheticalCentralLimit,
        inactiveCentralLimit,inactiveValuePrice,inactiveGaussianScale] using hb
    · simpa [inactiveHypotheticalCentralObservables,inactiveHypotheticalCentralLimit,inactiveGaussianScale] using hsu.1
    · simpa [inactiveHypotheticalCentralObservables,inactiveHypotheticalCentralLimit,inactiveCentralValue,inactiveValuePrice,inactiveGaussianScale] using hsu.2
  filter_upwards [Filter.eventually_all.mpr hj] with t ht x hx i a ha j
  exact ht j x hx (i,a) ha

end FCAppendix.Bayes
