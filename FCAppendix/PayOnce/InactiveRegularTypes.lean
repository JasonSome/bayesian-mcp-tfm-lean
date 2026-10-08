import FCAppendix.PayOnce.InactivePureFirstOrder

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_ae_ne_entry_value
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∀ᵐ v ∂F, max (v-g) 0 ≠ Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ := by
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hatom : F {g+L}=0 := by
    have hh := h.positive_values_atomless 0 (g+L)
    rw [h.common_values 0,h.common_fee 0] at hh
    exact hh (by linarith)
  apply ae_iff.mpr
  apply measure_mono_null _ hatom
  intro v hv
  simp only [mem_setOf_eq,not_not] at hv
  have hw : 0 < v-g := by
    have hh : 0 < max (v-g) 0 := by rw [hv]; exact hL
    simpa only [lt_max_iff,lt_self_iff_false,or_false] using hh
  rw [max_eq_left hw.le] at hv
  simp only [mem_singleton_iff]
  linarith

theorem payOnce_inactive_ae_eventually_pure_first_order
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let Q := fun t => coverage (k+1) (C t) hn
      (Measure.pi fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    ∀ᵐ v ∂F, g < v → ∀ᶠ t in atTop, 0 < b t v ∧
      HasDerivAt (Q t) (deriv (Q t) (b t v)) (b t v) ∧
      Q t (b t v) = (v-g-b t v)*deriv (Q t) (b t v) := by
  dsimp only
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (payOnce_inactive_eventual_pure_first_order Γ B F g ρ h b heq)
  have hall := ae_all_iff.mpr (fun t => ae_all_iff.mpr (fun ht : T ≤ t => hT t ht))
  filter_upwards [hall] with v hv hvg
  filter_upwards [eventually_ge_atTop T] with t ht
  exact hv t ht hvg

end FCAppendix.Bayes
