import FCAppendix.PayOnce.InactiveCentralProfiles
import FCAppendix.PayOnce.InactiveCentralRegularSet

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def inactiveActualCentralObservables
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (F : Measure ℝ) (g ρ : ℝ) (b : ℕ → ℝ → ℝ) (t : ℕ) (i : Fin (M t)) (x : ℝ) : Fin 4 → ℝ :=
  let v := inactiveCentralValue M C F (k+1) g ρ x t
  let s := inactiveGaussianScale M F (k+1) g ρ t
  ![(b t v-inactiveValuePrice M C F (k+1) g t)/s,
    (typeOutcome (Γ t) i v).success/s,(typeOutcome (Γ t) i v).load/s,
    (problem (Γ t) i).envelope v/s^2]

theorem payOnce_inactive_central_window_positive
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    {S : Set ℝ} (hS : IsCompact S) :
    ∀ᶠ t in atTop, ∀ x ∈ S, g < inactiveCentralValue M C F (k+1) g ρ x t := by
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hL : 0<L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hh := eventually_uniform_abs_lt_of_compact_sequences hS
    (fun t x => inactiveCentralValue M C F (k+1) g ρ x t-g) (fun _ => L)
    continuousOn_const (fun φ hφ x _ _ _ hx =>
      payOnce_inactive_central_value_tendsto (fun t => Γ (φ t)) (fun t => B (φ t))
        F g ρ (h.along φ hφ) x hx) (half_pos hL)
  filter_upwards [hh] with t ht x hx
  have hlo := (abs_lt.mp (ht x hx)).1
  linarith

theorem inactiveActualCentralObservables_eq
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed) (hn : 2 ≤ k+1)
    (F : Measure ℝ) (g ρ : ℝ) (b : ℕ → ℝ → ℝ) (t : ℕ) (x : ℝ)
    (hreg : InactiveCentralRegular Γ hn g b t (inactiveCentralValue M C F (k+1) g ρ x t))
    (i : Fin (M t)) :
    inactiveActualCentralObservables Γ F g ρ b t i x=inactiveCentralObservables Γ hn F g ρ b t x := by
  funext j
  have hs := (hreg.2 i).1
  have hm := (hreg.2 i).2.1
  have hu := (hreg.2 i).2.2.1
  fin_cases j
  · rfl
  · simp [inactiveActualCentralObservables,inactiveCentralObservables,hs]
  · simp [inactiveActualCentralObservables,inactiveCentralObservables,hm]
  · simp [inactiveActualCentralObservables,inactiveCentralObservables,hu]

theorem payOnce_inactive_central_regular_profiles
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
      (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
      (∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2=b t z.1) ∧
      ∃ A : Set ℝ, (∀ᵐ v ∂F, v ∈ A) ∧
        (∀ᶠ t in atTop, ∀ v ∈ A, g<v → InactiveCentralRegular Γ hn g b t v) ∧
        ∀ S : Set ℝ, IsCompact S → ∀ ε : ℝ, 0<ε →
          ∀ᶠ t in atTop, ∀ x ∈ S,
            inactiveCentralValue M C F (k+1) g ρ x t ∈ A → ∀ i : Fin (M t),
              (∀ᵐ a ∂(Γ t).σ (inactiveCentralValue M C F (k+1) g ρ x t),
                a.bid=b t (inactiveCentralValue M C F (k+1) g ρ x t) ∧ a.routeCount=k+1) ∧
              ∀ j : Fin 4, |inactiveActualCentralObservables Γ F g ρ b t i x j-
                inactiveCentralLimit F (k+1) g ρ x j| < ε := by
  dsimp only
  obtain ⟨_hL,_hD,b,hmono,hmeas,hbound,heq,hlim⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  obtain ⟨A,hA,hregular⟩ := payOnce_inactive_central_regular_set Γ B F g ρ h b heq
  refine ⟨b,hmono,hmeas,hbound,heq,A,hA,hregular,?_⟩
  intro S hS ε hε
  filter_upwards [payOnce_inactive_central_profiles_uniform_of_foc Γ B F g ρ h hlocal
    b hmono (fun t v => (hbound t v).2) hlim hS hε,hregular,
    payOnce_inactive_central_window_positive Γ B F g ρ h hS] with t ht hr hp
  intro x hx hxA i
  have hreg := hr _ hxA (hp x hx)
  refine ⟨(hreg.2 i).2.2.2,?_⟩
  intro j
  rw [inactiveActualCentralObservables_eq Γ _ F g ρ b t x hreg i]
  exact ht x hx hreg.1 j

end FCAppendix.Bayes
