import FCAppendix.PayOnce.InactiveCentralValueBid

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def inactiveCentralLimit (F : Measure ℝ) (n : ℕ) (g ρ x : ℝ) : Fin 4 → ℝ :=
  let y := GaussianResponse.response x
  let a := (n:ℝ)*(2/(((n:ℝ)-1)*Limit.capRoot (F.map (fun v => max (v-g) 0)) n ρ))
  ![y,a*gaussianSuccessPrimitive y,a*gaussianSuccessPrimitive y,
    (x-y)*(a*gaussianSuccessPrimitive y)]

noncomputable def inactiveCentralObservables
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed) (hn : 2 ≤ k+1)
    (F : Measure ℝ) (g ρ : ℝ) (b : ℕ → ℝ → ℝ) (t : ℕ) (x : ℝ) : Fin 4 → ℝ :=
  let v := inactiveCentralValue M C F (k+1) g ρ x t
  let s := inactiveGaussianScale M F (k+1) g ρ t
  let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := coverage (k+1) (C t) hn μ (b t v)
  ![(b t v-inactiveValuePrice M C F (k+1) g t)/s,Q/s,
    (∫ r, ((k+1:ℕ):ℝ)*allocation (k+1) (C t) hn r (b t v) ∂μ)/s,
    (v-g-b t v)*Q/s^2]

theorem continuous_inactiveCentralLimit (F : Measure ℝ) (n : ℕ) (g ρ : ℝ) (j : Fin 4) :
    Continuous (fun x => inactiveCentralLimit F n g ρ x j) := by
  have hR := GaussianResponse.response_continuous
  have hT : Continuous gaussianSuccessPrimitive :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gaussianSuccessPrimitive x).continuousAt
  fin_cases j <;> dsimp only [inactiveCentralLimit] <;> fun_prop

theorem payOnce_inactive_central_profiles_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (hbound : ∀ t v, b t v ≤ max (v-g) 0)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar (k+1) (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) (max (v-g) 0))))
    (x : ℕ → ℝ) {x₀ : ℝ} (hx : Tendsto x atTop (𝓝 x₀))
    (hfoc : ∀ᶠ t in atTop,
      let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
      let Q := coverage (k+1) (C t) hn
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      let v := inactiveCentralValue M C F (k+1) g ρ (x t) t
      Q (b t v)=(v-g-b t v)*deriv Q (b t v)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ j : Fin 4, Tendsto (fun t => inactiveCentralObservables Γ hn F g ρ b t (x t) j)
      atTop (𝓝 (inactiveCentralLimit F (k+1) g ρ x₀ j)) := by
  dsimp only
  have hbid := payOnce_inactive_pure_value_center_bid_tendsto Γ B F g ρ h hlocal b hmono hbound hlim x hx hfoc
  have hxbar := payOnce_inactive_central_value_coordinate Γ B F g ρ h hlocal x hx
  have hy := payOnce_inactive_pure_bid_of_central_values Γ B F g ρ h hlocal b hmono hbound hlim _ hxbar hfoc
  have hq := payOnce_inactive_central_coverage_of_normalized_bid Γ B F g ρ h hlocal _ hy
  have hload := payOnce_inactive_central_test_mean_of_normalized_bid Γ B F g ρ h hlocal _ hy
    (fun p => ((k+1:ℕ):ℝ)*p) (measurable_const.mul measurable_id) (D := ((k+1:ℕ):ℝ))
    (fun p hp => by rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hp.1)]; nlinarith [hp.2])
    (d := ((k+1:ℕ):ℝ)) (K := 0) (by norm_num) (fun p _ => by simp)
  have hu := payOnce_inactive_central_utility_of_normalized_bid Γ B F g ρ h hlocal _ _ hxbar hy
  intro j
  fin_cases j
  · simpa [inactiveCentralObservables,inactiveCentralLimit] using hbid
  · simpa [inactiveCentralObservables,inactiveCentralLimit] using hq
  · simpa [inactiveCentralObservables,inactiveCentralLimit] using hload
  · simpa [inactiveCentralObservables,inactiveCentralLimit] using hu

theorem payOnce_inactive_central_profiles_uniform_of_foc
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (hbound : ∀ t v, b t v ≤ max (v-g) 0)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar (k+1) (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) (max (v-g) 0))))
    {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0<ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let Q := fun t => coverage (k+1) (C t) hn
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    ∀ᶠ t in atTop, ∀ x ∈ S,
      let v := inactiveCentralValue M C F (k+1) g ρ x t
      Q t (b t v)=(v-g-b t v)*deriv (Q t) (b t v) →
        ∀ j : Fin 4, |inactiveCentralObservables Γ hn F g ρ b t x j-
          inactiveCentralLimit F (k+1) g ρ x j| < ε := by
  dsimp only
  have hj (j : Fin 4) : ∀ᶠ t in atTop, ∀ x ∈ S,
      let v := inactiveCentralValue M C F (k+1) g ρ x t
      let Q := coverage (k+1) (C t) (by have := h.proposers_two; omega)
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      Q (b t v)=(v-g-b t v)*deriv Q (b t v) →
        |inactiveCentralObservables Γ (by have := h.proposers_two; omega) F g ρ b t x j-
          inactiveCentralLimit F (k+1) g ρ x j| < ε := by
    apply eventually_uniform_abs_lt_of_compact_admissible_sequences hS _ _ _
      (continuous_inactiveCentralLimit F (k+1) g ρ j).continuousOn ?_ hε
    intro φ hφ x x₀ _hx₀ _hxS hfoc hx
    exact payOnce_inactive_central_profiles_tendsto (fun t => Γ (φ t)) (fun t => B (φ t))
      F g ρ (h.along φ hφ) hlocal (fun t => b (φ t)) (fun t => hmono (φ t))
      (fun t v => hbound (φ t) v) (hlim.mono fun v hv => hv.comp hφ) x hx hfoc j
  filter_upwards [Filter.eventually_all.mpr hj] with t ht
  intro x hx hfoc j
  exact ht j x hx hfoc

end FCAppendix.Bayes
