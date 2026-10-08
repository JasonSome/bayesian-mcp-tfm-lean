import FCAppendix.PayOnce.InactiveCentralHypotheticalUniform
import FCAppendix.Probability.CompactShiftUniform

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def inactiveActualCentralAtCenter
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (F : Measure ℝ) (g ρ : ℝ) (b : ℕ → ℝ → ℝ) (c : ℕ → ℝ)
    (t : ℕ) (i : Fin (M t)) (x : ℝ) : Fin 4 → ℝ :=
  let s := inactiveGaussianScale M F (k+1) g ρ t
  let v := g+c t+s*x
  ![(b t v-c t)/s,(typeOutcome (Γ t) i v).success/s,
    (typeOutcome (Γ t) i v).load/s,(problem (Γ t) i).envelope v/s^2]

noncomputable def inactiveHypotheticalCentralAtCenter
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (F : Measure ℝ) (g ρ : ℝ) (c : ℕ → ℝ)
    (t : ℕ) (i : Fin (M t)) (a : JointAction (k+1)) (x : ℝ) : Fin 3 → ℝ :=
  let s := inactiveGaussianScale M F (k+1) g ρ t
  ![(a.bid-c t)/s,((problem (Γ t) i).outcome a).success/s,
    (problem (Γ t) i).envelope (g+c t+s*x)/s^2]

theorem inactiveCentralValue_shift (F : Measure ℝ) (g ρ : ℝ) (c : ℕ → ℝ)
    (t : ℕ) (x : ℝ) (hs : inactiveGaussianScale M F (k+1) g ρ t ≠ 0) :
    inactiveCentralValue M C F (k+1) g ρ
      (x+(c t-inactiveValuePrice M C F (k+1) g t)/inactiveGaussianScale M F (k+1) g ρ t) t =
        g+c t+inactiveGaussianScale M F (k+1) g ρ t*x := by
  unfold inactiveCentralValue
  field_simp [hs]
  ring

theorem payOnce_inactive_central_recentered_regular_profiles
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
        (∀ᶠ t in atTop, ∀ v ∈ A, g < v → InactiveCentralRegular Γ hn g b t v) ∧
        ∀ c : ℕ → ℝ,
          Tendsto (fun t => (c t-inactiveValuePrice M C F (k+1) g t)/
            inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0) →
          ∀ S : Set ℝ, IsCompact S → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ t in atTop, ∀ x ∈ S,
              g+c t+inactiveGaussianScale M F (k+1) g ρ t*x ∈ A → ∀ i : Fin (M t),
                ∀ j : Fin 4, |inactiveActualCentralAtCenter Γ F g ρ b c t i x j-
                  inactiveCentralLimit F (k+1) g ρ x j| < ε := by
  dsimp only
  obtain ⟨b,hm,hme,hbound,heq,A,hA,hreg,hprof⟩ :=
    payOnce_inactive_central_regular_profiles Γ B F g ρ h hlocal
  refine ⟨b,hm,hme,hbound,heq,A,hA,hreg,?_⟩
  intro c hc S hS ε hε
  let δ := fun t => (c t-inactiveValuePrice M C F (k+1) g t)/inactiveGaussianScale M F (k+1) g ρ t
  have hj (j : Fin 4) : ∀ᶠ t in atTop, ∀ x ∈ S,
      ∀ i : Fin (M t), inactiveCentralValue M C F (k+1) g ρ (x+δ t) t ∈ A →
      |inactiveActualCentralObservables Γ F g ρ b t i (x+δ t) j+
        (if j=0 then -δ t else 0)-inactiveCentralLimit F (k+1) g ρ x j| < ε := by
    apply eventually_uniform_shifted_abs_lt (β := fun t => Fin (M t))
      (fun t x i => inactiveActualCentralObservables Γ F g ρ b t i x j)
      (fun x => inactiveCentralLimit F (k+1) g ρ x j)
      (fun t x _ => inactiveCentralValue M C F (k+1) g ρ x t ∈ A)
      (continuous_inactiveCentralLimit F (k+1) g ρ j) ?_ δ _ hc ?_ hS hε
    · intro K hK e he
      filter_upwards [hprof K hK e he] with t ht x hx i hAx
      exact (ht x hx hAx i).2 j
    · split_ifs
      · simpa using hc.neg
      · exact tendsto_const_nhds
  filter_upwards [Filter.eventually_all.mpr hj,h.population_grows.eventually_gt_atTop 0] with t ht hmt
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt
  intro x hx hAx i j
  have hv := inactiveCentralValue_shift (M := M) (C := C) (k := k) F g ρ c t x hs.ne'
  change inactiveCentralValue M C F (k+1) g ρ (x+δ t) t =
    g+c t+inactiveGaussianScale M F (k+1) g ρ t*x at hv
  have hz := ht j x hx i (by simpa only [hv] using hAx)
  have he : inactiveActualCentralObservables Γ F g ρ b t i (x+δ t) j+
      (if j=0 then -δ t else 0)=inactiveActualCentralAtCenter Γ F g ρ b c t i x j := by
    fin_cases j
    · simp [inactiveActualCentralObservables,inactiveActualCentralAtCenter,hv]
      dsimp only [δ]
      ring
    · simp [inactiveActualCentralObservables,inactiveActualCentralAtCenter,hv]
    · simp [inactiveActualCentralObservables,inactiveActualCentralAtCenter,hv]
    · simp [inactiveActualCentralObservables,inactiveActualCentralAtCenter,hv]
  rwa [he] at hz

theorem payOnce_inactive_central_recentered_hypothetical_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (c : ℕ → ℝ)
    (hc : Tendsto (fun t => (c t-inactiveValuePrice M C F (k+1) g t)/
      inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0))
    {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ x ∈ S, ∀ i : Fin (M t), ∀ a : JointAction (k+1),
      (problem (Γ t) i).BestResponse (g+c t+inactiveGaussianScale M F (k+1) g ρ t*x) a →
        ∀ j : Fin 3, |inactiveHypotheticalCentralAtCenter Γ F g ρ c t i a x j-
          inactiveHypotheticalCentralLimit F (k+1) g ρ x j| < ε := by
  let δ := fun t => (c t-inactiveValuePrice M C F (k+1) g t)/inactiveGaussianScale M F (k+1) g ρ t
  have hj (j : Fin 3) : ∀ᶠ t in atTop, ∀ x ∈ S,
      ∀ z : Fin (M t) × JointAction (k+1),
      (problem (Γ t) z.1).BestResponse (inactiveCentralValue M C F (k+1) g ρ (x+δ t) t) z.2 →
      |inactiveHypotheticalCentralObservables Γ F g ρ t z.1 z.2 (x+δ t) j+
        (if j=0 then -δ t else 0)-inactiveHypotheticalCentralLimit F (k+1) g ρ x j| < ε := by
    apply eventually_uniform_shifted_abs_lt (β := fun t => Fin (M t) × JointAction (k+1))
      (fun t x z => inactiveHypotheticalCentralObservables Γ F g ρ t z.1 z.2 x j)
      (fun x => inactiveHypotheticalCentralLimit F (k+1) g ρ x j)
      (fun t x z => (problem (Γ t) z.1).BestResponse (inactiveCentralValue M C F (k+1) g ρ x t) z.2)
      (continuous_inactiveHypotheticalCentralLimit F (k+1) g ρ j) ?_ δ _ hc ?_ hS hε
    · intro K hK e he
      filter_upwards [payOnce_inactive_central_hypothetical_uniform Γ B F g ρ h hlocal hK he] with t ht x hx z ha
      exact ht x hx z.1 z.2 ha j
    · split_ifs
      · simpa using hc.neg
      · exact tendsto_const_nhds
  filter_upwards [Filter.eventually_all.mpr hj,h.population_grows.eventually_gt_atTop 0] with t ht hmt
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt
  intro x hx i a ha j
  have hv := inactiveCentralValue_shift (M := M) (C := C) (k := k) F g ρ c t x hs.ne'
  change inactiveCentralValue M C F (k+1) g ρ (x+δ t) t =
    g+c t+inactiveGaussianScale M F (k+1) g ρ t*x at hv
  have hz := ht j x hx (i,a) (by simpa only [hv] using ha)
  have he : inactiveHypotheticalCentralObservables Γ F g ρ t i a (x+δ t) j+
      (if j=0 then -δ t else 0)=inactiveHypotheticalCentralAtCenter Γ F g ρ c t i a x j := by
    fin_cases j
    · simp [inactiveHypotheticalCentralObservables,inactiveHypotheticalCentralAtCenter]
      dsimp only [δ]
      ring
    · simp [inactiveHypotheticalCentralObservables,inactiveHypotheticalCentralAtCenter]
    · simp [inactiveHypotheticalCentralObservables,inactiveHypotheticalCentralAtCenter,hv]
  rwa [he] at hz

theorem payOnce_inactive_central_limit_center_shift
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (hcapacity : (fun t => (C t:ℝ)/(M t)-ρ) =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2))) :
    Tendsto (fun t => (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ-
      inactiveValuePrice M C F (k+1) g t)/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 0) := by
  have hh := (payOnce_inactive_price_centering_normalized Γ B F g ρ h hlocal).sub
    (payOnce_inactive_price_limit_centering_normalized Γ B F g ρ h hlocal hcapacity)
  simp only [sub_zero] at hh
  convert hh using 1
  funext t
  ring

end FCAppendix.Bayes
