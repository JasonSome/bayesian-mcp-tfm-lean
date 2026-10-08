import FCAppendix.PayOnce.InactiveCentralFOC
import FCAppendix.PayOnce.CentralBidLocalization
import FCAppendix.PayOnce.InactivePureFirstOrder

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_pure_central_bid_tendsto
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
      let w := inactiveGaussianPrice Γ F g ρ (x t) t
      Q (b t (g+w))=(w-b t (g+w))*deriv Q (b t (g+w))) :
    Tendsto (fun t => (b t (g+inactiveGaussianPrice Γ F g ρ (x t) t)-
      KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 (GaussianResponse.response x₀)) := by
  let w := fun t => inactiveGaussianPrice Γ F g ρ (x t) t
  let v := fun t => g+w t
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hw : Tendsto w atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :=
    payOnce_inactive_gaussian_bid_tendsto Γ B F g ρ h x hx
  have hv : Tendsto (fun t => v t-g) atTop
      (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) := by
    simpa only [v,add_sub_cancel_left] using hw
  have hb := monotone_entry_bid_tendsto F hL hlocal b hmono hbound hlim v hv
  apply payOnce_inactive_central_foc_bid_limit Γ B F g ρ h hlocal x (fun t => b t (v t)) hx hb ?_ hfoc
  filter_upwards [hw.eventually_const_lt hL] with t ht
  simpa only [v,add_sub_cancel_left,max_eq_left ht.le] using hbound t (v t)

theorem payOnce_inactive_pure_central_bid_uniform_of_foc
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
      let w := inactiveGaussianPrice Γ F g ρ x t
      Q t (b t (g+w))=(w-b t (g+w))*deriv (Q t) (b t (g+w)) →
        |(b t (g+w)-KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
          ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t-GaussianResponse.response x| < ε := by
  dsimp only
  apply eventually_uniform_abs_lt_of_compact_admissible_sequences hS _ _ _
    GaussianResponse.response_continuous.continuousOn ?_ hε
  intro φ hφ x x₀ _hx₀ _hxS hfoc hx
  exact payOnce_inactive_pure_central_bid_tendsto (fun t => Γ (φ t)) (fun t => B (φ t))
    F g ρ (h.along φ hφ) hlocal (fun t => b (φ t)) (fun t => hmono (φ t))
    (fun t v => hbound (φ t) v) (hlim.mono fun v hv => hv.comp hφ) x hx hfoc

theorem payOnce_inactive_pure_central_bid_profile
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (hbound : ∀ t v, b t v ≤ max (v-g) 0)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2=b t z.1)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar (k+1) (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) (max (v-g) 0)))) :
    ∃ A : Set ℝ, (∀ᵐ v ∂F, v ∈ A) ∧ ∀ S : Set ℝ, IsCompact S → ∀ ε : ℝ, 0<ε →
      ∀ᶠ t in atTop, ∀ v ∈ A, g<v →
        (v-g-KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
          inactiveGaussianScale M F (k+1) g ρ t ∈ S →
        |(b t v-KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
          inactiveGaussianScale M F (k+1) g ρ t-
          GaussianResponse.response ((v-g-KernelDemand.populationPrice (k+1)
            (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)| < ε := by
  have hfoc := payOnce_inactive_eventual_pure_first_order Γ B F g ρ h b heq
  obtain ⟨T,hT⟩ := eventually_atTop.mp hfoc
  let A := {v | ∀ t, T≤t → g<v →
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let Q := coverage (k+1) (C t) hn
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    Q (b t v)=(v-g-b t v)*deriv Q (b t v)}
  have hA : ∀ᵐ v ∂F, v ∈ A := by
    apply ae_all_iff.mpr
    intro t
    apply ae_all_iff.mpr
    intro ht
    exact (hT t ht).mono fun v hv hvg => (hv hvg).2.2
  refine ⟨A,hA,?_⟩
  intro S hS ε hε
  filter_upwards [payOnce_inactive_pure_central_bid_uniform_of_foc Γ B F g ρ h hlocal
    b hmono hbound hlim hS hε,eventually_ge_atTop T,h.population_grows.eventually_gt_atTop 0]
    with t ht hTt hmt
  intro v hv hvg hx
  let bar := KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ t
  let x := (v-g-bar)/s
  have hs : 0<s := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt
  have hw : inactiveGaussianPrice Γ F g ρ x t=v-g := by
    change bar+s*((v-g-bar)/s)=v-g
    rw [mul_div_cancel₀ _ hs.ne',add_sub_cancel]
  have hv' : g+inactiveGaussianPrice Γ F g ρ x t=v := by rw [hw]; ring
  have hh := ht x hx
  dsimp only at hh
  rw [hv',hw] at hh
  exact hh (hv t hTt hvg)

end FCAppendix.Bayes
