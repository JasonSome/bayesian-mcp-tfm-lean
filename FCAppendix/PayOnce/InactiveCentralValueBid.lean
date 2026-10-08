import FCAppendix.PayOnce.InactiveCentralPureBids
import FCAppendix.PayOnce.InactiveCentralEvaluation
import FCAppendix.PayOnce.InactiveValuePriceCLT

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def inactiveCentralValue (M C : ℕ → ℕ) (F : Measure ℝ)
    (n : ℕ) (g ρ x : ℝ) (t : ℕ) : ℝ :=
  g+inactiveValuePrice M C F n g t+inactiveGaussianScale M F n g ρ t*x

theorem payOnce_inactive_central_value_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (x : ℕ → ℝ) {x₀ : ℝ} (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun t => inactiveCentralValue M C F (k+1) g ρ (x t) t-g) atTop
      (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) := by
  have hh := (payOnce_inactive_value_price Γ B F g ρ h).2.add
    ((inactiveGaussianScale_tendsto_zero M F (k+1) g ρ h.population_grows).mul hx)
  simp only [zero_mul,add_zero] at hh
  convert hh using 1
  funext t
  dsimp only [inactiveCentralValue]
  ring

theorem payOnce_inactive_central_value_coordinate
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (x : ℕ → ℝ) {x₀ : ℝ} (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun t => (inactiveCentralValue M C F (k+1) g ρ (x t) t-g-
      KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 x₀) := by
  have hh := hx.sub (payOnce_inactive_price_centering_normalized Γ B F g ρ h hlocal)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
  unfold inactiveCentralValue
  field_simp
  ring

theorem payOnce_inactive_pure_bid_of_central_values
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (hbound : ∀ t v, b t v ≤ max (v-g) 0)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar (k+1) (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) (max (v-g) 0))))
    (v : ℕ → ℝ) {x₀ : ℝ}
    (hx : Tendsto (fun t => (v t-g-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 x₀))
    (hfoc : ∀ᶠ t in atTop,
      let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
      let Q := coverage (k+1) (C t) hn
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      Q (b t (v t))=(v t-g-b t (v t))*deriv Q (b t (v t))) :
    Tendsto (fun t => (b t (v t)-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 (GaussianResponse.response x₀)) := by
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let x := fun t => (v t-g-bar t)/s t
  have hv : ∀ᶠ t in atTop, g+inactiveGaussianPrice Γ F g ρ (x t) t=v t := by
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    have hs : 0<s t := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
    change g+(bar t+s t*((v t-g-bar t)/s t))=v t
    rw [mul_div_cancel₀ _ hs.ne']
    ring
  have hfoc' : ∀ᶠ t in atTop,
      let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
      let Q := coverage (k+1) (C t) hn
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      let w := inactiveGaussianPrice Γ F g ρ (x t) t
      Q (b t (g+w))=(w-b t (g+w))*deriv Q (b t (g+w)) := by
    filter_upwards [hv,hfoc] with t ht hf
    dsimp only
    rw [ht]
    have hw : inactiveGaussianPrice Γ F g ρ (x t) t=v t-g := by linarith
    rwa [hw]
  have hh := payOnce_inactive_pure_central_bid_tendsto Γ B F g ρ h hlocal b hmono hbound hlim x hx hfoc'
  apply hh.congr'
  filter_upwards [hv] with t ht
  rw [ht]

theorem payOnce_inactive_pure_value_center_bid_tendsto
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
    Tendsto (fun t => (b t (inactiveCentralValue M C F (k+1) g ρ (x t) t)-
      inactiveValuePrice M C F (k+1) g t)/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 (GaussianResponse.response x₀)) := by
  have hb := payOnce_inactive_pure_bid_of_central_values Γ B F g ρ h hlocal b hmono hbound hlim _
    (payOnce_inactive_central_value_coordinate Γ B F g ρ h hlocal x hx) hfoc
  have hh := hb.add (payOnce_inactive_price_centering_normalized Γ B F g ρ h hlocal)
  simp only [add_zero] at hh
  apply hh.congr
  intro t
  ring

end FCAppendix.Bayes
