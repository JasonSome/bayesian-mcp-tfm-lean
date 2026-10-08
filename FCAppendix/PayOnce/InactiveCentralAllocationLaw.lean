import FCAppendix.PayOnce.InactiveCentralLinearization
import FCAppendix.Probability.L1WeakConvergence

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_clipped_focal_price_tendstoInDistribution
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u)
    (b : ℕ → ℝ) (hb : ∀ᶠ t in atTop, 0 < b t) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    TendstoInDistribution (fun t r =>
      (clippedFocalPrice (k+1) (C t) hn ell u (b t) r-bar t)/
        inactiveGaussianScale M F (k+1) g ρ t) atTop id
      (fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      (gaussianReal 0 1) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  refine ⟨fun t => (((measurable_clippedFocalPrice hn ell u (b t)).sub_const _).div_const _).aemeasurable,
    aemeasurable_id,?_⟩
  apply probabilityMeasure_tendsto_of_cdf
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [payOnce_inactive_clipped_focal_price_gaussian_uniform_population
    Γ B F g ρ h hlocal ell u hell hu x ε hε,hb] with t ht hbt
  simpa only [ProbabilityMeasure.coe_mk,Measure.map_id,Real.dist_eq] using ht (b t) hbt

theorem payOnce_inactive_central_allocation_tendstoInDistribution
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let s := inactiveGaussianScale M F (k+1) g ρ
    TendstoInDistribution (fun t r => allocation (k+1) (C t) hn r (bar t+s t*y t)/s t)
      atTop (fun Z => (2/((((k+1:ℕ):ℝ)-1)*L))*max (z-Z) 0)
      (fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      (gaussianReal 0 1) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let b := fun t => bar t+s t*y t
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let X := fun t => clippedFocalPrice (N := M t-1) (k+1) (C t) hn (3*L/4) (5*L/4) (b t)
  let W := fun t r => (X t r-bar t)/s t
  let α := 2/((((k+1:ℕ):ℝ)-1)*L)
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hb : ∀ᶠ t in atTop, 0 < b t :=
    (payOnce_inactive_gaussian_bid_tendsto Γ B F g ρ h y hy).eventually_const_lt hL
  have hW t : Measurable (W t) :=
    ((measurable_clippedFocalPrice hn _ _ (b t)).sub_const (bar t)).div_const (s t)
  have hweak : TendstoInDistribution W atTop id μ (gaussianReal 0 1) :=
    payOnce_inactive_clipped_focal_price_tendstoInDistribution Γ B F g ρ h hlocal
      (3*L/4) (5*L/4) (by linarith) (by linarith) b hb
  have hp t : Measurable (fun r : Fin (M t-1) → ℝ => allocation (k+1) (C t) hn r (b t)/s t) :=
    (measurable_allocation_fixed_bid hn (b t)).div_const (s t)
  apply tendstoInDistribution_of_integral_abs_sub μ (gaussianReal 0 1) _
    (fun t r => α*max (y t-W t r) 0) _ hp
    (tendstoInDistribution_positivePart_moving μ (gaussianReal 0 1) W id hW hweak y hy α) ?_
    (payOnce_inactive_central_allocation_linearization Γ B F g ρ h hlocal y hy)
  intro t
  have hXi : Integrable (X t) (μ t) :=
    (memLp_of_bounded (.of_forall fun r => clipToInterval_mem (by linarith : 3*L/4 ≤ 5*L/4) _)
      (measurable_clippedFocalPrice hn _ _ (b t)).aestronglyMeasurable 2).integrable (by norm_num)
  have hpi : Integrable (fun r : Fin (M t-1) → ℝ => allocation (k+1) (C t) hn r (b t)/s t) (μ t) :=
    (UnitInterval.integrable _ _ (measurable_allocation_fixed_bid hn (b t))
      (fun r => (allocation_bounds hn r (b t)).1)
      (fun r => (allocation_bounds hn r (b t)).2)).div_const (s t)
  exact (hpi.sub ((((integrable_const (y t)).sub
    ((hXi.sub (integrable_const (bar t))).div_const (s t))).sup (integrable_const 0)).const_mul α)).abs

end FCAppendix.Bayes
