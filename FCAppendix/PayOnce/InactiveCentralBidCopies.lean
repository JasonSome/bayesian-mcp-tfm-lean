import FCAppendix.PayOnce.InactiveCentralAllocationMoments
import FCAppendix.PayOnce.BinomialMomentAsymptotics
import FCAppendix.Probability.WeakConvergenceCongruence

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_bid_copies
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ) {z : ℝ}
    (hy : Tendsto (fun t => (b t-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 z)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let α := 2/((((k+1:ℕ):ℝ)-1)*L)
    let s := inactiveGaussianScale M F (k+1) g ρ
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let p := fun (t : ℕ) (r : Fin (M t-1) → ℝ) => allocation (k+1) (C t) hn r (b t)
    TendstoInDistribution (fun t r => p t r/s t) atTop (fun Z => α*max (z-Z) 0) μ (gaussianReal 0 1) ∧
      (∀ j : ℕ, Tendsto (fun t => (∫ r, (p t r)^j ∂μ t)/(s t)^j) atTop
        (𝓝 (α^j*(∫ Z : ℝ, (max (z-Z) 0)^j ∂gaussianReal 0 1)))) ∧
      ∀ j : ℕ, Tendsto (fun t => (∫ r, ManyProposers.binomialMass (k+1) (p t r) j ∂μ t)/(s t)^j)
        atTop (𝓝 ((Nat.choose (k+1) j:ℝ)*α^j*(∫ Z : ℝ, (max (z-Z) 0)^j ∂gaussianReal 0 1))) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let α := 2/((((k+1:ℕ):ℝ)-1)*L)
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let y := fun t => (b t-bar t)/s t
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let p := fun (t : ℕ) (r : Fin (M t-1) → ℝ) => allocation (k+1) (C t) hn r (b t)
  have hsp : ∀ᶠ t in atTop, 0 < s t := by
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    exact payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
  have he : ∀ᶠ t in atTop, bar t+s t*y t=b t := by
    filter_upwards [hsp] with t ht
    dsimp only [y]
    rw [mul_div_cancel₀ _ ht.ne']
    ring
  have hmom j : Tendsto (fun t => (∫ r, (p t r)^j ∂μ t)/(s t)^j) atTop
      (𝓝 (α^j*(∫ Z : ℝ, (max (z-Z) 0)^j ∂gaussianReal 0 1))) := by
    apply (payOnce_inactive_central_allocation_moment_tendsto Γ B F g ρ h hlocal y hy j).congr'
    filter_upwards [he] with t ht
    change (∫ r, (allocation (k+1) (C t) hn r (bar t+s t*y t))^j ∂μ t)/(s t)^j = _
    rw [ht]
  refine ⟨?_,hmom,?_⟩
  · apply tendstoInDistribution_congr_eventually μ (gaussianReal 0 1) _ _ _
      (fun t => (measurable_allocation_fixed_bid hn (b t)).div_const (s t))
      (payOnce_inactive_central_allocation_tendstoInDistribution Γ B F g ρ h hlocal y hy)
    filter_upwards [he] with t ht
    apply Filter.Eventually.of_forall
    intro r
    change allocation (k+1) (C t) hn r (b t)/s t = allocation (k+1) (C t) hn r (bar t+s t*y t)/s t
    rw [ht]
  · intro j
    have hh := ManyProposers.binomialMass_integral_asymptotic μ p
      (fun t => measurable_allocation_fixed_bid hn (b t)) (fun t r => allocation_bounds hn r (b t))
      s hsp (inactiveGaussianScale_tendsto_zero M F (k+1) g ρ h.population_grows)
      (k+1) j (hmom j) (hmom (j+1))
    simpa only [mul_assoc] using hh

end FCAppendix.Bayes
