import FCAppendix.PayOnce.InactiveProfilePriceConcentration
import FCAppendix.Probability.ClippedSubGaussianMoments
import FCAppendix.PayOnce.InactiveAllocationMoments

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_clipped_focal_price_moments_with_remainder
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (ℓ u : ℝ)
    (hℓ : ℓ < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u)
    {r : ℝ} (hr : 1 ≤ r) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      Integrable (fun z => |clipToInterval ℓ u (focalPrice (k+1) (C t) hn b z)-bar t|^r) (P t) ∧
      (∫ z, |clipToInterval ℓ u (focalPrice (k+1) (C t) hn b z)-bar t|^r ∂P t) ≤
        (u-ℓ)^r*3*Real.exp (-d*((M t-1:ℕ):ℝ))+
        (2*Real.exp 8)*gaussianMomentConstant r (2*K^2)*((M t-1:ℕ):ℝ)^(-r/2) := by
  dsimp only
  have hk := h.proposers_two
  obtain ⟨K,d,hK,hd,htail⟩ := payOnce_inactive_focal_price_concentration Γ B F g ρ h
  refine ⟨K,d,hK,hd,?_⟩
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  filter_upwards [htail,hbar.eventually_const_lt hℓ,hbar.eventually_lt_const hu,
    h.population_grows.eventually_gt_atTop 1] with t ht hl hu htM
  intro b hb
  exact clipped_rpow_moment_le_exponential _ (measurable_focalPrice (by omega) b)
    ⟨hl.le,hu.le⟩ hr (by positivity) (by positivity) (M t-1) (by omega) (ht b hb)

theorem payOnce_inactive_clipped_profile_price_moments_with_remainder
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (ℓ u : ℝ)
    (hℓ : ℓ < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u)
    {r : ℝ} (hr : 1 ≤ r) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ t in atTop,
      Integrable (fun z => |clipToInterval ℓ u (sampleProfilePrice (k+1) (C t) hn z)-bar t|^r) (P t) ∧
      (∫ z, |clipToInterval ℓ u (sampleProfilePrice (k+1) (C t) hn z)-bar t|^r ∂P t) ≤
        (u-ℓ)^r*6*Real.exp (-d*(M t:ℝ))+
        (2*Real.exp 8)*gaussianMomentConstant r (2*K^2)*(M t:ℝ)^(-r/2) := by
  dsimp only
  have hk := h.proposers_two
  obtain ⟨K,d,hK,hd,htail⟩ := payOnce_inactive_profile_price_concentration Γ B F g ρ h
  refine ⟨K,d,hK,hd,?_⟩
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  filter_upwards [htail,hbar.eventually_const_lt hℓ,hbar.eventually_lt_const hu,
    h.population_grows.eventually_gt_atTop 0] with t ht hl hu htM
  exact clipped_rpow_moment_le_exponential _ (measurable_sampleProfilePrice (by omega))
    ⟨hl.le,hu.le⟩ hr (by positivity) (by positivity) (M t) htM ht

theorem payOnce_inactive_clipped_profile_price_moments
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (ℓ u : ℝ)
    (hℓ : ℓ < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u)
    {r : ℝ} (hr : 1 ≤ r) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t in atTop,
      Integrable (fun z => |clipToInterval ℓ u (sampleProfilePrice (k+1) (C t) hn z)-bar t|^r) (P t) ∧
      (∫ z, |clipToInterval ℓ u (sampleProfilePrice (k+1) (C t) hn z)-bar t|^r ∂P t) ≤
        K*(M t:ℝ)^(-r/2) := by
  dsimp only
  have hk := h.proposers_two
  obtain ⟨K,d,hK,hd,he⟩ :=
    payOnce_inactive_clipped_profile_price_moments_with_remainder Γ B F g ρ h ℓ u hℓ hu hr
  have hp := eventually_uniform_power_bound_of_exponential M h.population_grows (p := r/2) hd
    (show 0 ≤ (u-ℓ)^r*6 from mul_nonneg (Real.rpow_nonneg (by linarith) _) (by norm_num))
    (show 0 ≤ (2*Real.exp 8)*gaussianMomentConstant r (2*K^2) from
      mul_nonneg (by positivity) (gaussianMomentConstant_nonneg hr))
    (S := (Set.univ : Set Unit))
    (f := fun t _ => ∫ z,
      |clipToInterval ℓ u (sampleProfilePrice (k+1) (C t) (by omega) z)-
        KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))|^r
        ∂(Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))))
    (by filter_upwards [he] with t ht _ _; simpa only [neg_div] using ht.2)
  refine ⟨(u-ℓ)^r*6+(2*Real.exp 8)*gaussianMomentConstant r (2*K^2)+1,hp.1,?_⟩
  filter_upwards [he,hp.2] with t ht hpt
  exact ⟨ht.1,by simpa only [neg_div] using hpt () (mem_univ _)⟩

theorem payOnce_inactive_clipped_focal_price_moments
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (ℓ u : ℝ)
    (hℓ : ℓ < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u)
    {r : ℝ} (hr : 1 ≤ r) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      Integrable (fun z => |clipToInterval ℓ u (focalPrice (k+1) (C t) hn b z)-bar t|^r) (P t) ∧
      (∫ z, |clipToInterval ℓ u (focalPrice (k+1) (C t) hn b z)-bar t|^r ∂P t) ≤
        K*(M t:ℝ)^(-r/2) := by
  dsimp only
  have hk := h.proposers_two
  obtain ⟨K,d,hK,hd,he⟩ :=
    payOnce_inactive_clipped_focal_price_moments_with_remainder Γ B F g ρ h ℓ u hℓ hu hr
  let A := (u-ℓ)^r*3+(2*Real.exp 8)*gaussianMomentConstant r (2*K^2)+1
  have hp := eventually_uniform_power_bound_of_exponential (fun t => M t-1)
    ((tendsto_sub_atTop_nat 1).comp h.population_grows) (p := r/2) hd
    (show 0 ≤ (u-ℓ)^r*3 from mul_nonneg (Real.rpow_nonneg (by linarith) _) (by norm_num))
    (show 0 ≤ (2*Real.exp 8)*gaussianMomentConstant r (2*K^2) from
      mul_nonneg (by positivity) (gaussianMomentConstant_nonneg hr))
    (S := Ioi (0:ℝ))
    (f := fun t b => ∫ z,
      |clipToInterval ℓ u (focalPrice (k+1) (C t) (by omega) b z)-
        KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))|^r
        ∂(Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))))
    (by filter_upwards [he] with t ht b hb; simpa only [neg_div] using (ht b hb).2)
  have hA : 0 < A := hp.1
  refine ⟨A*(2:ℝ)^(r/2),mul_pos hA (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  filter_upwards [he,hp.2,h.population_grows.eventually_gt_atTop 1] with t ht hpt htM
  intro b hb
  refine ⟨(ht b hb).1,?_⟩
  have hh : (∫ z,
      |clipToInterval ℓ u (focalPrice (k+1) (C t) (by omega) b z)-
        KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))|^r
        ∂(Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))) ≤
      A*((M t-1:ℕ):ℝ)^(-r/2) := by simpa only [neg_div] using hpt b hb
  exact hh.trans (by
    have hh := mul_le_mul_of_nonneg_left (rival_rpow_rate_le_population (by omega : 2 ≤ M t)
      (by linarith : 0 ≤ r)) hA.le
    simpa only [mul_assoc] using hh)

end FCAppendix.Bayes
