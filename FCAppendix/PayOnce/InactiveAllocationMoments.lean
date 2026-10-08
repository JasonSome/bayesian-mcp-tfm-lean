import FCAppendix.PayOnce.InactiveAllocationConcentration
import FCAppendix.Probability.ClippedSubGaussianMoments

namespace FCAppendix.PayOnce

theorem rival_rpow_rate_le_population {M : ℕ} (hM : 2 ≤ M) {r : ℝ} (hr : 0 ≤ r) :
    ((M-1:ℕ):ℝ)^(-r/2) ≤ (2:ℝ)^(r/2)*(M:ℝ)^(-r/2) := by
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr (by omega)
  have hMN : (M:ℝ) ≤ 2*((M-1:ℕ):ℝ) := by
    exact_mod_cast (show M ≤ 2*(M-1) by omega)
  have hh := Real.rpow_le_rpow_of_nonpos (show 0 < (M:ℝ)/2 by positivity)
    (show (M:ℝ)/2 ≤ ((M-1:ℕ):ℝ) by linarith) (show -r/2 ≤ 0 by linarith)
  have he : -r/2 = -(r/2) := by ring
  rw [Real.div_rpow hMR.le (by norm_num),he,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul] at hh
  simpa only [he,mul_comm] using hh

end FCAppendix.PayOnce

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem integrable_focal_allocation_error_rpow {N n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] {T r : ℝ}
    (hT : 0 < T) (hr : 0 ≤ r) (b : ℝ) :
    Integrable (fun q => |allocation n c hn q b-kernel n b T|^r) μ := by
  apply Probability.integrable_rpow_of_bounded_nonneg μ (measurable_allocation_error hn b T) hr
  exact fun q => ⟨abs_nonneg _,allocation_error_le_one hn hT b q⟩

theorem payOnce_inactive_focal_allocation_moments_with_remainder
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (r : ℝ) (hr : 1 ≤ r) :
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      Integrable (fun q : Fin (M t-1) → ℝ =>
        |allocation (k+1) (C t) (by have := h.proposers_two; omega) q b-
          kernel (k+1) b (KernelDemand.populationPrice (k+1)
            (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))|^r)
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) ∧
      (∫ q : Fin (M t-1) → ℝ,
        |allocation (k+1) (C t) (by have := h.proposers_two; omega) q b-
          kernel (k+1) b (KernelDemand.populationPrice (k+1)
            (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))|^r
          ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) ≤
        3*Real.exp (-d*((M t-1:ℕ):ℝ))+
          (2*Real.exp 8)*Probability.gaussianMomentConstant r (2*K^2)*((M t-1:ℕ):ℝ)^(-r/2) := by
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  obtain ⟨K,d,hK,hd,hconc⟩ := payOnce_inactive_focal_allocation_concentration Γ B F g ρ h
  refine ⟨K,d,hK,hd,?_⟩
  filter_upwards [hconc,hbar.eventually (eventually_gt_nhds hL),
    h.population_grows.eventually_gt_atTop 1] with t ht hT htM
  intro b hb
  let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let T := KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let Y := fun q : Fin (M t-1) → ℝ => |allocation (k+1) (C t) hn q b-kernel (k+1) b T|
  have hYb : ∀ q, Y q ∈ Icc (0:ℝ) 1 := fun q =>
    ⟨abs_nonneg _,allocation_error_le_one hn hT b q⟩
  refine ⟨integrable_focal_allocation_error_rpow hn μ hT (by linarith) b,?_⟩
  have hh := Probability.bounded_rpow_moment_le_scaled_gaussian_tail μ
    (show Measurable Y from measurable_allocation_error hn b T)
    (by norm_num : (0:ℝ) ≤ 1) hr (by positivity : (0:ℝ) ≤ 2*Real.exp 8)
    (by positivity : (0:ℝ) < 2*K^2) (M t-1) (by omega) hYb (ht b hb)
  simpa only [Real.one_rpow,one_mul] using hh

theorem payOnce_inactive_focal_allocation_moments
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (r : ℝ) (hr : 1 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      Integrable (fun q : Fin (M t-1) → ℝ =>
        |allocation (k+1) (C t) (by have := h.proposers_two; omega) q b-
          kernel (k+1) b (KernelDemand.populationPrice (k+1)
            (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))|^r)
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) ∧
      (∫ q : Fin (M t-1) → ℝ,
        |allocation (k+1) (C t) (by have := h.proposers_two; omega) q b-
          kernel (k+1) b (KernelDemand.populationPrice (k+1)
            (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))|^r
          ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) ≤
        K*(M t:ℝ)^(-r/2) := by
  obtain ⟨K,d,hK,hd,hmoment⟩ :=
    payOnce_inactive_focal_allocation_moments_with_remainder Γ B F g ρ h r hr
  let Q := (2*Real.exp 8)*Probability.gaussianMomentConstant r (2*K^2)
  have hQ : 0 ≤ Q := mul_nonneg (by positivity)
    (Probability.gaussianMomentConstant_nonneg hr)
  have hcoef : 0 < 3+Q := by linarith
  have htwo : 0 < (2:ℝ)^(r/2) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨(3+Q)*(2:ℝ)^(r/2),mul_pos hcoef htwo,?_⟩
  have hN : Tendsto (fun t => M t-1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp h.population_grows
  have hexp : ∀ᶠ t in atTop, Real.exp (-d*((M t-1:ℕ):ℝ)) ≤ ((M t-1:ℕ):ℝ)^(-r/2) := by
    simpa only [neg_div] using Probability.eventually_nat_exp_neg_mul_le_rpow
      (fun t => M t-1) hN (r/2) hd
  filter_upwards [hmoment,hexp,h.population_grows.eventually_ge_atTop 2] with t ht he htM
  intro b hb
  refine ⟨(ht b hb).1,?_⟩
  have hdecay := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 3)
  have hrate := rival_rpow_rate_le_population htM (show 0 ≤ r by linarith)
  have hbound := (ht b hb).2
  change (∫ q : Fin (M t-1) → ℝ, _ ∂_) ≤ _ at hbound ⊢
  calc
    _ ≤ 3*Real.exp (-d*((M t-1:ℕ):ℝ))+Q*((M t-1:ℕ):ℝ)^(-r/2) := hbound
    _ ≤ (3+Q)*((M t-1:ℕ):ℝ)^(-r/2) := by linarith
    _ ≤ (3+Q)*((2:ℝ)^(r/2)*(M t:ℝ)^(-r/2)) :=
      mul_le_mul_of_nonneg_left hrate hcoef.le
    _ = ((3+Q)*(2:ℝ)^(r/2))*(M t:ℝ)^(-r/2) := by ring

end FCAppendix.Bayes
