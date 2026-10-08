import FCAppendix.PayOnce.AllocationFirstMoment
import FCAppendix.PayOnce.InactiveDerivativeRoot
import FCAppendix.PayOnce.FiniteFOCResponse

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_coverage_approximation
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let Q := fun t => coverage (k+1) (C t) hn
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |Q t b-success (k+1) (kernel (k+1) b (bar t))| ≤ A*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  obtain ⟨A,hA,he⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h 1 (by norm_num)
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually_const_lt hL
  refine ⟨((k+1:ℕ):ℝ)*A,by positivity,?_⟩
  filter_upwards [he,hbar] with t ht hT
  intro b hb
  have hmoment : (∫ r : Fin (M t-1) → ℝ,
      |allocation (k+1) (C t) hn r b-kernel (k+1) b
        (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))|
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) ≤
      A*(M t:ℝ)^(-(1:ℝ)/2) := by simpa only [rpow_one] using (ht b hb).2
  have hh := AnalyticalKernel.integral_success_error_le
    (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) (k+1)
    (fun r => allocation (k+1) (C t) hn r b) (measurable_allocation_fixed_bid hn b)
    (fun r => allocation_bounds hn r b) (kernel_bounds hn hT b)
  exact hh.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg (k+1)))

theorem payOnce_inactive_far_above_coverage_floor
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {ε : ℝ} (hε : 0 < ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let Q := fun t => coverage (k+1) (C t) hn
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    ∃ q₀ : ℝ, 0 < q₀ ∧ ∀ᶠ t in atTop, ∀ b : ℝ, bar t+ε ≤ b → q₀ ≤ Q t b := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let b₀ := L+ε/2
  let p₀ := kernel (k+1) b₀ L
  let S₀ := success (k+1) p₀
  let K := ((k+1:ℕ):ℝ)/(L/2)
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hb₀ : 0 < b₀ := by dsimp only [b₀]; positivity
  have hp₀ : 0 < p₀ := by
    have hb := kernel_bounds hn hL b₀
    apply lt_of_le_of_ne hb.1
    intro hh
    have hle := (kernel_eq_zero_iff (k+1) hn hb₀ hL).mp hh.symm
    dsimp only [b₀] at hle
    linarith
  have hS₀ : 0 < S₀ := success_pos (k+1) (by omega) p₀ hp₀ (kernel_bounds hn hL b₀).2
  have hK : 0 < K := by dsimp only [K]; positivity
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  change Tendsto bar atTop (𝓝 L) at hbar
  have hδ : Tendsto (fun t => (M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := (1:ℝ)/2) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp h.population_grows)
  obtain ⟨A,hA,hcov⟩ := payOnce_inactive_coverage_approximation Γ B F g ρ h
  have htotal : Tendsto (fun t => A*(M t:ℝ)^(-(1:ℝ)/2)+
      ((k+1:ℕ):ℝ)*K*|bar t-L|) atTop (𝓝 0) := by
    have hg := ((hbar.sub_const L).abs.const_mul (((k+1:ℕ):ℝ)*K))
    simpa only [sub_self,abs_zero,mul_zero,add_zero] using (hδ.const_mul A).add hg
  have hsmall := htotal.eventually_le_const (half_pos hS₀)
  refine ⟨S₀/2,half_pos hS₀,?_⟩
  filter_upwards [hcov,hsmall,hbar.eventually
    (Ioo_mem_nhds (show max (L/2) (L-ε/2) < L by apply max_lt <;> linarith)
      (show L < L+1 by linarith))] with t ht hsm hbt
  intro b hb
  have hbarlo : L/2 ≤ bar t := (le_max_left _ _).trans hbt.1.le
  have hbarpos : 0 < bar t := (half_pos hL).trans_le hbarlo
  have hb₀b : b₀ ≤ b := by
    have hnear := (le_max_right (L/2) (L-ε/2)).trans hbt.1.le
    dsimp only [b₀]
    linarith
  have hker := KernelLawConvergence.kernel_price_difference hn (half_pos hL)
    hbarlo (show L/2 ≤ L by linarith) b₀
  have hsucc := OwnImpact.success_abs_sub_le (k+1)
    (kernel_bounds hn hbarpos b₀) (kernel_bounds hn hL b₀)
  have hsucc' : |success (k+1) (kernel (k+1) b₀ (bar t))-S₀| ≤
      ((k+1:ℕ):ℝ)*K*|bar t-L| := by
    exact hsucc.trans (by simpa only [mul_assoc,K] using
      mul_le_mul_of_nonneg_left hker (Nat.cast_nonneg (k+1)))
  have hfixed := ht b₀ hb₀
  have hfloor : S₀/2 ≤ coverage (k+1) (C t) hn (μ t) b₀ := by
    have h1 := (abs_le.mp hfixed).1
    have h2 := (abs_le.mp hsucc').1
    change -(A*(M t:ℝ)^(-(1:ℝ)/2)) ≤
      coverage (k+1) (C t) hn (μ t) b₀-success (k+1) (kernel (k+1) b₀ (bar t)) at h1
    linarith
  exact hfloor.trans (coverage_monotone hn (μ t) hb₀b)

theorem payOnce_inactive_far_above_response
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {ε : ℝ} (hε : 0 < ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let Q := fun t => coverage (k+1) (C t) hn (μ t)
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t in atTop, ∀ w b : ℝ, bar t+ε ≤ b →
      Q t b = (w-b)*deriv (Q t) b →
      |kernel (k+1) b (bar t)-Limit.pStar (k+1) (bar t) w| ≤
        D*(M t:ℝ)^(-(1:ℝ)/2) ∧
      |(∫ r, allocation (k+1) (C t) hn r b ∂μ t)-Limit.pStar (k+1) (bar t) w| ≤
        D*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage (k+1) (C t) hn (μ t)
  obtain ⟨q₀,hq₀,hfloor⟩ := payOnce_inactive_far_above_coverage_floor Γ B F g ρ h hε
  obtain ⟨Ac,hAc,hcoverage⟩ := payOnce_inactive_coverage_approximation Γ B F g ρ h
  obtain ⟨Ar,hAr,hroot⟩ := payOnce_inactive_derivative_root_approximation Γ B F g ρ h hε
  obtain ⟨Ap,hAp,halloc⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h 1 (by norm_num)
  obtain ⟨D,hD,hinv⟩ := FiniteFOCResponse.exists_uniform_response_error_constant hn hq₀
  let A := Ac+Ar
  have hA : 0 < A := add_pos hAc hAr
  have hδ : Tendsto (fun t => (M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := (1:ℝ)/2) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp h.population_grows)
  have hsmall : ∀ᶠ t in atTop, A*(M t:ℝ)^(-(1:ℝ)/2) ≤ min 1 (q₀/2) := by
    have hzero : Tendsto (fun t => A*(M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hδ.const_mul A
    exact hzero.eventually_le_const (lt_min (by norm_num) (half_pos hq₀))
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually_const_lt hL
  refine ⟨Ap+D*A,by positivity,?_⟩
  filter_upwards [hfloor,hcoverage,hroot,halloc,hsmall,hbar] with t hf hc hr hp hs htbar
  intro w b hb hFOC
  change Q t b = (w-b)*deriv (Q t) b at hFOC
  have hTb : bar t < b := by linarith
  have hbp : 0 < b := lt_trans htbar hTb
  have hδnonneg : 0 ≤ (M t:ℝ)^(-(1:ℝ)/2) := rpow_nonneg (Nat.cast_nonneg _) _
  have hcov : |Q t b-success (k+1) (kernel (k+1) b (bar t))| ≤
      A*(M t:ℝ)^(-(1:ℝ)/2) :=
    (hc b hbp).trans (mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith) hδnonneg)
  have hrooterr : |(b*deriv (Q t) b)^(1/(((k+1:ℕ):ℝ)-1))-
      ResponseFactor.rootFactor (k+1) (kernel (k+1) b (bar t))| ≤
      A*(M t:ℝ)^(-(1:ℝ)/2) :=
    (hr b hb).2.trans (mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith) hδnonneg)
  have hR : 0 ≤ b*deriv (Q t) b :=
    mul_nonneg hbp.le (coverage_monotone hn (μ t)).deriv_nonneg
  have hnorm : b*Q t b = (w-b)*(b*deriv (Q t) b) := by
    calc
      b*Q t b = b*((w-b)*deriv (Q t) b) := by rw [hFOC]
      _ = (w-b)*(b*deriv (Q t) b) := by ring
  have hkernel := hinv (bar t) b w (Q t b) (b*deriv (Q t) b)
    (A*(M t:ℝ)^(-(1:ℝ)/2)) htbar hTb (hf b hb) hR hnorm hs hcov hrooterr
  have hmoment : (∫ r, |allocation (k+1) (C t) hn r b-kernel (k+1) b (bar t)| ∂μ t) ≤
      Ap*(M t:ℝ)^(-(1:ℝ)/2) := by simpa only [rpow_one] using (hp b hbp).2
  have hmean := (allocation_mean_error_le hn (μ t) b (kernel (k+1) b (bar t))).trans hmoment
  constructor
  · apply hkernel.trans
    nlinarith [mul_nonneg hAp.le hδnonneg]
  · calc
      _ ≤ |(∫ r, allocation (k+1) (C t) hn r b ∂μ t)-kernel (k+1) b (bar t)|+
          |kernel (k+1) b (bar t)-Limit.pStar (k+1) (bar t) w| := abs_sub_le _ _ _
      _ ≤ Ap*(M t:ℝ)^(-(1:ℝ)/2)+D*(A*(M t:ℝ)^(-(1:ℝ)/2)) := add_le_add hmean hkernel
      _ = (Ap+D*A)*(M t:ℝ)^(-(1:ℝ)/2) := by ring

end FCAppendix.Bayes
