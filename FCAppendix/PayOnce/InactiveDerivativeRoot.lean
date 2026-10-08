import FCAppendix.PayOnce.InactiveDerivativeApproximation
import FCAppendix.PayOnce.DerivativeRootMoment

namespace FCAppendix.Probability
open Real

theorem moment_root_le_sqrt_rate {x A N a : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A)
    (hN : 0 ≤ N) (ha : 0 < a) (h : x ≤ A*N^(-a/2)) :
    x^(1/a) ≤ A^(1/a)*N^(-(1:ℝ)/2) := by
  calc
    _ ≤ (A*N^(-a/2))^(1/a) := rpow_le_rpow hx h (one_div_pos.mpr ha).le
    _ = _ := by
      rw [mul_rpow hA (rpow_nonneg hN _),← rpow_mul hN]
      congr 2
      field_simp

theorem pow_div_le_half_rate {W N : ℝ} (hW : 0 ≤ W) (hN : 1 ≤ N) (a : ℕ) :
    (W/N)^a ≤ W^a*N^(-(a:ℝ)/2) := by
  have hNi : 1/N ≤ N^(-(1:ℝ)/2) := by
    simpa only [rpow_neg_one,one_div] using
      rpow_le_rpow_of_exponent_le hN (show (-1:ℝ) ≤ -(1:ℝ)/2 by norm_num)
  have hh := pow_le_pow_left₀ (div_nonneg hW (by linarith : 0 ≤ N))
    (show W/N ≤ W*N^(-(1:ℝ)/2) by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hNi hW) a
  apply hh.trans_eq
  rw [mul_pow,← rpow_mul_natCast (by linarith : 0 ≤ N)]
  congr 2
  ring

end FCAppendix.Probability

set_option maxHeartbeats 800000

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent
open PayOnce.RareSuccessSlope PayOnce.ResponseFactor
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_derivative_root_approximation
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {ε : ℝ} (hε : 0 < ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let Q := fun t => coverage (k+1) (C t) hn (Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ t in atTop, ∀ b : ℝ, bar t+ε ≤ b →
      HasDerivAt (Q t) (deriv (Q t) b) b ∧
      |(b*deriv (Q t) b)^(1/(((k+1:ℕ):ℝ)-1)) - rootFactor (k+1) (kernel (k+1) b (bar t))| ≤
        A*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  have hk : (1:ℝ) ≤ k := by exact_mod_cast h.proposers_two
  have hkpos : (0:ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  let n := k+1
  let bar := fun t => KernelDemand.populationPrice n
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage n (C t) hn (μ t)
  let κ := 1/((n:ℝ)^3+1)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  obtain ⟨D,hD,hroot⟩ := DerivativeRootMoment.exists_derivative_root_moment_bound hn hκ
  obtain ⟨q,d₀,hq,hd₀,hown⟩ := payOnce_inactive_ownImpact_moments Γ B F g ρ h
  obtain ⟨K,d₁,hK,hd₁,hzero⟩ := payOnce_inactive_zero_allocation_bound Γ B F g ρ h
  obtain ⟨Kp,hKp,halloc⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h k hk
  let W := (n:ℝ)^3/q
  let S := (2:ℝ)^((k:ℝ)/2)
  let Kw := (W^k+3)*S
  let Kz := (3+2*Real.exp 8)*S
  let dε := ε^2/(2*K^2)
  have hW : 0 < W := by dsimp only [W,n]; positivity
  have hS : 0 < S := Real.rpow_pos_of_pos (by norm_num) _
  have hKw : 0 < Kw := by dsimp only [Kw]; positivity
  have hKz : 0 < Kz := by dsimp only [Kz]; positivity
  have hdε : 0 < dε := by dsimp only [dε]; positivity
  refine ⟨D*(Kp^(1/(k:ℝ))+Kw^(1/(k:ℝ))+Kz^(1/(k:ℝ))),by positivity,?_⟩
  have hN : Tendsto (fun t => M t-1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp h.population_grows
  have hexp₀ := Probability.eventually_nat_exp_neg_mul_le_rpow (fun t => M t-1) hN ((k:ℝ)/2) hd₀
  have hexp₁ := Probability.eventually_nat_exp_neg_mul_le_rpow (fun t => M t-1) hN ((k:ℝ)/2) hd₁
  have hexpε := Probability.eventually_nat_exp_neg_mul_le_rpow (fun t => M t-1) hN ((k:ℝ)/2) hdε
  simp only [← neg_div] at hexp₀ hexp₁ hexpε
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually_const_lt hL
  filter_upwards [hown,hzero,halloc,hexp₀,hexp₁,hexpε,hbar,h.population_grows.eventually_ge_atTop 2]
    with t ht hz hp he₀ he₁ heε htbar htM
  intro b hb
  have hbbar : bar t ≤ b := by linarith
  have hbp := (hz b hbbar).1
  obtain ⟨w,hw,hwb,hgap,_hLp,hd,hwm⟩ := ht.2 b hbp
  have hederiv : b*deriv (Q t) b = ∫ r, weightedSlope n (allocation n (C t) hn r b) (w r) ∂μ t := by
    rw [hd.deriv]
    exact mul_div_cancel₀ _ hbp.ne'
  refine ⟨?_,?_⟩
  · convert hd using 1; exact hd.deriv
  have hNR : (1:ℝ) ≤ ((M t-1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ M t-1 by omega)
  have hrival := rival_rpow_rate_le_population htM hkpos.le
  change ((M t-1:ℕ):ℝ)^(-(k:ℝ)/2) ≤ S*(M t:ℝ)^(-(k:ℝ)/2) at hrival
  have hwmoment : (∫ r, w r^k ∂μ t) ≤ Kw*(M t:ℝ)^(-(k:ℝ)/2) := by
    have hh := (hwm k).2
    have heW : ((n:ℝ)^3/(q*((M t-1:ℕ):ℝ)))=W/((M t-1:ℕ):ℝ) := by dsimp only [W]; ring
    rw [heW] at hh
    have hpow := Probability.pow_div_le_half_rate hW.le hNR k
    have he := mul_le_mul_of_nonneg_left he₀ (by norm_num : (0:ℝ) ≤ 3)
    have hr := mul_le_mul_of_nonneg_left hrival (by positivity : 0 ≤ W^k+3)
    dsimp only [Kw]
    nlinarith
  have hpmoment : (∫ r, |allocation n (C t) hn r b-kernel n b (bar t)|^k ∂μ t) ≤
      Kp*(M t:ℝ)^(-(k:ℝ)/2) := by
    simpa only [Real.rpow_natCast] using (hp b hbp).2
  have htail : Real.exp (-((M t-1:ℕ):ℝ)*(b-bar t)^2/(2*K^2)) ≤
      Real.exp (-dε*((M t-1:ℕ):ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hsq : ε^2 ≤ (b-bar t)^2 := by nlinarith
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hsq
      (neg_nonpos.mpr (Nat.cast_nonneg (M t-1) : (0:ℝ) ≤ ((M t-1:ℕ):ℝ)))) (by positivity : 0 ≤ 2*K^2)
    dsimp only [dε]
    exact hh.trans_eq (by ring)
  have hzmoment : (μ t).real {r | allocation n (C t) hn r b=0} ≤ Kz*(M t:ℝ)^(-(k:ℝ)/2) := by
    have hh := (hz b hbbar).2
    have he := mul_le_mul_of_nonneg_left he₁ (by norm_num : (0:ℝ) ≤ 3)
    have hg := mul_le_mul_of_nonneg_left (htail.trans heε) (by positivity : (0:ℝ) ≤ 2*Real.exp 8)
    have hr := mul_le_mul_of_nonneg_left hrival (by positivity : (0:ℝ) ≤ 3+2*Real.exp 8)
    dsimp only [Kz]
    nlinarith
  have hpRoot := Probability.moment_root_le_sqrt_rate
    (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) k) hKp.le (Nat.cast_nonneg (M t)) hkpos hpmoment
  have hwRoot := Probability.moment_root_le_sqrt_rate
    (integral_nonneg fun r => pow_nonneg (hwb r).1 k) hKw.le (Nat.cast_nonneg (M t)) hkpos hwmoment
  have hzRoot := Probability.moment_root_le_sqrt_rate (measureReal_nonneg) hKz.le
    (Nat.cast_nonneg (M t)) hkpos hzmoment
  have hh := hroot (μ t) (fun r => allocation n (C t) hn r b) w
    (measurable_allocation_fixed_bid hn b) hw (fun r => allocation_bounds hn r b)
    (fun r => ⟨(hwb r).1,by linarith [hgap r]⟩) (kernel n b (bar t)) (kernel_bounds hn htbar b)
  have hncast : ((k+1:ℕ):ℝ)-1=(k:ℝ) := by norm_num
  simp only [Nat.add_sub_cancel,hncast] at hh
  rw [hederiv,hncast]
  dsimp only [n] at hpRoot hwRoot hzRoot hh ⊢
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (add_le_add hpRoot hwRoot) hzRoot) hD.le]

end FCAppendix.Bayes
