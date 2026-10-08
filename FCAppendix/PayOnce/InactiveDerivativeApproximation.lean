import FCAppendix.PayOnce.InactiveOwnImpactMoments
import FCAppendix.PayOnce.InactiveAllocationMoments
import FCAppendix.PayOnce.ResponseFactor

namespace FCAppendix.PayOnce.RareSuccessSlope
open MeasureTheory Set TruncatedFOC

theorem weightedSlope_phi_error_le {n : ℕ} (hn : 2 ≤ n) {p q w K : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1)
    (hlip : |phi n p-phi n q| ≤ K*|p-q|) :
    |weightedSlope n p w-phi n q| ≤
      (n:ℝ)^2*w+K*|p-q|+(if p=0 then (n:ℝ)^2 else 0) := by
  have hc := AnalyticalKernel.slope_correction_bounds hn hp hw
  have hbase : |baseSlope n p-phi n p| ≤ if p=0 then (n:ℝ)^2 else 0 := by
    by_cases hp0 : p=0
    · rw [hp0]
      simp only [baseSlope,weightedSlope,lt_self_iff_false,false_and,if_false,sub_zero,mul_one,
        zero_sub,abs_neg]
      rw [abs_of_nonneg (phi_nonneg hn ⟨le_rfl,zero_le_one⟩)]
      exact phi_le_sq hn ⟨le_rfl,zero_le_one⟩
    · by_cases hp1 : p=1
      · rw [hp1,ResponseFactor.phi_one hn]
        simp [baseSlope,weightedSlope]
      · have hi : 0<p ∧ p<1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0),lt_of_le_of_ne hp.2 hp1⟩
        simp [baseSlope,weightedSlope,hi,hp0]
  have hco : |weightedSlope n p w-baseSlope n p| ≤ (n:ℝ)^2*w := by
    rw [abs_sub_comm,abs_of_nonneg hc.1]
    exact hc.2
  calc
    _ ≤ |weightedSlope n p w-baseSlope n p|+|baseSlope n p-phi n p|+|phi n p-phi n q| :=
      by
        have h1 := abs_sub_le (weightedSlope n p w) (baseSlope n p) (phi n q)
        have h2 := abs_sub_le (baseSlope n p) (phi n p) (phi n q)
        linarith
    _ ≤ _ := by linarith

theorem integral_weightedSlope_phi_error_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {p w : Ω → ℝ} (hp : Measurable p) (hw : Measurable w)
    (hpb : ∀ x, p x ∈ Icc (0:ℝ) 1) (hwb : ∀ x, w x ∈ Icc (0:ℝ) 1)
    {q K : ℝ} (hq : q ∈ Icc (0:ℝ) 1)
    (hlip : ∀ x, |phi n (p x)-phi n q| ≤ K*|p x-q|) :
    |(∫ x, weightedSlope n (p x) (w x) ∂μ)-phi n q| ≤
      (n:ℝ)^2*(∫ x, w x ∂μ)+K*(∫ x, |p x-q| ∂μ)+(n:ℝ)^2*μ.real {x | p x=0} := by
  have hi := integrable_weightedSlope μ hn hp hw hpb (fun x _ => hwb x)
  have hwi : Integrable w μ := Integrable.of_bound hw.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hwb x).1] using (hwb x).2)
  have hpi := CovarianceConcentration.integrable_abs_gap μ hp measurable_const hpb (fun _ => hq)
  let E := {x | p x=0}
  have hE : MeasurableSet E := measurableSet_eq_fun hp measurable_const
  have hEi : Integrable (E.indicator (fun _ => (n:ℝ)^2)) μ := (integrable_const _).indicator hE
  calc
    _ = |∫ x, weightedSlope n (p x) (w x)-phi n q ∂μ| := by rw [integral_sub hi (integrable_const _)]; simp
    _ ≤ ∫ x, |weightedSlope n (p x) (w x)-phi n q| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => weightedSlope n (p x) (w x)-phi n q)
    _ ≤ ∫ x, (n:ℝ)^2*w x+K*|p x-q|+E.indicator (fun _ => (n:ℝ)^2) x ∂μ := by
      apply integral_mono (hi.sub (integrable_const _)).abs (((hwi.const_mul _).add (hpi.const_mul _)).add hEi)
      intro x
      simpa only [E,indicator,mem_setOf_eq,Pi.add_apply,Pi.sub_apply] using weightedSlope_phi_error_le hn (hpb x) (hwb x) (hlip x)
    _ = _ := by
      rw [integral_add (show Integrable (fun x => (n:ℝ)^2*w x+K*|p x-q|) μ from (hwi.const_mul _).add (hpi.const_mul _)) hEi,
        integral_add (hwi.const_mul _) (hpi.const_mul _),integral_const_mul,integral_const_mul,
        integral_indicator_const _ hE]
      simp only [smul_eq_mul,mul_comm (μ.real E),E]

end FCAppendix.PayOnce.RareSuccessSlope

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent PayOnce.RareSuccessSlope
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_zero_allocation_bound
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ t in atTop, ∀ b : ℝ, bar t ≤ b →
      0 < b ∧ (Measure.pi (fun _ : Fin (M t-1) =>
        (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | allocation (k+1) (C t) hn r b=0} ≤
          3*Real.exp (-d*((M t-1:ℕ):ℝ))+
          (2*Real.exp 8)*Real.exp (-((M t-1:ℕ):ℝ)*(b-bar t)^2/(2*K^2)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  obtain ⟨K,d,hK,hd,he⟩ := payOnce_inactive_focal_price_concentration Γ B F g ρ h
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually_const_lt hL
  refine ⟨K,d,hK,hd,?_⟩
  filter_upwards [he,hbar] with t ht htbar
  intro b hb
  have hbp : 0 < b := lt_of_lt_of_le htbar hb
  refine ⟨hbp,?_⟩
  apply le_trans (measureReal_mono ?_) (ht b hbp (b-bar t) (sub_nonneg.mpr hb))
  intro r hr
  have hs := focalPrice_spec (c := C t) hn b r hbp
  have hzero : kernel (k+1) b (focalPrice (k+1) (C t) hn b r)=0 := hs.2.2.symm.trans hr
  have hprice := (kernel_eq_zero_iff (k+1) hn hbp hs.1).mp hzero
  exact (sub_le_sub_right hprice (bar t)).trans (le_abs_self _)

theorem payOnce_inactive_derivative_approximation
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let Q := fun t => coverage (k+1) (C t) hn (Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᶠ t in atTop, ∀ b : ℝ, bar t ≤ b →
      HasDerivAt (Q t) (deriv (Q t) b) b ∧
      |b*deriv (Q t) b-phi (k+1) (kernel (k+1) b (bar t))| ≤
        A*(M t:ℝ)^(-(1:ℝ)/2)+A*Real.exp (-c*(M t:ℝ)*(b-bar t)^2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let n := k+1
  let bar := fun t => KernelDemand.populationPrice n
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage n (C t) hn (μ t)
  obtain ⟨q,d₀,hq,hd₀,hown⟩ := payOnce_inactive_ownImpact_moments Γ B F g ρ h
  obtain ⟨K,d₁,hK,hd₁,hzero⟩ := payOnce_inactive_zero_allocation_bound Γ B F g ρ h
  obtain ⟨Kp,hKp,halloc⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h 1 le_rfl
  obtain ⟨Kφ,hKφ,hφ⟩ := ResponseFactor.exists_lipschitz_phi hn
  let W := (n:ℝ)^3/q
  let S := (2:ℝ)^((1:ℝ)/2)
  let A₀ := (n:ℝ)^2*(W+6)*S+Kφ*Kp
  let A₁ := (n:ℝ)^2*(2*Real.exp 8)
  have hW : 0 < W := by dsimp only [W,n]; positivity
  have hS : 0 < S := Real.rpow_pos_of_pos (by norm_num) _
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; positivity
  have hA₁ : 0 < A₁ := by dsimp only [A₁,n]; positivity
  refine ⟨A₀+A₁,1/(4*K^2),add_pos hA₀ hA₁,by positivity,?_⟩
  have hN : Tendsto (fun t => M t-1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp h.population_grows
  have hexp₀ := Probability.eventually_nat_exp_neg_mul_le_rpow (fun t => M t-1) hN ((1:ℝ)/2) hd₀
  have hexp₁ := Probability.eventually_nat_exp_neg_mul_le_rpow (fun t => M t-1) hN ((1:ℝ)/2) hd₁
  simp only [← neg_div] at hexp₀ hexp₁
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually_const_lt hL
  filter_upwards [hown,hzero,halloc,hexp₀,hexp₁,hbar,h.population_grows.eventually_ge_atTop 2]
    with t ht hz hp he₀ he₁ htbar htM
  intro b hb
  have hbp := (hz b hb).1
  obtain ⟨w,hw,hwb,_hgap,_hLp,hd,hwm⟩ := ht.2 b hbp
  have hederiv : b*deriv (Q t) b = ∫ r, weightedSlope n (allocation n (C t) hn r b) (w r) ∂μ t := by
    rw [hd.deriv]
    exact mul_div_cancel₀ _ hbp.ne'
  refine ⟨?_,?_⟩
  · convert hd using 1; exact hd.deriv
  have hNR : (1:ℝ) ≤ ((M t-1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ M t-1 by omega)
  have hinv : 1/((M t-1:ℕ):ℝ) ≤ ((M t-1:ℕ):ℝ)^(-(1:ℝ)/2) := by
    simpa only [Real.rpow_neg_one,one_div] using
      Real.rpow_le_rpow_of_exponent_le hNR (show (-1:ℝ) ≤ -(1:ℝ)/2 by norm_num)
  have hrival := rival_rpow_rate_le_population htM (by norm_num : (0:ℝ) ≤ 1)
  change ((M t-1:ℕ):ℝ)^(-(1:ℝ)/2) ≤ S*(M t:ℝ)^(-(1:ℝ)/2) at hrival
  have hwr : (∫ r, w r ∂μ t) ≤ (W+3)*S*(M t:ℝ)^(-(1:ℝ)/2) := by
    have hh := (hwm 1).2
    simp only [pow_one] at hh
    have hwfrac : ((n:ℝ)^3/(q*((M t-1:ℕ):ℝ))) = W*(1/((M t-1:ℕ):ℝ)) := by
      dsimp only [W]; ring
    rw [hwfrac] at hh
    have hx := mul_le_mul_of_nonneg_left hinv hW.le
    have he := mul_le_mul_of_nonneg_left he₀ (by norm_num : (0:ℝ) ≤ 3)
    have hr := mul_le_mul_of_nonneg_left hrival (by linarith : 0 ≤ W+3)
    nlinarith
  have hpr : (∫ r, |allocation n (C t) hn r b-kernel n b (bar t)| ∂μ t) ≤
      Kp*(M t:ℝ)^(-(1:ℝ)/2) := by
    simpa only [Real.rpow_one] using (hp b hbp).2
  have htail : Real.exp (-((M t-1:ℕ):ℝ)*(b-bar t)^2/(2*K^2)) ≤
      Real.exp (-(1/(4*K^2))*(M t:ℝ)*(b-bar t)^2) := by
    apply Real.exp_le_exp.mpr
    have hNM : (M t:ℝ)/2 ≤ ((M t-1:ℕ):ℝ) := by
      have he : ((M t-1:ℕ):ℝ)=(M t:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
      rw [he]; have : (2:ℝ) ≤ M t := by exact_mod_cast htM
      linarith
    have hh := mul_le_mul_of_nonneg_right hNM (sq_nonneg (b-bar t))
    have hK2 : 0 < K^2 := sq_pos_of_pos hK
    apply (mul_le_mul_iff_right₀ (show 0 < 4*K^2 by positivity)).mp
    field_simp
    nlinarith
  have hzr : (μ t).real {r | allocation n (C t) hn r b=0} ≤
      3*S*(M t:ℝ)^(-(1:ℝ)/2)+(2*Real.exp 8)*Real.exp (-(1/(4*K^2))*(M t:ℝ)*(b-bar t)^2) := by
    have hh := (hz b hb).2
    have he := mul_le_mul_of_nonneg_left (he₁.trans hrival) (by norm_num : (0:ℝ) ≤ 3)
    have hg := mul_le_mul_of_nonneg_left htail (by positivity : (0:ℝ) ≤ 2*Real.exp 8)
    nlinarith
  have hcmp := integral_weightedSlope_phi_error_le (μ t) hn
    (measurable_allocation_fixed_bid (c := C t) hn b) hw (fun r => allocation_bounds hn r b) hwb
    (kernel_bounds hn htbar b) (fun r => hφ _ (allocation_bounds hn r b) _ (kernel_bounds hn htbar b))
  rw [hederiv]
  have hδ : 0 ≤ (M t:ℝ)^(-(1:ℝ)/2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he : 0 ≤ Real.exp (-(1/(4*K^2))*(M t:ℝ)*(b-bar t)^2) := (Real.exp_pos _).le
  have h1 := mul_le_mul_of_nonneg_left hwr (sq_nonneg (n:ℝ))
  have h2 := mul_le_mul_of_nonneg_left hpr hKφ.le
  have h3 := mul_le_mul_of_nonneg_left hzr (sq_nonneg (n:ℝ))
  dsimp only [A₀,A₁] at hA₀ hA₁ ⊢
  nlinarith [mul_nonneg hA₀.le he,mul_nonneg hA₁.le hδ]

end FCAppendix.Bayes
