import FCAppendix.PayOnce.InactiveDerivativeApproximation

namespace FCAppendix.PayOnce.RareSuccessSlope
open MeasureTheory Set

theorem integral_weightedSlope_sub_phi_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {p w : Ω → ℝ} (hp : Measurable p) (hw : Measurable w)
    (hpb : ∀ x, p x ∈ Icc (0:ℝ) 1) (hwb : ∀ x, w x ∈ Icc (0:ℝ) 1) :
    |(∫ x, weightedSlope n (p x) (w x) ∂μ)-(∫ x, phi n (p x) ∂μ)| ≤
      (n:ℝ)^2*(∫ x, w x ∂μ)+(n:ℝ)^2*μ.real {x | p x=0} := by
  have hi := integrable_weightedSlope μ hn hp hw hpb (fun x _ => hwb x)
  have hj : Integrable (fun x => phi n (p x)) μ := Integrable.of_bound
    ((measurable_phi n).comp hp).aestronglyMeasurable ((n:ℝ)^2)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (phi_nonneg hn (hpb x))]
      exact phi_le_sq hn (hpb x))
  have hwi : Integrable w μ := Integrable.of_bound hw.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hwb x).1] using (hwb x).2)
  let E := {x | p x=0}
  have hE : MeasurableSet E := measurableSet_eq_fun hp measurable_const
  have hEi : Integrable (E.indicator (fun _ => (n:ℝ)^2)) μ := (integrable_const _).indicator hE
  calc
    _ = |∫ x, weightedSlope n (p x) (w x)-phi n (p x) ∂μ| := by rw [integral_sub hi hj]
    _ ≤ ∫ x, |weightedSlope n (p x) (w x)-phi n (p x)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => weightedSlope n (p x) (w x)-phi n (p x))
    _ ≤ ∫ x, (n:ℝ)^2*w x+E.indicator (fun _ => (n:ℝ)^2) x ∂μ := by
      apply integral_mono (hi.sub hj).abs ((hwi.const_mul _).add hEi)
      intro x
      simpa only [E,indicator,mem_setOf_eq,Pi.add_apply,Pi.sub_apply,zero_mul,add_zero] using
        weightedSlope_phi_error_le hn (hpb x) (hwb x)
          (show |phi n (p x)-phi n (p x)| ≤ (0:ℝ)*|p x-p x| by simp)
    _ = _ := by
      rw [integral_add (hwi.const_mul _) hEi,integral_const_mul,integral_indicator_const _ hE]
      simp only [smul_eq_mul,mul_comm (μ.real E),E]

end FCAppendix.PayOnce.RareSuccessSlope

namespace FCAppendix.Probability
open Filter Topology

theorem sqrt_population_div_rivals_le {M : ℕ} (hM : 2 ≤ M) :
    Real.sqrt (M:ℝ)/((M-1:ℕ):ℝ) ≤ 2/Real.sqrt (M:ℝ) := by
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr (by omega)
  have hNR : (0:ℝ) < ((M-1:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  have hN : ((M-1:ℕ):ℝ)=(M:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  apply (div_le_div_iff₀ hNR (Real.sqrt_pos.mpr hMR)).mpr
  have h2 : (2:ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [Real.sq_sqrt hMR.le]

theorem exp_neg_rivals_le_population {M : ℕ} (hM : 2 ≤ M) {d : ℝ} (hd : 0 ≤ d) :
    Real.exp (-d*((M-1:ℕ):ℝ)) ≤ Real.exp (-(d/2)*(M:ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hN : ((M-1:ℕ):ℝ)=(M:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have h2 : (2:ℝ) ≤ M := by exact_mod_cast hM
  rw [hN]
  nlinarith

theorem tendsto_sqrt_nat_mul_exp_neg_mul (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun t => Real.sqrt (M t:ℝ)*Real.exp (-d*(M t:ℝ))) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1:ℝ)/2) d hd).comp
      (tendsto_natCast_atTop_atTop.comp hM)

end FCAppendix.Probability

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent PayOnce.RareSuccessSlope
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_above_entry_zero_exponential
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {ε : ℝ} (hε : 0 < ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᶠ t in atTop, ∀ b : ℝ, bar t+ε ≤ b →
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | allocation (k+1) (C t) hn r b=0} ≤ A*Real.exp (-c*(M t:ℝ)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  obtain ⟨K,d,hK,hd,he⟩ := payOnce_inactive_zero_allocation_bound Γ B F g ρ h
  let c := min d (ε^2/(2*K^2))/2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcd : c ≤ d/2 := by dsimp only [c]; linarith [min_le_left d (ε^2/(2*K^2))]
  have hcε : c ≤ (ε^2/(2*K^2))/2 := by dsimp only [c]; linarith [min_le_right d (ε^2/(2*K^2))]
  refine ⟨3+2*Real.exp 8,c,by positivity,hc,?_⟩
  filter_upwards [he,h.population_grows.eventually_ge_atTop 2] with t ht htM
  intro b hb
  have hbbar : bar t ≤ b := by linarith
  have htail := (ht b hbbar).2
  have hsq : ε^2 ≤ (b-bar t)^2 := by nlinarith
  have he₀ : Real.exp (-d*((M t-1:ℕ):ℝ)) ≤ Real.exp (-c*(M t:ℝ)) :=
    (Probability.exp_neg_rivals_le_population htM hd.le).trans (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_right hcd (Nat.cast_nonneg (M t) : (0:ℝ) ≤ M t)]))
  have he₁ : Real.exp (-((M t-1:ℕ):ℝ)*(b-bar t)^2/(2*K^2)) ≤ Real.exp (-c*(M t:ℝ)) := by
    calc
      _ ≤ Real.exp (-(ε^2/(2*K^2))*((M t-1:ℕ):ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hsq
          (neg_nonpos.mpr (Nat.cast_nonneg (M t-1) : (0:ℝ) ≤ ((M t-1:ℕ):ℝ)))) (by positivity : 0 ≤ 2*K^2)
        exact hh.trans_eq (by ring)
      _ ≤ Real.exp (-((ε^2/(2*K^2))/2)*(M t:ℝ)) :=
        Probability.exp_neg_rivals_le_population htM (by positivity)
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hcε (Nat.cast_nonneg (M t) : (0:ℝ) ≤ M t)])
  have h0 := mul_le_mul_of_nonneg_left he₀ (by norm_num : (0:ℝ) ≤ 3)
  have h1 := mul_le_mul_of_nonneg_left he₁ (by positivity : (0:ℝ) ≤ 2*Real.exp 8)
  nlinarith

theorem payOnce_inactive_derivative_phi_mean_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ) {β : ℝ}
    (hb : Tendsto b atTop (𝓝 β))
    (hβ : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < β) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let Q := fun t => coverage (k+1) (C t) hn (μ t)
    Tendsto (fun t => Real.sqrt (M t:ℝ)*(b t*deriv (Q t) (b t)-
      ∫ r, phi (k+1) (allocation (k+1) (C t) hn r (b t)) ∂μ t)) atTop (𝓝 0) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage (k+1) (C t) hn (μ t)
  let ε := (β-L)/2
  have hε : 0 < ε := by dsimp only [ε,L]; linarith
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hgap := (hb.sub hbar).eventually_const_lt (show ε < β-L by dsimp only [ε]; linarith)
  obtain ⟨q,d,hq,hd,hown⟩ := payOnce_inactive_ownImpact_moments Γ B F g ρ h
  obtain ⟨A,c,hA,hc,hzero⟩ := payOnce_inactive_above_entry_zero_exponential Γ B F g ρ h hε
  let W := ((k+1:ℕ):ℝ)^3/q
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hinv : Tendsto (fun t => 2*W/Real.sqrt (M t:ℝ)) atTop (𝓝 0) := by
    have hh := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp h.population_grows))).const_mul (2*W)
    simpa only [mul_zero,div_eq_mul_inv,Function.comp_def] using hh
  have he₀ := Probability.tendsto_sqrt_nat_mul_exp_neg_mul M h.population_grows (by positivity : 0 < d/2)
  have he₁ := Probability.tendsto_sqrt_nat_mul_exp_neg_mul M h.population_grows hc
  have hboundlim : Tendsto (fun t => ((k+1:ℕ):ℝ)^2*(2*W/Real.sqrt (M t:ℝ)+
      3*(Real.sqrt (M t:ℝ)*Real.exp (-(d/2)*(M t:ℝ)))+
      A*(Real.sqrt (M t:ℝ)*Real.exp (-c*(M t:ℝ))))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using ((hinv.add (he₀.const_mul 3)).add (he₁.const_mul A)).const_mul (((k+1:ℕ):ℝ)^2)
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ hboundlim
  filter_upwards [hown,hzero,hgap,hbar.eventually_const_lt hL,h.population_grows.eventually_ge_atTop 2]
    with t ht hz hbt hLt htM
  have hbbar : bar t+ε ≤ b t := by linarith
  have hbp : 0 < b t := by linarith
  obtain ⟨w,hw,hwb,_hgap,_hLp,hder,hwm⟩ := ht.2 (b t) hbp
  have hderiv : b t*deriv (Q t) (b t) = ∫ r, weightedSlope (k+1) (allocation (k+1) (C t) hn r (b t)) (w r) ∂μ t := by
    rw [hder.deriv]
    exact mul_div_cancel₀ _ hbp.ne'
  have hcmp := integral_weightedSlope_sub_phi_le (μ t) hn
    (measurable_allocation_fixed_bid (c := C t) hn (b t)) hw (fun r => allocation_bounds hn r (b t)) hwb
  have hwmean := (hwm 1).2
  simp only [pow_one] at hwmean
  have heW : ((k+1:ℕ):ℝ)^3/(q*((M t-1:ℕ):ℝ))=W/((M t-1:ℕ):ℝ) := by dsimp only [W]; ring
  rw [heW] at hwmean
  have hwscaled : Real.sqrt (M t:ℝ)*(∫ r, w r ∂μ t) ≤
      2*W/Real.sqrt (M t:ℝ)+3*(Real.sqrt (M t:ℝ)*Real.exp (-(d/2)*(M t:ℝ))) := by
    have h0 := mul_le_mul_of_nonneg_left (Probability.sqrt_population_div_rivals_le htM) hW
    have h1 := mul_le_mul_of_nonneg_left (Probability.exp_neg_rivals_le_population htM hd.le)
      (Real.sqrt_nonneg (M t:ℝ))
    have hh := mul_le_mul_of_nonneg_left hwmean (Real.sqrt_nonneg (M t:ℝ))
    simp only [div_eq_mul_inv] at h0 h1 hh ⊢
    nlinarith
  have hzscaled := mul_le_mul_of_nonneg_left (hz (b t) hbbar) (Real.sqrt_nonneg (M t:ℝ))
  have hh := mul_le_mul_of_nonneg_left hcmp (Real.sqrt_nonneg (M t:ℝ))
  change |Real.sqrt (M t:ℝ)*(b t*deriv (Q t) (b t)-_)| ≤ _
  rw [hderiv,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h0 := mul_le_mul_of_nonneg_left hwscaled (sq_nonneg (((k+1:ℕ):ℝ)))
  have h1 := mul_le_mul_of_nonneg_left hzscaled (sq_nonneg (((k+1:ℕ):ℝ)))
  nlinarith

end FCAppendix.Bayes
