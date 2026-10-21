import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalLimitSlope

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology
namespace Physical

theorem eventually_raw_crossover_optimizer_rent
    {row : Uniform07.Row} {market : ℕ→ℕ} {Seed : ℕ→ Type*}
    [∀ k, MeasurableSpace (Seed k)]
    (Γ : ∀ k, FiniteGame (market k) 2 (Uniform07.capacity (market k)) (Seed k))
    (i : ∀ k, Fin (market k)) (B : ∀ k, CanonicalEvent (Γ k))
    {L R U Amin Amax Rmax Dmax : ℝ} {A : ℝ→ℝ}
    (P : ∀ k, BroadcastLaw05 (Γ k) (Uniform07.cutoff row) U)
    {e19 e ell eS eD : ℕ→ℝ}
    (hmarket : Tendsto market atTop atTop)
    (hAmin : 0< Amin) (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax)
    (hSchedule : ∀ k, (Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ k, (Γ k).g=0)
    (hdata : ∀ᶠ k in atTop,
      Nonempty (RemoteKernels06 row (Γ k) (i k) (B k) L R U (P k) A
        Amin Amax Rmax Dmax (e19 k) (e k) (ell k)) ∧
      Nonempty (PureDerivativeBounds06 (Γ k) (i k) (B k) (Uniform07.cutoff row) L R (eS k) (eD k)))
    (hpositive : ∀ᶠ k in atTop, 0≤ e19 k ∧ 0≤ e k ∧ 0< ell k ∧ 0≤ eS k ∧ 0≤ eD k)
    (he19 : Tendsto e19 atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (heS : Tendsto eS atTop (𝓝 0)) (heD : Tendsto eD atTop (𝓝 0))
    (hduplicateRent : Tendsto (fun k => eD k/((market k:ℝ)*L*ell k/2)) atTop (𝓝 0))
    (v : ℕ→ℝ) (a : ℕ→ JointAction 2)
    (haroute : ∀ k, (a k).routeCount=1) (hunderbid : ∀ k, (a k).bid≤ v k)
    (hopt : ∀ k, ∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ U →
      (problem (Γ k) (i k)).payoff (v k) a'≤(problem (Γ k) (i k)).payoff (v k) (a k))
    {b0 : ℝ} (hb0 : b0∈Ioo L R)
    (hbid : Tendsto (fun k => (a k).bid) atTop (𝓝 b0)) :
    ∀ epsilon∈Ioo (0:ℝ) 1, ∀ᶠ k in atTop,
      (1-epsilon)/referenceSlope (market k) A (a k).bid≤ v k-(a k).bid := by
  intro epsilon hepsilon
  obtain ⟨k₀,hk₀⟩ := hdata.exists
  obtain ⟨E₀⟩ := hk₀.1
  let L' : ℝ := (L+b0)/2
  let middle : ℝ := (L'+b0)/2
  let a0 : ℝ := Amin/2
  let sigma : ℝ := epsilon/16
  let omega : ℝ := sigma*a0/4
  let W : ℝ := epsilon/(4*a0)
  have hLL' : L< L' := by dsimp [L']; linarith [hb0.1]
  have hL'b0 : L'< b0 := by dsimp [L']; linarith [hb0.1]
  have hmid : L'< middle ∧ middle< b0 := by dsimp [middle]; constructor <;> linarith
  have ha0 : 0< a0 := by dsimp [a0]; positivity
  have hsigma : 0< sigma := div_pos hepsilon.1 (by norm_num)
  have hsigma1 : sigma<1 := by dsimp [sigma]; linarith [hepsilon.2]
  have homega : 0< omega := by dsimp [omega]; positivity
  have hW : 0< W := div_pos hepsilon.1 (mul_pos (by norm_num) ha0)
  have hlog := eventually_actual_crossover_log_slope Γ i B P hmarket hAmin hRmax hDmax
    hSchedule hFee hdata hpositive he19 he heS heD hduplicateRent sigma ⟨hsigma,hsigma1⟩ L' hLL' (hL'b0.trans hb0.2).le
  have hAUC : UniformContinuousOn A (Icc L R) :=
    isCompact_Icc.uniformContinuousOn_of_continuous E₀.rateContinuous
  have hmod := hmarket.eventually (eventually_shrinking_interval_modulus hAUC hW.le
    (by norm_num : (0:ℝ)<1) omega homega)
  have hcast : Tendsto (fun k => (market k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmarket
  have hwidth : Tendsto (fun k => W/(market k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hwidthSmall := hwidth.eventually (Iio_mem_nhds (sub_pos.mpr hmid.1))
  have hbidI := hbid.eventually (Ioo_mem_nhds hmid.2 hb0.2)
  have h19small := he19.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< min (Amin/4) (omega/2)))
  have hesmall := he.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdata,hpositive,hlog,hmod,hwidthSmall,hbidI,h19small,hesmall,
    hmarket.eventually (eventually_ge_atTop 1)]
    with k hdk hpk hlogk hmodk hwk hbk h19k hek hmk
  obtain ⟨E⟩ := hdk.1
  have hm : 1≤(market k:ℝ) := by exact_mod_cast hmk
  have hm0 : 0<(market k:ℝ) := by linarith
  rcases hpk with ⟨h190,he0,_,_,_⟩
  have hbI : (a k).bid∈Icc L R := ⟨hLL'.le.trans (hmid.1.le.trans hbk.1.le),hbk.2.le⟩
  have hbJ : (a k).bid∈Icc L' R := ⟨hmid.1.le.trans hbk.1.le,hbk.2.le⟩
  have h19A : e19 k≤ Amin/4 := (lt_min_iff.mp h19k).1.le
  have halower : a0*(market k:ℝ)≤ referenceSlope (market k) A (a k).bid :=
    (by
      have hh := E.reference_slope_lower hm0 hbI
      dsimp [a0]
      nlinarith)
  have ha : 0< referenceSlope (market k) A (a k).bid := (mul_pos ha0 hm0).trans_le halower
  let step : ℝ := (epsilon/4)/referenceSlope (market k) A (a k).bid
  have hstep0 : 0< step := div_pos (div_pos hepsilon.1 (by norm_num)) ha
  have hstepUpper : step≤ W/(market k:ℝ) := by
    have h := div_le_div_of_nonneg_left
      (show (0:ℝ)≤epsilon/4 from div_nonneg hepsilon.1.le (by norm_num))
      (mul_pos ha0 hm0) halower
    calc
      _ ≤ (epsilon/4)/(a0*(market k:ℝ)) := h
      _ = _ := by dsimp [W]; ring
  have hstep : L'≤(a k).bid-step := by linarith [hbk.1,hstepUpper,hwk,hmid.1]
  have hleftI : (a k).bid-step∈Icc L R := ⟨hLL'.le.trans hstep,by linarith [hbk.2]⟩
  have hfreeze : ∀ z∈Icc ((a k).bid-step) (a k).bid,
      referenceSlope (market k) A z≤(1+sigma)*referenceSlope (market k) A (a k).bid := by
    intro z hz
    have hzI : z∈Icc L R := ⟨hleftI.1.trans hz.1,hz.2.trans hbk.2.le⟩
    have hdist : (a k).bid-z≤ W/((1:ℝ)*(market k:ℝ)) := by simpa only [one_mul] using
      (show (a k).bid-z≤ W/(market k:ℝ) by linarith [hz.1,hstepUpper])
    have hosc := hmodk z hzI (a k).bid hbI hz.2 hdist
    apply finite_uniform_slope_freeze (a := referenceSlope (market k) A) (A := A)
      (a0 := a0) (osc := omega) (e := 0) hm0 (by norm_num) hsigma.le
      (by simp [referenceSlope,hm0.ne']) (by simp [referenceSlope,hm0.ne'])
      (by simpa only [abs_sub_comm] using hosc.le) halower
    dsimp [omega]
    nlinarith
  have hqAC := actual_marginal_ac (Γ k) (i k)
    (by rw [min_eq_left E.interval]; exact E.bid0.le) E.successAC E.duplicateAC
  have hsub : uIcc ((a k).bid-step) (a k).bid ⊆ uIcc L R := by
    rw [uIcc_of_le (by linarith : (a k).bid-step≤(a k).bid),uIcc_of_le E.interval]
    exact fun z hz => ⟨hleftI.1.trans hz.1,hz.2.trans hbk.2.le⟩
  have hslope : ∀ᵐ z ∂(volume : Measure ℝ), z∈Icc ((a k).bid-step) (a k).bid →
      deriv (q (Γ k) (i k)) z≤((1+epsilon/4)*referenceSlope (market k) A (a k).bid)*q (Γ k) (i k) z := by
    filter_upwards [hlogk] with z hz hzI
    have hzJ : z∈Icc L' R := ⟨hstep.trans hzI.1,hzI.2.trans hbk.2.le⟩
    have hq0 := q_nonneg (Γ k) (i k) z
    have hfr := mul_le_mul_of_nonneg_right (hfreeze z hzI) hq0
    have hfr' := mul_le_mul_of_nonneg_left hfr (by positivity : 0≤ 1+sigma)
    have hcoef : (1+sigma)*(1+sigma)≤ 1+epsilon/4 := by
      dsimp [sigma]
      nlinarith [mul_nonneg hepsilon.1.le (sub_nonneg.mpr hepsilon.2.le)]
    have hcoef' := mul_le_mul_of_nonneg_right hcoef (mul_nonneg ha.le hq0)
    nlinarith [hz hzJ]
  have hscalar := raw_singleton_optimum_scalar_below (Γ k) (hFee k) (i k) (v k) U (a k) (haroute k) (hopt k)
  exact singleton_relative_rent_of_integrated_slope ha hepsilon.1 hepsilon.2 (hunderbid k)
    (E.actual_marginal_positive hm he0 hek hleftI)
    (hscalar _ ⟨E.bid0.le.trans hleftI.1,hleftI.2.trans E.feasible⟩) (hqAC.mono hsub) hslope

theorem referencePaymentError_tendsto
    {e19 : ℕ → ℝ} (he19 : Tendsto e19 atTop (𝓝 0)) (Amin : ℝ) :
    Tendsto (fun k => ReferencePaymentError Amin (e19 k)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [ReferencePaymentError,add_zero,mul_zero,zero_div,mul_one,sub_self] using
    ((h1.add he19).mul
      (h1.add ((he19.const_mul 2).div_const Amin))).sub h1

theorem actualPaymentBudget_tendsto
    {e19 e : ℕ→ℝ} (he19 : Tendsto e19 atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (eta xi Amax : ℝ) :
    Tendsto (fun k => actualPaymentBudget eta xi Amax (e19 k) (e k)) atTop (𝓝 (2*eta/xi)) := by
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hmax : Tendsto (fun _ : ℕ => Amax) atTop (𝓝 Amax) := tendsto_const_nhds
  have hnum := ((h1.add he19).const_mul (2*eta/xi)).add
    ((he.const_mul eta).mul (hmax.add he19))
  have hden := h1.sub he
  have ht := hnum.div hden (by norm_num : (1:ℝ)-0≠0)
  change Tendsto (fun k => (2*eta/xi*(1+e19 k)+eta*e k*(Amax+e19 k))/(1-e k))
    atTop (𝓝 ((2*eta/xi*(1+0)+eta*0*(Amax+0))/(1-0))) at ht
  simpa only [actualPaymentBudget,add_zero,mul_one,mul_zero,zero_mul,sub_zero,div_one] using
    ht

theorem duplicate_ratio_bound_tendsto
    {market : ℕ→ℕ} {e : ℕ→ℝ} (hmarket : Tendsto market atTop atTop)
    (he : Tendsto e atTop (𝓝 0)) (Rmax : ℝ) :
    Tendsto (fun k => (Rmax+e k)/((market k:ℝ)*(1-e k))) atTop (𝓝 0) := by
  have hn : Tendsto (fun k => (Rmax+e k)/(1-e k)) atTop (𝓝 Rmax) := by
    have hmax : Tendsto (fun _ : ℕ => Rmax) atTop (𝓝 Rmax) := tendsto_const_nhds
    have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have ht := (hmax.add he).div (h1.sub he) (by norm_num : (1:ℝ)-0≠0)
    change Tendsto (fun k => (Rmax+e k)/(1-e k)) atTop (𝓝 ((Rmax+0)/(1-0))) at ht
    simpa only [add_zero,sub_zero,div_one] using
      ht
  have hm : Tendsto (fun k => (market k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmarket
  convert hn.div_atTop hm using 1
  ext k
  rw [div_div,mul_comm]

theorem eventually_raw_crossover_optimizer_relative_route_gap
    {row : Uniform07.Row} {market : ℕ→ℕ} {Seed : ℕ→ Type*}
    [∀ k, MeasurableSpace (Seed k)]
    (Γ : ∀ k, FiniteGame (market k) 2 (Uniform07.capacity (market k)) (Seed k))
    (i : ∀ k, Fin (market k)) (B : ∀ k, CanonicalEvent (Γ k))
    {L R U Amin Amax Rmax Dmax : ℝ} {A : ℝ→ℝ}
    (P : ∀ k, BroadcastLaw05 (Γ k) (Uniform07.cutoff row) U)
    {e19 e ell eS eD : ℕ→ℝ}
    (hmarket : Tendsto market atTop atTop)
    (hAmin : 0< Amin) (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax)
    (hSchedule : ∀ k, (Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ k, (Γ k).g=0)
    (hdata : ∀ᶠ k in atTop,
      Nonempty (RemoteKernels06 row (Γ k) (i k) (B k) L R U (P k) A
        Amin Amax Rmax Dmax (e19 k) (e k) (ell k)) ∧
      Nonempty (PureDerivativeBounds06 (Γ k) (i k) (B k) (Uniform07.cutoff row) L R (eS k) (eD k)))
    (hpositive : ∀ᶠ k in atTop, 0≤ e19 k ∧ 0≤ e k ∧ 0< ell k ∧ 0≤ eS k ∧ 0≤ eD k)
    (he19 : Tendsto e19 atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (heS : Tendsto eS atTop (𝓝 0)) (heD : Tendsto eD atTop (𝓝 0))
    (hduplicateRent : Tendsto (fun k => eD k/((market k:ℝ)*L*ell k/2)) atTop (𝓝 0))
    (v : ℕ→ℝ) (a : ℕ→ JointAction 2)
    (haroute : ∀ k, (a k).routeCount=1) (hunderbid : ∀ k, (a k).bid≤ v k)
    (hopt : ∀ k, ∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ U →
      (problem (Γ k) (i k)).payoff (v k) a'≤(problem (Γ k) (i k)).payoff (v k) (a k))
    {b0 : ℝ} (hb0 : b0∈Ioo L R)
    (hbid : Tendsto (fun k => (a k).bid) atTop (𝓝 b0)) :
    ∀ zeta>0, ∀ᶠ k in atTop,
      (1-2*Uniform07.eta row/Uniform07.xi row-zeta)*
          q (Γ k) (i k) (a k).bid/referenceSlope (market k) A (a k).bid≤
        (problem (Γ k) (i k)).payoff (v k) (LowBody.addSecondRoute (a k))-
          (problem (Γ k) (i k)).payoff (v k) (a k) := by
  intro zeta hzeta
  let epsilon : ℝ := min (zeta/4) (1/2)
  have hepsilon0 : 0< epsilon := by dsimp [epsilon]; positivity
  have hepsilon1 : epsilon<1 := by
    have h := min_le_right (zeta/4) (1/2:ℝ)
    dsimp [epsilon]
    linarith
  have hepsilonZ : epsilon< zeta :=
    (min_le_left (zeta/4) (1/2:ℝ)).trans_lt (by linarith)
  have hrent := eventually_raw_crossover_optimizer_rent Γ i B P hmarket hAmin hRmax hDmax
    hSchedule hFee hdata hpositive he19 he heS heD hduplicateRent v a haroute hunderbid hopt hb0 hbid
    epsilon ⟨hepsilon0,hepsilon1⟩
  have hpayment := actualPaymentBudget_tendsto (referencePaymentError_tendsto he19 Amin) he
    (Uniform07.eta row) (Uniform07.xi row) Amax
  have hratio := duplicate_ratio_bound_tendsto hmarket he Rmax
  have hcoef : Tendsto (fun k =>
      (1-epsilon)*(1-(Rmax+e k)/((market k:ℝ)*(1-e k)))-
        actualPaymentBudget (Uniform07.eta row) (Uniform07.xi row) Amax (ReferencePaymentError Amin (e19 k)) (e k))
      atTop (𝓝 (1-epsilon-2*Uniform07.eta row/Uniform07.xi row)) := by
    have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_zero,mul_one] using
      ((h1.sub hratio).const_mul (1-epsilon)).sub hpayment
  have hcoefGood := hcoef.eventually (Ioi_mem_nhds
    (show 1-2*Uniform07.eta row/Uniform07.xi row-zeta<
      1-epsilon-2*Uniform07.eta row/Uniform07.xi row by linarith))
  have hbidGood := hbid.eventually (Ioo_mem_nhds hb0.1 hb0.2)
  have h19Good := he19.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< Amin/4))
  have heGood := he.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hrent,hcoefGood,hbidGood,h19Good,heGood,hdata,hpositive,
    hmarket.eventually (eventually_ge_atTop 1)] with k hr hk hb h19 hek hdk hpk hmk
  obtain ⟨E⟩ := hdk.1
  have hm : 1≤(market k:ℝ) := by exact_mod_cast hmk
  have hm0 : 0<(market k:ℝ) := by linarith
  rcases hpk with ⟨h190,he0,_,_,_⟩
  have hbI : (a k).bid∈Icc L R := ⟨hb.1.le,hb.2.le⟩
  have haPos := E.reference_slope_positive hm0 hAmin hbI
  have hqPos := E.actual_marginal_positive hm he0 hek hbI
  have hDq := E.actual_duplicate_ratio hm he0 hek hRmax hbI
  have hDpay := E.actual_duplicate_budget (hb0.1.trans hb0.2) hm hAmin h190 h19.le he0 hek hbI
  have hcoefActual : 1-2*Uniform07.eta row/Uniform07.xi row-zeta≤
      (1-epsilon)*(1-duplicate (Γ k) (i k) (a k).bid/q (Γ k) (i k) (a k).bid)-
        actualPaymentBudget (Uniform07.eta row) (Uniform07.xi row) Amax (ReferencePaymentError Amin (e19 k)) (e k) := by
    have h := mul_le_mul_of_nonneg_left hDq (sub_nonneg.mpr hepsilon1.le)
    linarith
  have hbound := route_gap_from_relative_rent haPos hqPos
    (duplicate_nonneg (Γ k) (i k) (a k).bid)
    (duplicate_le_q (Γ k) (i k) (a k).bid_nonneg) hepsilon1.le hr hDpay
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoefActual hqPos.le) haPos.le
  have hraw :
      (problem (Γ k) (i k)).payoff (v k) (LowBody.addSecondRoute (a k))-
          (problem (Γ k) (i k)).payoff (v k) (a k)=
        utilityTwo (Uniform07.eta row) (v k) (a k).bid
          (q (Γ k) (i k) (a k).bid) (duplicate (Γ k) (i k) (a k).bid)-
        utilityOne (v k) (a k).bid (q (Γ k) (i k) (a k).bid) := by
    rw [raw_route_difference (Γ k) (source_eta_mem row).1 (source_eta_mem row).2
      (hSchedule k) (hFee k) (i k) (v k) (a k) (haroute k)]
    exact (route_difference _ _ _ _ _).symm
  rw [hraw]
  exact hscaled.trans hbound

theorem source_route_margin_positive (row : Uniform07.Row) :
    0<1-2*Uniform07.eta row/Uniform07.xi row :=
  Uniform07.route_coefficient_pos row

theorem eventually_raw_crossover_optimizer_loses
    {row : Uniform07.Row} {market : ℕ→ℕ} {Seed : ℕ→ Type*}
    [∀ k, MeasurableSpace (Seed k)]
    (Γ : ∀ k, FiniteGame (market k) 2 (Uniform07.capacity (market k)) (Seed k))
    (i : ∀ k, Fin (market k)) (B : ∀ k, CanonicalEvent (Γ k))
    {L R U Amin Amax Rmax Dmax : ℝ} {A : ℝ→ℝ}
    (P : ∀ k, BroadcastLaw05 (Γ k) (Uniform07.cutoff row) U)
    {e19 e ell eS eD : ℕ→ℝ}
    (hmarket : Tendsto market atTop atTop)
    (hAmin : 0< Amin) (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax)
    (hSchedule : ∀ k, (Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ k, (Γ k).g=0)
    (hdata : ∀ᶠ k in atTop,
      Nonempty (RemoteKernels06 row (Γ k) (i k) (B k) L R U (P k) A
        Amin Amax Rmax Dmax (e19 k) (e k) (ell k)) ∧
      Nonempty (PureDerivativeBounds06 (Γ k) (i k) (B k) (Uniform07.cutoff row) L R (eS k) (eD k)))
    (hpositive : ∀ᶠ k in atTop, 0≤ e19 k ∧ 0≤ e k ∧ 0< ell k ∧ 0≤ eS k ∧ 0≤ eD k)
    (he19 : Tendsto e19 atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (heS : Tendsto eS atTop (𝓝 0)) (heD : Tendsto eD atTop (𝓝 0))
    (hduplicateRent : Tendsto (fun k => eD k/((market k:ℝ)*L*ell k/2)) atTop (𝓝 0))
    (v : ℕ→ℝ) (a : ℕ→ JointAction 2)
    (haroute : ∀ k, (a k).routeCount=1) (hunderbid : ∀ k, (a k).bid≤ v k)
    (hopt : ∀ k, ∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ U →
      (problem (Γ k) (i k)).payoff (v k) a'≤(problem (Γ k) (i k)).payoff (v k) (a k))
    {b0 : ℝ} (hb0 : b0∈Ioo L R)
    (hbid : Tendsto (fun k => (a k).bid) atTop (𝓝 b0)) :
    ∀ᶠ k in atTop, (problem (Γ k) (i k)).payoff (v k) (a k)<
      (problem (Γ k) (i k)).payoff (v k) (LowBody.addSecondRoute (a k)) := by
  let zeta : ℝ := (1-2*Uniform07.eta row/Uniform07.xi row)/2
  have hzeta : 0< zeta := by dsimp [zeta]; exact half_pos (source_route_margin_positive row)
  have hgap := eventually_raw_crossover_optimizer_relative_route_gap Γ i B P hmarket
    hAmin hRmax hDmax hSchedule hFee hdata hpositive he19 he heS heD hduplicateRent
    v a haroute hunderbid hopt hb0 hbid zeta hzeta
  have hbidGood := hbid.eventually (Ioo_mem_nhds hb0.1 hb0.2)
  have h19Good := he19.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< Amin/4))
  have heGood := he.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hgap,hbidGood,h19Good,heGood,hdata,hpositive,
    hmarket.eventually (eventually_ge_atTop 1)] with k hg hk h19 hek hdk hpk hmk
  obtain ⟨E⟩ := hdk.1
  have hm : 1≤(market k:ℝ) := by exact_mod_cast hmk
  have hm0 : 0<(market k:ℝ) := by linarith
  have hbI : (a k).bid∈Icc L R := ⟨hk.1.le,hk.2.le⟩
  have hqPos := E.actual_marginal_positive hm hpk.2.1 hek hbI
  have haPos := E.reference_slope_positive hm0 hAmin hbI
  have hmargin : 0<1-2*Uniform07.eta row/Uniform07.xi row-zeta := by
    dsimp [zeta]
    linarith [source_route_margin_positive row]
  exact sub_pos.mp ((div_pos (mul_pos hmargin hqPos) haPos).trans_le hg)

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
