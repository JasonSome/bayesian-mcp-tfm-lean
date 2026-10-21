import FCAppendix.Affine.Uniform06.EntrySourceGap

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntrySourceLower
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.ExponentialTilt
open EntrySequence EntrySequence.Source EntrySourceRatios EntrySourceGap
open EntryEarlySourceLimits EntryRawModerate EntryGoodModerate EntryReciprocalLimit
open EntryLiteralResponseMoments EntryLiteralCanonicalTransfer
open scoped BigOperators

def SubexponentialLower (N : ℕ → ℕ) (F : ℕ → ℝ) : Prop :=
  ∀ ε>0,∀ᶠ m in atTop,Real.exp (-ε*(N m:ℝ))≤ F m

lemma polynomial_subexponential (N : ℕ → ℕ) (hNp : ∀ m,0< N m)
    (hN : Tendsto N atTop atTop) (F α : ℕ → ℝ)
    (hα : Tendsto α atTop (𝓝 0)) {c : ℝ} (hc : 0< c) (d : ℕ)
    (hlower : ∀ᶠ m in atTop,c*Real.exp (-α m*(N m:ℝ))/(N m:ℝ)^d≤ F m) :
    SubexponentialLower N F := by
  intro ε hε
  have he : Tendsto (fun m => (N m:ℝ)^d*Real.exp (-(ε/2)*(N m:ℝ))) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d:ℝ) (ε/2)
      (by positivity)).comp (tendsto_natCast_atTop_atTop.comp hN)
    simpa only [Function.comp_def,Real.rpow_natCast] using hh
  filter_upwards [hlower,hα.eventually (Iio_mem_nhds (show 0<ε/2 by positivity)),
    he.eventually (Iio_mem_nhds hc)] with m hm hαm hem
  have hn : (0:ℝ)< N m := Nat.cast_pos.mpr (hNp m)
  have hex : Real.exp (-(ε-α m)*(N m:ℝ))≤ Real.exp (-(ε/2)*(N m:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpoly : (N m:ℝ)^d*Real.exp (-(ε-α m)*(N m:ℝ))≤ c :=
    (mul_le_mul_of_nonneg_left hex (pow_nonneg hn.le d)).trans hem.le
  have hmul := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos (-α m*(N m:ℝ))).le
  have hexp : Real.exp (-α m*(N m:ℝ))*Real.exp (-(ε-α m)*(N m:ℝ))=
      Real.exp (-ε*(N m:ℝ)) := by
    rw [← Real.exp_add,show -α m*(N m:ℝ)+(-(ε-α m)*(N m:ℝ))= -ε*(N m:ℝ) by ring]
  have hfinite : Real.exp (-ε*(N m:ℝ))≤ c*Real.exp (-α m*(N m:ℝ))/(N m:ℝ)^d := by
    apply (le_div_iff₀ (pow_pos hn d)).mpr
    have hid : Real.exp (-α m*(N m:ℝ))*((N m:ℝ)^d*
        Real.exp (-(ε-α m)*(N m:ℝ)))=(N m:ℝ)^d*Real.exp (-ε*(N m:ℝ)) := by
      rw [mul_left_comm,hexp]
    rw [hid] at hmul
    simpa only [mul_comm] using hmul
  exact hfinite.trans hm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {i : Row} (s : Source μ i)

lemma constant_positive : 0< limitConstant μ i s.value := by
  have hv := limitingVariance_positive μ i s.value s.bid s.value_measurable s.bid_measurable
    s.value_law s.admissible s.active s.focal s.focal_pos s.focal_le_cutoff s.focal_tendsto
  exact div_pos (mul_pos (div_pos (gaussianPDFReal_pos 0 1 0 (by norm_num))
    (Real.sqrt_pos.mpr hv)) (EntryModerateWindow.peak_constant_pos
      (sub_pos.mpr (cutoff_lt_one i))))
    (eligibleHMean_positive μ i s.value s.value_measurable s.value_law)

theorem moderate_first (hm : Tendsto (fun m => -s.center m) atTop atTop) :
    SubexponentialLower s.rivals s.first := by
  let θ := theta μ i s.value s.bid s.focal s.population
  let Q := commonFactor μ i s.value s.bid s.focal s.population
  let C := limitConstant μ i s.value*(1/(entry i*reciprocalMean μ i s.value))
  have hκ := reciprocalMean_positive μ i s.value s.value_measurable s.value_law
  have hC : 0< C := mul_pos (constant_positive s)
    (one_div_pos.mpr (mul_pos (EarlyMean.entry_pos i) hκ))
  have ht := original_moderate_tilt μ i s.value s.bid s.value_measurable s.bid_measurable
    s.value_law s.admissible s.active s.focal s.focal_pos s.focal_le_cutoff s.focal_tendsto
    s.population s.population_ge_four s.population_tendsto hm
  have hmoment (k : ℕ) (hk : k≤2) :
      Tendsto (fun m => (s.rivals m:ℝ)^(k+1)*θ m^(k+2)*
        (∫ x,EntryUntilting.deficitMoment k (s.response m x) ∂s.law m)/Q m) atTop
          (𝓝 (limitConstant μ i s.value*(1/(entry i*reciprocalMean μ i s.value))^k*
            (Nat.factorial k:ℝ))) :=
    EntryLiteralModerate.original_moderate_response_moments μ i s.value s.bid
      s.value_measurable s.bid_measurable s.value_law s.admissible s.active s.focal
      s.focal_le_cutoff s.focal_tendsto s.guards s.multiplier_tendsto s.population
      s.population_ge_four s.population_tendsto s.epsilon_pos s.lowerPrice_lt_entry
      s.stripBid s.demandMargin s.weightMargin s.seedMargin s.cap s.finite hm hk
  have hraw : Tendsto (fun m => (s.rivals m:ℝ)^2*θ m^3*
      (∫ x,EntryUntilting.deficitMoment 1 (s.response m x) ∂s.law m)/Q m) atTop (𝓝 C) := by
    simpa only [show (1:ℕ)+1=2 by norm_num,show (1:ℕ)+2=3 by norm_num,
      pow_one,Nat.factorial_one,Nat.cast_one,mul_one] using hmoment 1 (by norm_num)
  have hscaled : Tendsto (fun m => (s.rivals m:ℝ)^2*θ m^3*s.first m/Q m) atTop (𝓝 C) := by
    simpa only [(source_moment_integrals s _).2.1] using hraw
  apply polynomial_subexponential s.rivals s.rivals_pos s.rivals_tendsto s.first θ ht.2.1
    (c := C/2) (by positivity) 2
  filter_upwards [hscaled.eventually (Ioi_mem_nhds (show C/2< C by linarith))] with m hm
  have hθ := EntryOriginalModerate.theta_bounds μ i s.value s.bid s.focal s.population m
  have hQ : 0< Q m := commonFactor_positive μ i s.value s.bid s.focal s.population m
  have hQL : Real.exp (-θ m*(s.rivals m:ℝ))≤ Q m :=
    EntryGoodEvent.actual_untilt_factor_lower (s.raw m)
      (RawMixedSource.demand (xi i) (s.focal m)) (RawMixedSource.measurable_demand _ _)
      (ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) (s.focal_pos m))) (s.rivals m)
      hθ.1 (Nat.cast_nonneg (capacity (s.population m)))
  have hnum : (C/2)*Q m≤(s.rivals m:ℝ)^2*θ m^3*s.first m :=
    (le_div_iff₀ hQ).mp hm.le
  have hp3 : θ m^3≤1 := by simpa using pow_le_pow_left₀ hθ.1 hθ.2.le 3
  have hnum' : (s.rivals m:ℝ)^2*θ m^3*s.first m≤(s.rivals m:ℝ)^2*s.first m := by
    have hh := mul_le_mul_of_nonneg_left hp3 (mul_nonneg (sq_nonneg (s.rivals m:ℝ)) (s.first_nonneg m))
    nlinarith
  apply (div_le_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr (s.rivals_pos m)))).mpr
  have hh := mul_le_mul_of_nonneg_left hQL (show 0≤ C/2 by positivity)
  nlinarith

lemma sqrt_le_nat (n : ℕ) (hn : 0< n) : Real.sqrt (n:ℝ)≤ n := by
  have h1 : (1:ℝ)≤ n := by exact_mod_cast hn
  nlinarith [Real.sqrt_nonneg (n:ℝ),Real.sq_sqrt (Nat.cast_nonneg n),sq_nonneg ((n:ℝ)-1)]

theorem central_first {z : ℝ} (hz : Tendsto s.center atTop (𝓝 z)) :
    SubexponentialLower s.rivals s.first := by
  let α := Real.sqrt (limitingVariance μ i s.value)
  let β := eligibleHMean μ i s.value*Real.sqrt (1-cutoff i)
  let κ := reciprocalMean μ i s.value
  let C := EntryCentralRatio.firstMoment α β z/(entry i*κ)
  have hv := limitingVariance_positive μ i s.value s.bid s.value_measurable s.bid_measurable
    s.value_law s.admissible s.active s.focal s.focal_pos s.focal_le_cutoff s.focal_tendsto
  have hα : 0<α := Real.sqrt_pos.mpr hv
  have hκ : 0<κ := reciprocalMean_positive μ i s.value s.value_measurable s.value_law
  have hC : 0< C := div_pos (EntryCentralRatio.first_second_moment_pos hα β z).1
    (mul_pos (EarlyMean.entry_pos i) hκ)
  have hm := original_central_response_moments μ i s.value s.bid s.value_measurable
    s.bid_measurable s.value_law s.admissible s.active s.focal s.focal_le_cutoff
    s.focal_tendsto s.guards s.multiplier_tendsto s.population s.population_ge_four
    s.population_tendsto s.epsilon_pos s.lowerPrice_lt_entry s.stripBid s.demandMargin
    s.weightMargin s.seedMargin s.cap s.finite hz
  have hcentral : Tendsto (fun m => ∫ x,Real.sqrt (s.rivals m:ℝ)*s.response m x ∂s.law m)
      atTop (𝓝 C) := hm.2.1
  have hscaled : Tendsto (fun m => Real.sqrt (s.rivals m:ℝ)*s.first m) atTop (𝓝 C) := by
    simpa only [integral_const_mul,(s.canonical_integrals _).1] using hcentral
  apply polynomial_subexponential s.rivals s.rivals_pos s.rivals_tendsto s.first
    (fun _ => 0) tendsto_const_nhds (c := C/2) (by positivity) 1
  filter_upwards [hscaled.eventually (Ioi_mem_nhds (show C/2< C by linarith))] with m hm
  simp only [neg_zero,zero_mul,Real.exp_zero,mul_one,pow_one]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (s.rivals_pos m))).mpr
  have hh := mul_le_mul_of_nonneg_right (sqrt_le_nat _ (s.rivals_pos m)) (s.first_nonneg m)
  nlinarith

theorem above_first (hpos : ∀ m,0< s.center m) (ha : Tendsto s.center atTop atTop) :
    SubexponentialLower s.rivals s.first := by
  let δ := fun m => EntryRawAbove.delta i (s.jointLaw m) (s.rivals m)
    (capacity (s.population m)) (s.focal m)
  let a := 1/(entry i*reciprocalMean μ i s.value)
  have ha0 : 0< a := one_div_pos.mpr (mul_pos (EarlyMean.entry_pos i)
    (reciprocalMean_positive μ i s.value s.value_measurable s.value_law))
  have hδ (m) : 0<δ m := by
    have hh := hpos m
    change 0<δ m/Real.sqrt (s.rivals m:ℝ) at hh
    exact (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (s.rivals_pos m)))).mp hh
  have hm := EntryLiteralAbove.original_above_canonical_ratio μ i s.value s.bid
    s.value_measurable s.bid_measurable s.value_law s.admissible s.active s.focal
    s.focal_le_cutoff s.focal_tendsto s.guards s.multiplier_tendsto s.population
    s.population_ge_four s.population_tendsto s.epsilon_pos s.lowerPrice_lt_entry
    s.stripBid s.demandMargin s.weightMargin s.seedMargin s.cap s.finite hδ ha
  have hscaled : Tendsto (fun m => ((s.rivals m:ℝ)/(δ m*a))*s.first m) atTop (𝓝 1) := hm.2.2.2.2
  apply polynomial_subexponential s.rivals s.rivals_pos s.rivals_tendsto s.first
    (fun _ => 0) tendsto_const_nhds (c := a/2) (by positivity) 1
  filter_upwards [hscaled.eventually (Ioi_mem_nhds (by norm_num : (1/2:ℝ)<1)),
    ha.eventually_ge_atTop 1] with m hm hcent
  have hn : (0:ℝ)< s.rivals m := Nat.cast_pos.mpr (s.rivals_pos m)
  have hδ1 : 1≤δ m := by
    have hs1 : (1:ℝ)≤ Real.sqrt (s.rivals m:ℝ) := by
      have hN1 : (1:ℝ)≤ s.rivals m := by exact_mod_cast s.rivals_pos m
      nlinarith [Real.sqrt_nonneg (s.rivals m:ℝ),Real.sq_sqrt hn.le]
    change 1≤δ m/Real.sqrt (s.rivals m:ℝ) at hcent
    have hh := (le_div_iff₀ (Real.sqrt_pos.mpr hn)).mp hcent
    nlinarith
  have hnum : (δ m*a)/2≤(s.rivals m:ℝ)*s.first m := by
    have hh : (1/2:ℝ)≤((s.rivals m:ℝ)*s.first m)/(δ m*a) := by
      convert! hm.le using 1; ring
    have hh' := (le_div_iff₀ (mul_pos (hδ m) ha0)).mp hh
    linarith
  simp only [neg_zero,zero_mul,Real.exp_zero,mul_one,pow_one]
  apply (div_le_iff₀ hn).mpr
  nlinarith [mul_le_mul_of_nonneg_right hδ1 ha0.le]

theorem first_subexponential : SubexponentialLower s.rivals s.first := by
  intro ε hε
  apply eventually_of_every_subsequence
  intro ψ hψ
  let t := s.reindex ψ hψ
  obtain ⟨φ,hφ,hreg⟩ := three_regime_exhaustion t.center
  let u := t.reindex φ hφ.tendsto_atTop
  refine ⟨φ,hφ,?_⟩
  rcases hreg with hm | hc | ha
  · exact moderate_first u hm ε hε
  · obtain ⟨z,hz⟩ := hc
    exact central_first u hz ε hε
  · exact above_first u ha.1 ha.2 ε hε

end FCAppendix.Affine.Uniform06.EntrySourceLower
