import FCAppendix.Affine.Uniform06.EntrySequence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntrySourceRatios
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open EntrySequence EntrySequence.Source EntryUntilting EntryGoodVelocity
open EntryGoodModerate EntryRawModerate EntryEarlySourceLimits EntryReciprocalLimit
open scoped BigOperators

lemma moderate_root_ratio
    (N : ℕ → ℕ) (hNp : ∀ m,0< N m) (_hN : Tendsto N atTop atTop)
    (θ Q M0 M1 M2 : ℕ → ℝ) (hθ : ∀ᶠ m in atTop,0<θ m)
    (hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop)
    (hQ : ∀ m,0< Q m) {C a : ℝ} (hC : 0< C) (ha : 0< a)
    (h0 : Tendsto (fun m => (N m:ℝ)*θ m^2*M0 m/Q m) atTop (𝓝 C))
    (h1 : Tendsto (fun m => (N m:ℝ)^2*θ m^3*M1 m/Q m) atTop (𝓝 (C*a)))
    (h2 : Tendsto (fun m => (N m:ℝ)^3*θ m^4*M2 m/Q m) atTop (𝓝 (2*C*a^2))) :
    (∀ᶠ m in atTop,0< M0 m ∧ 0< M1 m ∧ 0< M2 m) ∧
      Tendsto (fun m => M1 m^2/(M0 m*M2 m)) atTop (𝓝 (1/2:ℝ)) ∧
      Tendsto (fun m => M1 m/M0 m) atTop (𝓝 0) := by
  have hpos : ∀ᶠ m in atTop,0< M0 m ∧ 0< M1 m ∧ 0< M2 m := by
    filter_upwards [hθ,h0.eventually (Ioi_mem_nhds hC),
      h1.eventually (Ioi_mem_nhds (mul_pos hC ha)),
      h2.eventually (Ioi_mem_nhds (show 0<2*C*a^2 by positivity))] with m hθm h0m h1m h2m
    have hn : (0:ℝ)< N m := Nat.cast_pos.mpr (hNp m)
    refine ⟨?_,?_,?_⟩
    · exact (mul_pos_iff_of_pos_left (by positivity : 0<(N m:ℝ)*θ m^2)).mp
        ((div_pos_iff_of_pos_right (hQ m)).mp h0m)
    · exact (mul_pos_iff_of_pos_left (by positivity : 0<(N m:ℝ)^2*θ m^3)).mp
        ((div_pos_iff_of_pos_right (hQ m)).mp h1m)
    · exact (mul_pos_iff_of_pos_left (by positivity : 0<(N m:ℝ)^3*θ m^4)).mp
        ((div_pos_iff_of_pos_right (hQ m)).mp h2m)
  have hratio := (h1.pow 2).div (h0.mul h2) (by positivity : C*(2*C*a^2)≠0)
  have hconstant : (C*a)^2/(C*(2*C*a^2))=(1/2:ℝ) := by
    field_simp [hC.ne',ha.ne']
  rw [hconstant] at hratio
  have hratio' : Tendsto (fun m => M1 m^2/(M0 m*M2 m)) atTop (𝓝 (1/2:ℝ)) := by
    apply hratio.congr'
    filter_upwards [hpos,hθ] with m hm hθm
    have hn : (N m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hNp m))
    change ((N m:ℝ)^2*θ m^3*M1 m/Q m)^2/
      ((N m:ℝ)*θ m^2*M0 m/Q m*((N m:ℝ)^3*θ m^4*M2 m/Q m))=M1 m^2/(M0 m*M2 m)
    field_simp [hn,hθm.ne',(hQ m).ne',hm.1.ne',hm.2.2.ne']
  have hθN' : Tendsto (fun m => (N m:ℝ)*θ m) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁ := fun m => θ m*Real.sqrt (N m:ℝ)) ?_ hθN
    filter_upwards [hθ] with m hm
    have hN1 : (1:ℝ)≤ N m := by exact_mod_cast hNp m
    have hs : Real.sqrt (N m:ℝ)≤ N m := by
      have hs0 := Real.sqrt_nonneg (N m:ℝ)
      have hs2 := Real.sq_sqrt (Nat.cast_nonneg (N m))
      nlinarith [sq_nonneg ((N m:ℝ)-1)]
    nlinarith [mul_le_mul_of_nonneg_left hs hm.le]
  have hquot := h1.div h0 hC.ne'
  have hmean := hquot.div_atTop hθN'
  refine ⟨hpos,hratio',?_⟩
  apply hmean.congr'
  filter_upwards [hpos,hθ] with m hm hθm
  have hn : (N m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hNp m))
  change (((N m:ℝ)^2*θ m^3*M1 m/Q m)/
    ((N m:ℝ)*θ m^2*M0 m/Q m))/((N m:ℝ)*θ m)=M1 m/M0 m
  field_simp [hn,hθm.ne',(hQ m).ne',hm.1.ne']

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {i : Row} (s : Source μ i)

lemma source_moment_integrals (m : ℕ) :
    (∫ x,deficitMoment 0 (s.response m x) ∂s.law m)=s.success m ∧
      (∫ x,deficitMoment 1 (s.response m x) ∂s.law m)=s.first m ∧
      (∫ x,deficitMoment 2 (s.response m x) ∂s.law m)=s.second m := by
  refine ⟨integral_strict_indicator _ (s.response_measurable m),?_,?_⟩
  · simpa only [deficitMoment_one,max_eq_left (s.response_bounds m _).1] using (s.canonical_integrals m).1
  · simpa only [deficitMoment_two,max_eq_left (s.response_bounds m _).1] using (s.canonical_integrals m).2

theorem moderate (hm : Tendsto (fun m => -s.center m) atTop atTop) :
    (∀ᶠ m in atTop,0< s.success m ∧ 0< s.first m ∧ 0< s.second m) ∧
      Tendsto s.ratio atTop (𝓝 (1/2:ℝ)) ∧
      Tendsto s.conditionalMean atTop (𝓝 0) := by
  let θ := theta μ i s.value s.bid s.focal s.population
  let Q := commonFactor μ i s.value s.bid s.focal s.population
  let C := limitConstant μ i s.value
  let a := 1/(entry i*reciprocalMean μ i s.value)
  have hκ := reciprocalMean_positive μ i s.value s.value_measurable s.value_law
  have ha : 0< a := one_div_pos.mpr (mul_pos (EarlyMean.entry_pos i) hκ)
  have hv := limitingVariance_positive μ i s.value s.bid s.value_measurable s.bid_measurable
    s.value_law s.admissible s.active s.focal s.focal_pos s.focal_le_cutoff s.focal_tendsto
  have hC : 0< C := by
    exact div_pos (mul_pos
      (div_pos (gaussianPDFReal_pos 0 1 0 (by norm_num)) (Real.sqrt_pos.mpr hv))
      (EntryModerateWindow.peak_constant_pos (sub_pos.mpr (cutoff_lt_one i))))
      (eligibleHMean_positive μ i s.value s.value_measurable s.value_law)
  have ht := original_moderate_tilt μ i s.value s.bid s.value_measurable s.bid_measurable
    s.value_law s.admissible s.active s.focal s.focal_pos s.focal_le_cutoff s.focal_tendsto
    s.population s.population_ge_four s.population_tendsto hm
  have hmoment (k : ℕ) (hk : k≤2) :
      Tendsto (fun m => (s.rivals m:ℝ)^(k+1)*θ m^(k+2)*
        (∫ x,deficitMoment k (s.response m x) ∂s.law m)/Q m) atTop
          (𝓝 (C*a^k*(Nat.factorial k:ℝ))) :=
    EntryLiteralModerate.original_moderate_response_moments
    μ i s.value s.bid s.value_measurable s.bid_measurable s.value_law s.admissible s.active
    s.focal s.focal_le_cutoff s.focal_tendsto s.guards s.multiplier_tendsto
    s.population s.population_ge_four s.population_tendsto s.epsilon_pos s.lowerPrice_lt_entry
    s.stripBid s.demandMargin s.weightMargin s.seedMargin s.cap s.finite hm hk
  have h0 : Tendsto (fun m => (s.rivals m:ℝ)*θ m^2*s.success m/Q m) atTop (𝓝 C) := by
    simpa only [zero_add,pow_one,pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,
      (source_moment_integrals s _).1] using hmoment 0 (by norm_num)
  have h1 : Tendsto (fun m => (s.rivals m:ℝ)^2*θ m^3*s.first m/Q m) atTop (𝓝 (C*a)) := by
    simpa only [show (1:ℕ)+1=2 by norm_num,show (1:ℕ)+2=3 by norm_num,pow_one,
      Nat.factorial_one,Nat.cast_one,mul_one,(source_moment_integrals s _).2.1] using hmoment 1 (by norm_num)
  have h2 : Tendsto (fun m => (s.rivals m:ℝ)^3*θ m^4*s.second m/Q m) atTop (𝓝 (2*C*a^2)) := by
    have hh := hmoment 2 (by norm_num)
    norm_num only [show (2:ℕ)+1=3 by norm_num,show (2:ℕ)+2=4 by norm_num,
      Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      mul_one,(source_moment_integrals s _).2.2] at hh
    have he : C*a^2*2=2*C*a^2 := by ring
    simpa only [he] using hh
  exact moderate_root_ratio s.rivals s.rivals_pos s.rivals_tendsto θ Q
    s.success s.first s.second (ht.1.mono fun _ hx => hx.1) ht.2.2.1
    (commonFactor_positive μ i s.value s.bid s.focal s.population) hC ha h0 h1 h2

theorem central {z : ℝ} (hc : Tendsto s.center atTop (𝓝 z)) :
    (∀ᶠ m in atTop,0< s.success m ∧ 0< s.first m ∧ 0< s.second m) ∧
      ∃ r≥(1/2:ℝ),Tendsto s.ratio atTop (𝓝 r) ∧
        Tendsto s.conditionalMean atTop (𝓝 0) :=
  EntryLiteralCanonicalTransfer.original_central_canonical_ratio μ i s.value s.bid s.value_measurable s.bid_measurable
    s.value_law s.admissible s.active s.focal s.focal_le_cutoff s.focal_tendsto s.guards
    s.multiplier_tendsto s.population s.population_ge_four s.population_tendsto
    s.epsilon_pos s.lowerPrice_lt_entry s.stripBid s.demandMargin s.weightMargin s.seedMargin
    s.cap s.finite hc

theorem above (hpos : ∀ m,0< s.center m) (ha : Tendsto s.center atTop atTop) :
    (∀ᶠ m in atTop,0< s.success m ∧ 0< s.first m ∧ 0< s.second m) ∧
      Tendsto s.ratio atTop (𝓝 1) ∧ Tendsto s.conditionalMean atTop (𝓝 0) := by
  have hδ (m) : 0< EntryRawAbove.delta i (s.jointLaw m) (s.rivals m)
      (capacity (s.population m)) (s.focal m) := by
    have hh := hpos m
    change 0< EntryRawAbove.delta i (s.jointLaw m) (s.rivals m)
      (capacity (s.population m)) (s.focal m)/Real.sqrt (s.rivals m:ℝ) at hh
    exact (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (s.rivals_pos m)))).mp hh
  have hh := EntryLiteralAbove.original_above_canonical_ratio μ i s.value s.bid
    s.value_measurable s.bid_measurable s.value_law s.admissible s.active
    s.focal s.focal_le_cutoff s.focal_tendsto s.guards s.multiplier_tendsto
    s.population s.population_ge_four s.population_tendsto s.epsilon_pos s.lowerPrice_lt_entry
    s.stripBid s.demandMargin s.weightMargin s.seedMargin s.cap s.finite hδ ha
  exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem every_subsequence (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) :
    ∃ φ : ℕ → ℕ,StrictMono φ ∧
      (∀ᶠ m in atTop,0< s.success (ψ (φ m)) ∧ 0< s.first (ψ (φ m)) ∧ 0< s.second (ψ (φ m))) ∧
      ∃ r≥(1/2:ℝ),Tendsto (fun m => s.ratio (ψ (φ m))) atTop (𝓝 r) ∧
        Tendsto (fun m => s.conditionalMean (ψ (φ m))) atTop (𝓝 0) := by
  let t := s.reindex ψ hψ
  obtain ⟨φ,hφ,hreg⟩ := three_regime_exhaustion t.center
  let u := t.reindex φ hφ.tendsto_atTop
  refine ⟨φ,hφ,?_⟩
  rcases hreg with hm | hc | ha
  · have hh := moderate u hm
    exact ⟨hh.1,1/2,le_rfl,hh.2.1,hh.2.2⟩
  · obtain ⟨z,hz⟩ := hc
    exact central u hz
  · have hh := above u ha.1 ha.2
    exact ⟨hh.1,1,by norm_num,hh.2.1,hh.2.2⟩

theorem conditionalMean_tendsto_zero : Tendsto s.conditionalMean atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ψ hψ
  obtain ⟨φ,hφ,hpos,r,hr,hlim,hmean⟩ := every_subsequence s ψ hψ
  exact ⟨φ,hmean⟩

end FCAppendix.Affine.Uniform06.EntrySourceRatios
