import FCAppendix.PayOnce.OwnImpact
import FCAppendix.PayOnce.KernelCoverage
import FCAppendix.PayOnce.EndpointVariance

namespace FCAppendix.PayOnce.RareSuccessSlope
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.PayOnce.OwnImpact

noncomputable def phi (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) * (1 - p) ^ (n - 1) * H n p / Hslope n p

theorem phi_nonneg {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    0 ≤ phi n p :=
  div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (sub_nonneg.mpr hp.2) _)) (H_pos n (by omega) p hp.1 hp.2).le)
    (Hslope_pos hn hp).le

theorem continuous_Hslope (n : ℕ) : Continuous (Hslope n) := by
  unfold Hslope
  fun_prop

theorem continuousOn_phi {n : ℕ} (hn : 2 ≤ n) : ContinuousOn (phi n) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div ?_ (continuous_Hslope n).continuousOn
    (fun p hp => (Hslope_pos hn hp).ne')
  unfold H
  fun_prop

theorem continuousAt_phi_zero {n : ℕ} (hn : 2 ≤ n) : ContinuousAt (phi n) 0 := by
  apply ContinuousAt.div ?_ (continuous_Hslope n).continuousAt
    (Hslope_pos hn (show (0 : ℝ) ∈ Icc 0 1 by norm_num)).ne'
  unfold H
  fun_prop

theorem phi_zero {n : ℕ} (hn : 2 ≤ n) : phi n 0 = 2 * n / ((n : ℝ) - 1) := by
  have hn0 : 0 < n := by omega
  have hd : Hslope n 0 = ((n : ℝ) - 1) / 2 := by
    rw [← neg_deriv_H_eq_Hslope, EndpointVariance.deriv_H_zero hn0]
    ring
  simp only [phi, sub_zero, one_pow, mul_one, H_zero n hn0, hd]
  rw [div_div_eq_mul_div]
  ring

theorem phi_zero_pos {n : ℕ} (hn : 2 ≤ n) : 0 < phi n 0 := by
  rw [phi_zero hn]
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  positivity

theorem phi_lower_near_zero {n : ℕ} (hn : 2 ≤ n) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ p ∈ Icc (0 : ℝ) η, phi n 0 / 2 ≤ phi n p := by
  have hp := phi_zero_pos hn
  have he : ∀ᶠ p in 𝓝 (0 : ℝ), phi n 0 / 2 < phi n p :=
    (continuousAt_phi_zero hn).eventually_const_lt (by linarith)
  obtain ⟨d, hd, hdall⟩ := Metric.eventually_nhds_iff.mp he
  let η := min (d / 2) (1 / 2)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  refine ⟨η, hη, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro p hp
  apply (hdall ?_).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hp.1]
  exact hp.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))

noncomputable def weightedSlope (n : ℕ) (p weight : ℝ) : ℝ :=
  if 0 < p ∧ p < 1 then phi n p * (1 - weight) else 0

theorem weightedSlope_nonneg {n : ℕ} (hn : 2 ≤ n) {p weight : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hw : 0 < p ∧ p < 1 → weight ≤ 1) :
    0 ≤ weightedSlope n p weight := by
  unfold weightedSlope
  split_ifs with h
  · exact mul_nonneg (phi_nonneg hn hp) (sub_nonneg.mpr (hw h))
  · rfl

theorem success_le_slope_add_tail {n : ℕ} (hn : 2 ≤ n) {p weight ε κ a : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hκ : 0 < κ) (ha : 0 < a)
    (hw : 0 < p ∧ p < 1 → κ ≤ 1 - weight)
    (hphi : p ≤ ε → a ≤ phi n p) :
    success n p ≤ success n ε / (κ * a) * weightedSlope n p weight +
      if ε ≤ p then 1 else 0 := by
  have hSε := (success_pos n (by omega) ε hε hε1).le
  have hD := weightedSlope_nonneg hn (weight := weight) hp (fun h => by linarith [hw h])
  by_cases htail : ε ≤ p
  · rw [if_pos htail]
    have hS : success n p ≤ 1 := by
      unfold success
      exact sub_le_self _ (pow_nonneg (sub_nonneg.mpr hp.2) _)
    exact hS.trans (le_add_of_nonneg_left (mul_nonneg (div_nonneg hSε (mul_pos hκ ha).le) hD))
  · rw [if_neg htail, add_zero]
    have hpε : p < ε := lt_of_not_ge htail
    by_cases hp0 : p = 0
    · simp [hp0, success, weightedSlope]
    · have hpi : 0 < p ∧ p < 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), hpε.trans_le hε1⟩
      have hDa : κ * a ≤ weightedSlope n p weight := by
        rw [weightedSlope, if_pos hpi]
        calc
          κ * a = a * κ := mul_comm _ _
          _ ≤ phi n p * (1 - weight) := mul_le_mul (hphi hpε.le) (hw hpi) hκ.le (phi_nonneg hn hp)
      have hmon : success n p ≤ success n ε := by
        unfold success
        have hh := pow_le_pow_left₀ (sub_nonneg.mpr hε1) (by linarith : 1 - ε ≤ 1 - p) n
        linarith
      apply hmon.trans
      have hh := mul_le_mul_of_nonneg_left hDa (div_nonneg hSε (mul_pos hκ ha).le)
      simpa only [div_mul_cancel₀ _ (mul_pos hκ ha).ne'] using hh

theorem phi_le_sq {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    phi n p ≤ (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hH := H_bounds n (by omega) p hp.1 hp.2
  have hpow : (1 - p) ^ (n - 1) ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1])
  have hnum : (n : ℝ) * (1 - p) ^ (n - 1) * H n p ≤ n := by
    have hh := mul_le_mul hpow hH.2 (H_pos n (by omega) p hp.1 hp.2).le (by norm_num : (0 : ℝ) ≤ 1)
    have hh' := mul_le_mul_of_nonneg_left hh hnR.le
    simpa only [one_mul, mul_one, mul_assoc] using hh'
  have hsl := (div_le_iff₀ hnR).mp (Hslope_bounds hn hp).1
  have hsl' := mul_le_mul_of_nonneg_left hsl hnR.le
  apply (div_le_iff₀ (Hslope_pos hn hp)).mpr
  nlinarith

theorem measurable_phi (n : ℕ) : Measurable (phi n) := by
  unfold phi H Hslope
  fun_prop

theorem measurable_weightedSlope (n : ℕ) :
    Measurable (fun z : ℝ × ℝ => weightedSlope n z.1 z.2) := by
  unfold weightedSlope
  exact Measurable.ite (by measurability)
    (((measurable_phi n).comp measurable_fst).mul (measurable_const.sub measurable_snd)) measurable_const

theorem integrable_weightedSlope {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (hn : 2 ≤ n)
    {p weight : Ω → ℝ} (hp : Measurable p) (hw : Measurable weight)
    (hbound : ∀ ω, p ω ∈ Icc (0 : ℝ) 1)
    (hweight : ∀ ω, 0 < p ω ∧ p ω < 1 → weight ω ∈ Icc (0 : ℝ) 1) :
    Integrable (fun ω => weightedSlope n (p ω) (weight ω)) P := by
  apply (integrable_const ((n : ℝ) ^ 2)).mono'
    ((measurable_weightedSlope n).comp (hp.prodMk hw)).aestronglyMeasurable
  filter_upwards [] with ω
  change ‖weightedSlope n (p ω) (weight ω)‖ ≤ (n : ℝ) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (weightedSlope_nonneg hn (hbound ω)
    (fun h => (hweight ω h).2))]
  unfold weightedSlope
  split_ifs with hi
  · exact (mul_le_of_le_one_right (phi_nonneg hn (hbound ω))
      (by linarith [(hweight ω hi).1])).trans (phi_le_sq hn (hbound ω))
  · positivity

theorem coverage_le_slope_add_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (hn : 2 ≤ n)
    {p weight : Ω → ℝ} (hp : Measurable p) (hw : Measurable weight)
    (hbound : ∀ ω, p ω ∈ Icc (0 : ℝ) 1)
    (hweight : ∀ ω, 0 < p ω ∧ p ω < 1 → weight ω ∈ Icc (0 : ℝ) 1)
    {ε κ a : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hκ : 0 < κ) (ha : 0 < a)
    (hgap : ∀ ω, 0 < p ω ∧ p ω < 1 → κ ≤ 1 - weight ω)
    (hphi : ∀ q ∈ Icc (0 : ℝ) ε, a ≤ phi n q) :
    (∫ ω, success n (p ω) ∂P) ≤ success n ε / (κ * a) *
      (∫ ω, weightedSlope n (p ω) (weight ω) ∂P) + P.real {ω | ε ≤ p ω} := by
  let E := {ω | ε ≤ p ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hp
  have hI : Integrable (E.indicator (fun _ => (1 : ℝ))) P := (integrable_const _).indicator hE
  have hD := integrable_weightedSlope P hn hp hw hbound hweight
  have hS := UnitInterval.integrable_success P p hp (fun ω => (hbound ω).1)
    (fun ω => (hbound ω).2) n
  have hh := integral_mono hS ((hD.const_mul (success n ε / (κ * a))).add hI) (fun ω => by
    simpa only [Pi.add_apply, E, indicator, mem_setOf_eq] using success_le_slope_add_tail hn (hbound ω)
      hε hε1 hκ ha (hgap ω) (fun hq => hphi _ ⟨(hbound ω).1, hq⟩))
  simp only [Pi.add_apply] at hh
  rw [integral_add (hD.const_mul _) hI, integral_const_mul,
    integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one] at hh
  exact hh

theorem tendsto_slope_over_coverage_atTop
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    {n : ℕ} (hn : 2 ≤ n) (p weight : ∀ m, Ω m → ℝ)
    (hp : ∀ m, Measurable (p m)) (hw : ∀ m, Measurable (weight m))
    (hbound : ∀ m ω, p m ω ∈ Icc (0 : ℝ) 1)
    (hweight : ∀ m ω, 0 < p m ω ∧ p m ω < 1 → weight m ω ∈ Icc (0 : ℝ) 1)
    {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ m ω, 0 < p m ω ∧ p m ω < 1 → κ ≤ 1 - weight m ω)
    (hpos : ∀ᶠ m in atTop, 0 < ∫ ω, success n (p m ω) ∂P m)
    (htails : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Tendsto (fun m => (P m).real {ω | ε ≤ p m ω} /
        (∫ ω, success n (p m ω) ∂P m)) atTop (𝓝 0)) :
    Tendsto (fun m => (∫ ω, weightedSlope n (p m ω) (weight m ω) ∂P m) /
      (∫ ω, success n (p m ω) ∂P m)) atTop atTop := by
  obtain ⟨η, hη, hη1, hphi⟩ := phi_lower_near_zero hn
  let a := phi n 0 / 2
  have ha : 0 < a := half_pos (phi_zero_pos hn)
  have hκa := mul_pos hκ ha
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply tendsto_atTop.mpr
  intro M
  let A := max M 0 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hMA : M < A := by dsimp [A]; linarith [le_max_left M 0]
  let ε := min η (κ * a / (4 * n * A))
  have hden : 0 < (4 : ℝ) * n * A := by positivity
  have hε : 0 < ε := lt_min hη (div_pos hκa hden)
  have hεη : ε ≤ η := min_le_left _ _
  have hε1 : ε ≤ 1 := hεη.trans hη1.le
  have hεsmall : ε * (4 * n * A) ≤ κ * a :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hS : success n ε ≤ (n : ℝ) * ε := by
    rw [← H_mul n (by omega)]
    exact mul_le_of_le_one_right (mul_nonneg hnR.le hε.le) (H_bounds n (by omega) ε hε.le hε1).2
  let C := success n ε / (κ * a)
  have hC : 0 ≤ C := (div_pos (success_pos n (by omega) ε hε hε1) hκa).le
  have hCA : C * A ≤ 1 / 4 := by
    change success n ε / (κ * a) * A ≤ 1 / 4
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hκa).mpr
    have hh := mul_le_mul_of_nonneg_right hS hA.le
    nlinarith
  have htail := (htails ε hε hε1).eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hpos, htail] with m hQ hT
  have hineq := coverage_le_slope_add_tail (P m) hn (hp m) (hw m) (hbound m)
    (hweight m) hε hε1 hκ ha (hgap m) (fun q hq => hphi q ⟨hq.1, hq.2.trans hεη⟩)
  have hd := div_le_div_of_nonneg_right hineq hQ.le
  rw [div_self hQ.ne', add_div, mul_div_assoc] at hd
  by_contra hnot
  have hR : (∫ ω, weightedSlope n (p m ω) (weight m ω) ∂P m) /
      (∫ ω, success n (p m ω) ∂P m) ≤ A := (lt_of_not_ge hnot).le.trans hMA.le
  have hh := mul_le_mul_of_nonneg_left hR hC
  change C * _ ≤ C * A at hh
  change 1 ≤ C * _ + _ at hd
  linarith

theorem tendsto_logarithmicSlope_atTop {D Q x q' : ℕ → ℝ} {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hx : Tendsto x atTop (𝓝 x₀))
    (hD : Tendsto (fun m => D m / Q m) atTop atTop)
    (hderiv : ∀ᶠ m in atTop, q' m = D m / x m) :
    Tendsto (fun m => q' m / Q m) atTop atTop := by
  have hh := hD.atTop_mul_pos (inv_pos.mpr hx₀) (hx.inv₀ hx₀.ne')
  apply hh.congr'
  filter_upwards [hderiv] with m hm
  rw [hm]
  ring

theorem tendsto_surplus_zero_of_firstOrder {Q q' w b : ℕ → ℝ}
    (hQ : ∀ᶠ m in atTop, 0 < Q m)
    (hfirst : ∀ᶠ m in atTop, Q m = (w m - b m) * q' m)
    (hslope : Tendsto (fun m => q' m / Q m) atTop atTop) :
    Tendsto (fun m => w m - b m) atTop (𝓝 0) := by
  have hh := hslope.const_div_atTop (1 : ℝ)
  apply hh.congr'
  filter_upwards [hQ, hfirst] with m hQm hm
  have hq : q' m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    exact hQm.ne' hm
  rw [div_div_eq_mul_div, one_mul]
  exact ((eq_div_iff hq).mpr hm.symm).symm

end FCAppendix.PayOnce.RareSuccessSlope
