import FCAppendix.Affine.Uniform06.LowChernoffCertificate
import FCAppendix.Affine.ClippedResidualRoots

set_option autoImplicit false

noncomputable section
namespace FCAppendix.Affine.Uniform06.LowChernoff

open MeasureTheory Set
open FCAppendix.Affine.Uniform07
open FCAppendix.Affine.ClippedResidual

def normalizedFloor (i : Row) (y : ℝ) : ℝ :=
  (69/100:ℝ)*max 0 (y-1/200)*
    min 1 (max 0 ((y-(x i+1/400))/(1/400)))

def physicalFloor (i : Row) (v : ℝ) : ℝ :=
  (69/100:ℝ)*max 0 (v-cutoff i/200)*
    min 1 (max 0 ((v-(entry i+cutoff i/400))/(cutoff i/400)))

def conditionalValueLaw (i : Row) : Measure ℝ :=
  ENNReal.ofReal (1/cutoff i) • volume.restrict (Icc (0:ℝ) (cutoff i))

def floorStatistic (i : Row) (y : ℝ) : ℝ :=
  exposure (xi i) (501/1000) (normalizedFloor i y)

def physicalStatistic (i : Row) (b : ℝ) : ℝ :=
  exposure (xi i) ((501/1000)*cutoff i) b

theorem continuous_normalizedFloor (i : Row) : Continuous (normalizedFloor i) := by
  unfold normalizedFloor
  fun_prop

theorem continuous_physicalFloor (i : Row) : Continuous (physicalFloor i) := by
  unfold physicalFloor
  fun_prop

theorem physicalFloor_scaled (i : Row) (y : ℝ) :
    physicalFloor i (cutoff i*y) = cutoff i*normalizedFloor i y := by
  have ht := cutoff_pos i
  have hnum : cutoff i*y-cutoff i/200 = cutoff i*(y-1/200) := by ring
  have hmax : max 0 (cutoff i*(y-1/200)) = cutoff i*max 0 (y-1/200) := by
    by_cases hy : 0 ≤ y-1/200
    · rw [max_eq_right hy, max_eq_right (mul_nonneg ht.le hy)]
    · have hy' := le_of_not_ge hy
      rw [max_eq_left hy', max_eq_left (mul_nonpos_of_nonneg_of_nonpos ht.le hy')]
      ring
  have hquot : (cutoff i*y-(entry i+cutoff i/400))/(cutoff i/400) =
      (y-(x i+1/400))/(1/400) := by
    unfold entry
    field_simp [ht.ne']
  unfold physicalFloor normalizedFloor
  rw [hnum, hmax, hquot]
  ring

theorem exposure_positive_scaling {ξ z b t : ℝ} (hξ : 0 < ξ)
    (hz : 0 < z) (ht : 0 < t) :
    exposure ξ (t*z) (t*b) = exposure ξ z b := by
  by_cases hb : b ≤ z
  · rw [exposure_zero hb, exposure_zero (mul_le_mul_of_nonneg_left hb ht.le)]
  · have hzb := lt_of_not_ge hb
    have hb0 := hz.trans hzb
    have hbz : 0 ≤ b-z := sub_nonneg.mpr hzb.le
    have htbz : 0 ≤ t*b-t*z := by nlinarith
    unfold exposure
    rw [max_eq_left hzb.le,
      max_eq_left (mul_le_mul_of_nonneg_left hzb.le ht.le),
      max_eq_right hbz, max_eq_right htbz]
    congr 1
    field_simp [hξ.ne', hb0.ne', ht.ne']

theorem physical_floor_statistic_scaled (i : Row) (y : ℝ) :
    physicalStatistic i (physicalFloor i (cutoff i*y)) = floorStatistic i y := by
  rw [physicalFloor_scaled]
  unfold physicalStatistic floorStatistic
  rw [mul_comm (501/1000:ℝ) (cutoff i)]
  exact exposure_positive_scaling (xi_pos i) (by norm_num) (cutoff_pos i)

theorem exposure_monotone_bid {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z) :
    Monotone (exposure ξ z) := by
  intro a b hab
  by_cases ha : a ≤ z
  · rw [exposure_zero ha]
    exact exposure_nonneg hξ hz
  · have hza := lt_of_not_ge ha
    have hzb := hza.trans_le hab
    have ha0 := hz.trans hza
    have hb0 := hz.trans hzb
    have hf (u : ℝ) (hu : z < u) :
        exposure ξ z u = min 1 ((1-z/u)/ξ) := by
      have hu0 := hz.trans hu
      unfold exposure
      rw [max_eq_left hu.le, max_eq_right (sub_nonneg.mpr hu.le)]
      congr 1
      field_simp [hξ.ne', hu0.ne']
    rw [hf a hza, hf b hzb]
    apply min_le_min_left
    apply div_le_div_of_nonneg_right _ hξ.le
    have hd := div_le_div_of_nonneg_left hz.le ha0 hab
    linarith

theorem floorStatistic_nonneg (i : Row) (y : ℝ) : 0 ≤ floorStatistic i y :=
  exposure_nonneg (xi_pos i) (by norm_num)

theorem continuous_floorStatistic (i : Row) : Continuous (floorStatistic i) :=
  (continuous_exposure (xi_pos i) (by norm_num)).comp (continuous_normalizedFloor i)

theorem physicalStatistic_nonneg (i : Row) (b : ℝ) : 0 ≤ physicalStatistic i b :=
  exposure_nonneg (xi_pos i) (mul_pos (by norm_num) (cutoff_pos i))

theorem continuous_physicalStatistic (i : Row) : Continuous (physicalStatistic i) :=
  continuous_exposure (xi_pos i) (mul_pos (by norm_num) (cutoff_pos i))

theorem normalizedFloor_full (i : Row) {y : ℝ}
    (hy : (aQ i : ℝ) ≤ y) :
    normalizedFloor i y = (69/100:ℝ)*(y-1/200) := by
  have hay : x i+1/200 ≤ y := by
    have hh : x i+1/200 ≤ (aQ i : ℝ) := by
      cases i <;> norm_num [aQ, leftQ, x, xQ]
    exact hh.trans hy
  have hmax : 0 ≤ y-1/200 := by
    have hx : 0 < x i := by cases i <;> norm_num [x, xQ]
    linarith
  have hclip : 1 ≤ (y-(x i+1/400))/(1/400) := by linarith
  unfold normalizedFloor
  rw [max_eq_right hmax, max_eq_right (zero_le_one.trans hclip),
    min_eq_left hclip, mul_one]

theorem floorStatistic_on_full_piece (i : Row) {y : ℝ}
    (hy : y ∈ Icc (aQ i : ℝ) 1) :
    floorStatistic i y =
      pieceP (alphaQ i : ℝ) (betaQ i : ℝ) (y-1/200) := by
  have hxi := xi_pos i
  have hyl : 0 < y-1/200 := by
    have hl : (1/200:ℝ) < aQ i := by cases i <;> norm_num [aQ, leftQ]
    linarith [hy.1]
  have hb : (501/1000:ℝ) ≤ (69/100)*(y-1/200) := by
    have hh : (501/1000:ℝ) ≤ (69/100)*((aQ i : ℝ)-1/200) := by
      cases i <;> norm_num [aQ, leftQ]
    nlinarith [hy.1]
  have hclip : (1-xi i)*((69/100)*(y-1/200)) ≤ (501/1000:ℝ) := by
    cases i <;> norm_num [xi, xiQ, etaQ] at * <;> nlinarith [hy.2]
  have hex : exposure (xi i) (501/1000) ((69/100)*(y-1/200)) =
      (1-(501/1000)/((69/100)*(y-1/200)))/xi i := by
    rcases hb.eq_or_lt with hb | hb
    · rw [← hb, exposure_zero le_rfl]
      norm_num
    · exact exposure_of_between hxi (by norm_num) hb hclip
  unfold floorStatistic
  rw [normalizedFloor_full i hy.1, hex]
  unfold pieceP alphaQ betaQ xi
  cases i <;> norm_num [xiQ, etaQ] <;> field_simp [hyl.ne'] <;> ring

theorem floor_mgf_integral_bound (i : Row) :
    (∫ y in (0:ℝ)..1, Real.exp (-(thetaQ i : ℝ)*floorStatistic i y)) ≤
      (aQ i : ℝ)+pieceZ (alphaQ i : ℝ) (betaQ i : ℝ) (thetaQ i : ℝ)
        (leftQ i : ℝ) (rightQ : ℝ) := by
  let f : ℝ → ℝ := fun y => Real.exp (-(thetaQ i : ℝ)*floorStatistic i y)
  have hf : Continuous f := (continuous_const.mul (continuous_floorStatistic i)).rexp
  have ha0 : (0:ℝ) ≤ aQ i := by cases i <;> norm_num [aQ, leftQ]
  have ha1 : (aQ i : ℝ) ≤ 1 := by cases i <;> norm_num [aQ, leftQ]
  have hθ : (0:ℝ) ≤ thetaQ i := by cases i <;> norm_num [thetaQ]
  have hsmall : (∫ y in (0:ℝ)..(aQ i : ℝ), f y) ≤ (aQ i : ℝ) := by
    have h := intervalIntegral.integral_mono_on ha0 (hf.intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) (fun y _ => Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (floorStatistic_nonneg i y)))
    simpa using h
  have hlarge : (∫ y in (aQ i : ℝ)..1, f y) =
      pieceZ (alphaQ i : ℝ) (betaQ i : ℝ) (thetaQ i : ℝ)
        (leftQ i : ℝ) (rightQ : ℝ) := by
    calc
      _ = ∫ y in (aQ i : ℝ)..1,
          Real.exp (-(thetaQ i : ℝ)*
            pieceP (alphaQ i : ℝ) (betaQ i : ℝ) (y-1/200)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le ha1] at hy
        simp only [f, floorStatistic_on_full_piece i hy]
      _ = _ := by
        change (∫ y in (aQ i : ℝ)..1,
          (fun u => Real.exp (-(thetaQ i : ℝ)*pieceP (alphaQ i : ℝ) (betaQ i : ℝ) u))
            (y-1/200)) = _
        rw [intervalIntegral.integral_comp_sub_right
          (fun u : ℝ => Real.exp (-(thetaQ i : ℝ)*pieceP (alphaQ i : ℝ) (betaQ i : ℝ) u))]
        congr 2 <;> norm_num [aQ, rightQ]
  change (∫ y in (0:ℝ)..1, f y) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 (aQ i)) (hf.intervalIntegrable (aQ i) 1), hlarge]
  linarith

private theorem integrable_bounded_negative_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) {θ : ℝ} (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (-θ*Y ω)) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (hY.const_mul (-θ)).exp.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [hY0 ω])

theorem original_lower_mgf_bound (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, physicalFloor i p.1 ≤ p.2) :
    (1-cutoff i)*Real.exp (-(thetaQ i : ℝ)/2)+cutoff i*
      (∫ p, Real.exp (-(thetaQ i : ℝ)*physicalStatistic i p.2) ∂G)
        ≤ lowSurrogate i := by
  have ht := cutoff_pos i
  have hθ : (0:ℝ) ≤ thetaQ i := by cases i <;> norm_num [thetaQ]
  let f : ℝ → ℝ := fun v =>
    Real.exp (-(thetaQ i : ℝ)*physicalStatistic i (physicalFloor i v))
  have hf : Continuous f :=
    (continuous_const.mul
      ((continuous_physicalStatistic i).comp (continuous_physicalFloor i))).rexp
  have h1 := integrable_bounded_negative_exp G
    (fun p => physicalStatistic i p.2)
    ((continuous_physicalStatistic i).measurable.comp measurable_snd)
    (fun p => physicalStatistic_nonneg i p.2) hθ
  have h2 := integrable_bounded_negative_exp G
    (fun p => physicalStatistic i (physicalFloor i p.1))
    (((continuous_physicalStatistic i).comp (continuous_physicalFloor i)).measurable.comp
      measurable_fst)
    (fun p => physicalStatistic_nonneg i (physicalFloor i p.1)) hθ
  have hdom : (∫ p, Real.exp (-(thetaQ i : ℝ)*physicalStatistic i p.2) ∂G) ≤
      ∫ p, f p.1 ∂G := by
    apply integral_mono_ae h1 h2
    filter_upwards [hfloor] with p hp
    apply Real.exp_le_exp.mpr
    have hmono := exposure_monotone_bid (xi_pos i)
      (mul_pos (by norm_num) (cutoff_pos i) : (0:ℝ)<(501/1000)*cutoff i) hp
    change physicalStatistic i (physicalFloor i p.1) ≤ physicalStatistic i p.2 at hmono
    nlinarith
  have hnormalize : (∫ p, f p.1 ∂G) =
      ∫ y in (0:ℝ)..1, Real.exp (-(thetaQ i : ℝ)*floorStatistic i y) := by
    rw [← integral_map measurable_fst.aemeasurable hf.measurable.aestronglyMeasurable,
      hvalue, conditionalValueLaw, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity)]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.le]
    have hscale := intervalIntegral.smul_integral_comp_mul_left
      (a := (0:ℝ)) (b := 1) f (cutoff i)
    simp only [smul_eq_mul, mul_zero, mul_one] at hscale
    rw [← hscale]
    have hfun : (fun y => f (cutoff i*y)) =
        (fun y => Real.exp (-(thetaQ i : ℝ)*floorStatistic i y)) := by
      funext y
      simp only [f, physical_floor_statistic_scaled]
    rw [hfun]
    simp only [smul_eq_mul]
    field_simp [ht.ne']
  rw [hnormalize] at hdom
  have hbound := hdom.trans (floor_mgf_integral_bound i)
  have hh := mul_le_mul_of_nonneg_left hbound ht.le
  dsimp [lowSurrogate]
  linarith

theorem original_lower_chernoff_gap (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, physicalFloor i p.1 ≤ p.2) :
    sourceGap i < -(thetaQ i : ℝ)*rho-
      Real.log ((1-cutoff i)*Real.exp (-(thetaQ i : ℝ)/2)+cutoff i*
        (∫ p, Real.exp (-(thetaQ i : ℝ)*physicalStatistic i p.2) ∂G))-
      rankI0 i := by
  have hp : 0 < (1-cutoff i)*Real.exp (-(thetaQ i : ℝ)/2) :=
    mul_pos (sub_pos.mpr (cutoff_lt_one i)) (Real.exp_pos _)
  have hn : 0 ≤ cutoff i*
      (∫ p, Real.exp (-(thetaQ i : ℝ)*physicalStatistic i p.2) ∂G) :=
    mul_nonneg (cutoff_pos i).le (integral_nonneg (fun _ => (Real.exp_pos _).le))
  apply dominated_mgf_rate_gap i (by linarith)
  exact original_lower_mgf_bound i G hvalue hfloor

end FCAppendix.Affine.Uniform06.LowChernoff
