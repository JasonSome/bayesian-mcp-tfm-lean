import FCAppendix.PayOnce.GaussianTiltPrefactor
import Mathlib.MeasureTheory.Integral.Layercake

noncomputable section
namespace FCAppendix.PayOnce.GaussianTilt
open MeasureTheory ProbabilityTheory Set Filter Topology
local notation "γ" => gaussianReal 0 1
local notation "Φ" => cdf γ

def strictNegativeHalfExp (v z : ℝ) : ℝ := (Iio 0).indicator (fun z => Real.exp (v*z)) z

theorem measurable_strictNegativeHalfExp (v : ℝ) : Measurable (strictNegativeHalfExp v) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).indicator measurableSet_Iio

theorem strictNegativeHalfExp_bounds {v : ℝ} (hv : 0 ≤ v) (z : ℝ) :
    strictNegativeHalfExp v z ∈ Icc (0:ℝ) 1 := by
  by_cases hz : z < 0
  · simp only [strictNegativeHalfExp,indicator_of_mem (show z ∈ Iio 0 from hz),mem_Icc]
    exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hv hz.le)⟩
  · simp only [strictNegativeHalfExp,indicator_of_notMem (show z ∉ Iio 0 from hz)]
    exact ⟨le_rfl,zero_le_one⟩

theorem integrable_strictNegativeHalfExp_of_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ]
    {v : ℝ} (hv : 0 ≤ v) : Integrable (strictNegativeHalfExp v) μ := by
  apply Integrable.of_bound (measurable_strictNegativeHalfExp v).aestronglyMeasurable 1
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs,abs_of_nonneg (strictNegativeHalfExp_bounds hv z).1] using
    (strictNegativeHalfExp_bounds hv z).2

theorem prefactor_eq_integral_strict (v : ℝ) : prefactor v = ∫ z, strictNegativeHalfExp v z ∂γ := by
  rw [prefactor_eq_strict_integral,← integral_indicator measurableSet_Iio]
  rfl

theorem cdf_leftLim_error_le (μ : Measure ℝ) {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) (x : ℝ) :
    |Function.leftLim (cdf μ) x-Φ x| ≤ η := by
  have hh := ((monotone_cdf μ).tendsto_leftLim x).sub
    ((GaussianResponse.hasDerivAt_normalCDF x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  exact le_of_tendsto hh.abs (Eventually.of_forall hCDF)

private theorem real_Icc_eq_cdf_sub_leftLim (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) :
    μ.real (Icc a b) = cdf μ b-Function.leftLim (cdf μ) a := by
  have he : μ (Icc a b) = ENNReal.ofReal (cdf μ b-Function.leftLim (cdf μ) a) := by
    simpa only [measure_cdf] using (cdf μ).measure_Icc a b
  rw [Measure.real,he,ENNReal.toReal_ofReal (sub_nonneg.mpr ((monotone_cdf μ).leftLim_le hab))]

private theorem real_Ico_eq_leftLim_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) :
    μ.real (Ico a b) = Function.leftLim (cdf μ) b-Function.leftLim (cdf μ) a := by
  have he : μ (Ico a b) = ENNReal.ofReal (Function.leftLim (cdf μ) b-Function.leftLim (cdf μ) a) := by
    simpa only [measure_cdf] using (cdf μ).measure_Ico a b
  rw [Measure.real,he,ENNReal.toReal_ofReal (sub_nonneg.mpr ((monotone_cdf μ).leftLim hab))]

private theorem real_Iio_eq_leftLim (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    μ.real (Iio x) = Function.leftLim (cdf μ) x := by
  have he : μ (Iio x) = ENNReal.ofReal (Function.leftLim (cdf μ) x) := by
    simpa only [measure_cdf,sub_zero] using (cdf μ).measure_Iio (tendsto_cdf_atBot μ) x
  have hn : 0 ≤ Function.leftLim (cdf μ) x :=
    ge_of_tendsto ((monotone_cdf μ).tendsto_leftLim x) (Eventually.of_forall (cdf_nonneg μ))
  rw [Measure.real,he,ENNReal.toReal_ofReal hn]

private theorem normalCDF_leftLim (x : ℝ) : Function.leftLim Φ x = Φ x :=
  (GaussianResponse.hasDerivAt_normalCDF x).continuousAt.continuousWithinAt.leftLim_eq

theorem real_Icc_error_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) {a b : ℝ} (hab : a ≤ b) :
    |μ.real (Icc a b)-(γ).real (Icc a b)| ≤ 2*η := by
  rw [real_Icc_eq_cdf_sub_leftLim μ hab,real_Icc_eq_cdf_sub_leftLim γ hab,normalCDF_leftLim]
  have h1 := abs_le.mp (hCDF b)
  have h2 := abs_le.mp (cdf_leftLim_error_le μ hCDF a)
  exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩

theorem real_Ico_error_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) {a b : ℝ} (hab : a ≤ b) :
    |μ.real (Ico a b)-(γ).real (Ico a b)| ≤ 2*η := by
  rw [real_Ico_eq_leftLim_sub μ hab,real_Ico_eq_leftLim_sub γ hab,normalCDF_leftLim,normalCDF_leftLim]
  have h1 := abs_le.mp (cdf_leftLim_error_le μ hCDF b)
  have h2 := abs_le.mp (cdf_leftLim_error_le μ hCDF a)
  exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩

private theorem integrable_unit_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (Y : ℝ → ℝ) :
    IntegrableOn (fun t : ℝ => μ.real {z | t ≤ Y z}) (Ioc 0 1) := by
  have hm : Antitone (fun t : ℝ => μ {z | t ≤ Y z}) := by
    intro s t hst
    exact measure_mono (fun _ hz => hst.trans hz)
  apply Integrable.of_bound hm.measurable.ennreal_toReal.aestronglyMeasurable.restrict 1
  filter_upwards [] with t
  change |μ.real {z | t ≤ Y z}| ≤ 1
  rw [abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

private theorem integral_error_le_of_unit_tail
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Y : ℝ → ℝ} (hY : Measurable Y) (hb : ∀ z, Y z ∈ Icc (0:ℝ) 1) {δ : ℝ}
    (htail : ∀ t ∈ Ioc (0:ℝ) 1, |μ.real {z | t ≤ Y z}-ν.real {z | t ≤ Y z}| ≤ δ) :
    |(∫ z, Y z ∂μ)-(∫ z, Y z ∂ν)| ≤ δ := by
  have hI (P : Measure ℝ) [IsProbabilityMeasure P] : Integrable Y P := by
    apply Integrable.of_bound hY.aestronglyMeasurable 1
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hb z).1] using (hb z).2
  rw [(hI μ).integral_eq_integral_Ioc_meas_le (Eventually.of_forall fun z => (hb z).1)
      (Eventually.of_forall fun z => (hb z).2),
    (hI ν).integral_eq_integral_Ioc_meas_le (Eventually.of_forall fun z => (hb z).1)
      (Eventually.of_forall fun z => (hb z).2),
    ← integral_sub (integrable_unit_tail μ Y) (integrable_unit_tail ν Y)]
  have hh := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0:ℝ) 1))
    (f := fun t => μ.real {z | t ≤ Y z}-ν.real {z | t ≤ Y z})
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [Real.norm_eq_abs] using htail t ht)
  simpa only [Real.norm_eq_abs,Measure.real,Measure.restrict_apply MeasurableSet.univ,
    univ_inter,Real.volume_Ioc,sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,mul_one] using hh

private theorem negativeHalfExp_superlevel {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    {z | t ≤ negativeHalfExp v z} = Icc (Real.log t/v) 0 := by
  ext z
  by_cases hz : z ≤ 0
  · simp only [negativeHalfExp,mem_setOf_eq,indicator_of_mem (show z ∈ Iic 0 from hz),mem_Icc,hz,and_true]
    rw [div_le_iff₀ hv,Real.log_le_iff_le_exp ht]
    rw [mul_comm]
  · simp only [negativeHalfExp,mem_setOf_eq,indicator_of_notMem (show z ∉ Iic 0 from hz),mem_Icc,hz,and_false]
    exact iff_false_intro (not_le_of_gt ht)

private theorem strictNegativeHalfExp_superlevel {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    {z | t ≤ strictNegativeHalfExp v z} = Ico (Real.log t/v) 0 := by
  ext z
  by_cases hz : z < 0
  · simp only [strictNegativeHalfExp,mem_setOf_eq,indicator_of_mem (show z ∈ Iio 0 from hz),mem_Ico,hz,and_true]
    rw [div_le_iff₀ hv,Real.log_le_iff_le_exp ht]
    rw [mul_comm]
  · simp only [strictNegativeHalfExp,mem_setOf_eq,indicator_of_notMem (show z ∉ Iio 0 from hz),mem_Ico,hz,and_false]
    exact iff_false_intro (not_le_of_gt ht)

theorem integral_negativeHalfExp_sub_prefactor_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) {v : ℝ} (hv : 0 ≤ v) :
    |(∫ z, negativeHalfExp v z ∂μ)-prefactor v| ≤ 2*η := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hCDF 0)
  rcases hv.eq_or_lt with rfl | hv
  · have hi : (∫ z, negativeHalfExp 0 z ∂μ) = cdf μ 0 := by
      simp only [negativeHalfExp,zero_mul,Real.exp_zero,
        integral_indicator_const _ measurableSet_Iic,smul_eq_mul,mul_one,cdf_eq_real]
    rw [hi,prefactor_eq_exp_mul_cdf]
    norm_num only [zero_pow (by norm_num : 2 ≠ 0),zero_div,Real.exp_zero,neg_zero,one_mul]
    exact (hCDF 0).trans (by linarith)
  · rw [prefactor_eq_integral]
    apply integral_error_le_of_unit_tail μ γ (measurable_negativeHalfExp v) (negativeHalfExp_bounds hv.le)
    intro t ht
    rw [negativeHalfExp_superlevel hv ht.1]
    exact real_Icc_error_le μ hCDF (div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos ht.1.le ht.2) hv.le)

theorem integral_strictNegativeHalfExp_sub_prefactor_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) {v : ℝ} (hv : 0 ≤ v) :
    |(∫ z, strictNegativeHalfExp v z ∂μ)-prefactor v| ≤ 2*η := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hCDF 0)
  rcases hv.eq_or_lt with rfl | hv
  · have hi : (∫ z, strictNegativeHalfExp 0 z ∂μ) = Function.leftLim (cdf μ) 0 := by
      simp only [strictNegativeHalfExp,zero_mul,Real.exp_zero,
        integral_indicator_const _ measurableSet_Iio,smul_eq_mul,mul_one,real_Iio_eq_leftLim]
    rw [hi,prefactor_eq_exp_mul_cdf]
    norm_num only [zero_pow (by norm_num : 2 ≠ 0),zero_div,Real.exp_zero,neg_zero,one_mul]
    exact (cdf_leftLim_error_le μ hCDF 0).trans (by linarith)
  · rw [prefactor_eq_integral_strict]
    apply integral_error_le_of_unit_tail μ γ (measurable_strictNegativeHalfExp v) (strictNegativeHalfExp_bounds hv.le)
    intro t ht
    rw [strictNegativeHalfExp_superlevel hv ht.1]
    exact real_Ico_error_le μ hCDF (div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos ht.1.le ht.2) hv.le)

theorem integral_negativeHalfExp_relative_error_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) {v : ℝ} (hv : 0 ≤ v) :
    |(∫ z, negativeHalfExp v z ∂μ)/prefactor v-1| ≤ 2*η*(1+v)/lowerConstant := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hCDF 0)
  have hp := prefactor_pos v
  have hden : 0 < 1+v := by linarith
  have he : (∫ z, negativeHalfExp v z ∂μ)/prefactor v-1 =
      ((∫ z, negativeHalfExp v z ∂μ)-prefactor v)/prefactor v := by field_simp
  rw [he,abs_div,abs_of_pos hp]
  calc
    _ ≤ (2*η)/prefactor v := (div_le_div_iff_of_pos_right hp).mpr
      (integral_negativeHalfExp_sub_prefactor_le μ hCDF hv)
    _ ≤ (2*η)/(lowerConstant/(1+v)) := div_le_div_of_nonneg_left (by positivity)
      (div_pos lowerConstant_pos hden) (prefactor_bounds hv).1
    _ = 2*η*(1+v)/lowerConstant := by field_simp

theorem integral_strictNegativeHalfExp_relative_error_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) {v : ℝ} (hv : 0 ≤ v) :
    |(∫ z, strictNegativeHalfExp v z ∂μ)/prefactor v-1| ≤ 2*η*(1+v)/lowerConstant := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hCDF 0)
  have hp := prefactor_pos v
  have hden : 0 < 1+v := by linarith
  have he : (∫ z, strictNegativeHalfExp v z ∂μ)/prefactor v-1 =
      ((∫ z, strictNegativeHalfExp v z ∂μ)-prefactor v)/prefactor v := by field_simp
  rw [he,abs_div,abs_of_pos hp]
  calc
    _ ≤ (2*η)/prefactor v := (div_le_div_iff_of_pos_right hp).mpr
      (integral_strictNegativeHalfExp_sub_prefactor_le μ hCDF hv)
    _ ≤ (2*η)/(lowerConstant/(1+v)) := div_le_div_of_nonneg_left (by positivity)
      (div_pos lowerConstant_pos hden) (prefactor_bounds hv).1
    _ = 2*η*(1+v)/lowerConstant := by field_simp

theorem integral_negativeHalfExp_comparable
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) {v : ℝ} (hv : 0 ≤ v)
    (hsmall : η*(1+v) ≤ lowerConstant/4) :
    prefactor v/2 ≤ (∫ z, negativeHalfExp v z ∂μ) ∧
      (∫ z, negativeHalfExp v z ∂μ) ≤ 3*prefactor v/2 := by
  have hh := integral_negativeHalfExp_relative_error_le μ hCDF hv
  have herr : 2*η*(1+v)/lowerConstant ≤ 1/2 :=
    (div_le_iff₀ lowerConstant_pos).mpr (by linarith)
  have hbound := abs_le.mp (hh.trans herr)
  have hlo := (le_div_iff₀ (prefactor_pos v)).mp (show 1/2 ≤ (∫ z, negativeHalfExp v z ∂μ)/prefactor v by linarith)
  have hhi := (div_le_iff₀ (prefactor_pos v)).mp (show (∫ z, negativeHalfExp v z ∂μ)/prefactor v ≤ 3/2 by linarith)
  constructor <;> linarith

theorem integral_strictNegativeHalfExp_comparable
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {η : ℝ}
    (hCDF : ∀ x : ℝ, |cdf μ x-Φ x| ≤ η) {v : ℝ} (hv : 0 ≤ v)
    (hsmall : η*(1+v) ≤ lowerConstant/4) :
    prefactor v/2 ≤ (∫ z, strictNegativeHalfExp v z ∂μ) ∧
      (∫ z, strictNegativeHalfExp v z ∂μ) ≤ 3*prefactor v/2 := by
  have hh := integral_strictNegativeHalfExp_relative_error_le μ hCDF hv
  have herr : 2*η*(1+v)/lowerConstant ≤ 1/2 :=
    (div_le_iff₀ lowerConstant_pos).mpr (by linarith)
  have hbound := abs_le.mp (hh.trans herr)
  have hlo := (le_div_iff₀ (prefactor_pos v)).mp (show 1/2 ≤ (∫ z, strictNegativeHalfExp v z ∂μ)/prefactor v by linarith)
  have hhi := (div_le_iff₀ (prefactor_pos v)).mp (show (∫ z, strictNegativeHalfExp v z ∂μ)/prefactor v ≤ 3/2 by linarith)
  constructor <;> linarith

end FCAppendix.PayOnce.GaussianTilt
