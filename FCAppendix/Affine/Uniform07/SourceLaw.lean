import FCAppendix.Affine.Uniform07.RateDefinitions
import FCAppendix.Affine.Uniform07.ParameterCertificate
import Mathlib.Probability.Moments.Tilted

namespace FCAppendix.Affine.Uniform07
open MeasureTheory ProbabilityTheory Set

theorem measurable_normalizedAcceptance (i : Row) (z : ℝ) :
    Measurable (normalizedAcceptance i z) := by
  unfold normalizedAcceptance pieceP
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic
      (measurable_const.sub (measurable_const.div measurable_id))
      (measurable_const.sub (measurable_const.div measurable_id)))

theorem normalizedAcceptance_bounds (i : Row) {z y : ℝ}
    (hz : z ∈ Icc (1/2) (x i)) (hy : y ∈ Icc (0:ℝ) 1) :
    normalizedAcceptance i z y ∈ Icc (0:ℝ) 1 := by
  unfold normalizedAcceptance
  split_ifs with hyz hyx
  · exact ⟨le_rfl,zero_le_one⟩
  · exact low_piece_bounds i hz.1 (le_of_not_ge hyz) hyx
  · exact high_piece_bounds i hz.1 hz.2 (le_of_not_ge hyx) hy.2

instance uniformLaw_probability : IsProbabilityMeasure uniformLaw := by
  constructor
  norm_num [uniformLaw, Measure.restrict_apply, Real.volume_Icc]

noncomputable def lowerSourceLaw (i : Row) (z : ℝ) : Measure ℝ :=
  uniformLaw.map (normalizedAcceptance i z)

instance lowerSourceLaw_probability (i : Row) (z : ℝ) :
    IsProbabilityMeasure (lowerSourceLaw i z) :=
  Measure.isProbabilityMeasure_map (measurable_normalizedAcceptance i z).aemeasurable

noncomputable def sourceLaw (i : Row) (z : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1-cutoff i) • Measure.dirac (1/2:ℝ) +
    ENNReal.ofReal (cutoff i) • lowerSourceLaw i z

instance sourceLaw_probability (i : Row) (z : ℝ) :
    IsProbabilityMeasure (sourceLaw i z) := by
  constructor
  simp only [sourceLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [cutoff_lt_one i]) (cutoff_pos i).le]
  norm_num

theorem lowerSourceLaw_bounds (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i)) :
    ∀ᵐ y ∂lowerSourceLaw i z, y ∈ Icc (0:ℝ) 1 := by
  apply (ae_map_iff (measurable_normalizedAcceptance i z).aemeasurable
    measurableSet_Icc).mpr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with y hy
  exact normalizedAcceptance_bounds i hz hy

theorem sourceLaw_bounds (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i)) :
    ∀ᵐ y ∂sourceLaw i z, y ∈ Icc (0:ℝ) 1 := by
  rw [sourceLaw, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure ((ae_dirac_iff (by measurability)).mpr (by norm_num)) _
  · exact Measure.ae_smul_measure (lowerSourceLaw_bounds i hz) _

theorem lowerSourceLaw_integrable (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i))
    {f : ℝ → ℝ} (hf : Continuous f) : Integrable f (lowerSourceLaw i z) := by
  have hi := hf.integrableOn_Icc (μ := lowerSourceLaw i z) (a := (0:ℝ)) (b := 1)
  change Integrable f ((lowerSourceLaw i z).restrict (Icc 0 1)) at hi
  rwa [Measure.restrict_eq_self_of_ae_mem (lowerSourceLaw_bounds i hz)] at hi

theorem lowerSourceLaw_integral (i : Row) (z : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ y, f y ∂lowerSourceLaw i z) =
      ∫ y in (0:ℝ)..1, f (normalizedAcceptance i z y) := by
  rw [lowerSourceLaw, integral_map (measurable_normalizedAcceptance i z).aemeasurable
    hf.measurable.aestronglyMeasurable]
  unfold uniformLaw
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

theorem sourceLaw_integral (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i))
    {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ y, f y ∂sourceLaw i z) = (1-cutoff i)*f (1/2)+
      cutoff i*(∫ y in (0:ℝ)..1, f (normalizedAcceptance i z y)) := by
  have hl := lowerSourceLaw_integrable i hz hf
  have hd : Integrable f (Measure.dirac (1/2:ℝ)) := integrable_dirac (by finiteness)
  rw [sourceLaw, integral_add_measure
    (hd.smul_measure ENNReal.ofReal_ne_top) (hl.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (by linarith [cutoff_lt_one i]),
    ENNReal.toReal_ofReal (cutoff_pos i).le, lowerSourceLaw_integral i z hf]
  rfl

theorem sourceLaw_piece_integral (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i))
    {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ y, f y ∂sourceLaw i z) = (1-cutoff i)*f (1/2)+cutoff i*
      (z*f 0+(∫ y in z..x i, f (pieceP (1/xi i) (z/xi i) y))+
        ∫ y in x i..1, f (pieceP ((1-z*kappa i/x i)/xi i) z y)) := by
  let g := fun y => f (normalizedAcceptance i z y)
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hx1 : x i ≤ 1 := by cases i <;> norm_num [x,xQ]
  have hx0 : 0 ≤ x i := hz0.trans hz.2
  have hg0 := (lowerSourceLaw_integrable i hz hf).comp_measurable
    (measurable_normalizedAcceptance i z)
  have hg : IntervalIntegrable g volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr
    exact hg0
  have hint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable g volume a b := by
    apply hg.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc ha hb
  have h0z := hint 0 z le_rfl hz0 (hz.2.trans hx1)
  have hzx := hint z (x i) hz0 hz.2 hx1
  have h0x := hint 0 (x i) le_rfl hx0 hx1
  have hxone := hint (x i) 1 hx0 hx1 le_rfl
  have hsplit : (∫ y in (0:ℝ)..1, g y) =
      (∫ y in (0:ℝ)..z, g y)+(∫ y in z..x i, g y)+(∫ y in x i..1, g y) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals h0x hxone,
      ← intervalIntegral.integral_add_adjacent_intervals h0z hzx]
  have hzero : (∫ y in (0:ℝ)..z, g y) = z*f 0 := by
    calc
      _ = ∫ _y in (0:ℝ)..z, f 0 := by
        simp only [intervalIntegral.integral_of_le hz0]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro y hy
        simp [g, normalizedAcceptance, hy.2]
      _ = _ := by simp [intervalIntegral.integral_const]
  have hlow : (∫ y in z..x i, g y) =
      ∫ y in z..x i, f (pieceP (1/xi i) (z/xi i) y) := by
    simp only [intervalIntegral.integral_of_le hz.2]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp [g, normalizedAcceptance, not_le_of_gt hy.1, hy.2]
  have hhigh : (∫ y in x i..1, g y) =
      ∫ y in x i..1, f (pieceP ((1-z*kappa i/x i)/xi i) z y) := by
    simp only [intervalIntegral.integral_of_le hx1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp [g, normalizedAcceptance, not_le_of_gt (hz.2.trans_lt hy.1), not_le_of_gt hy.1]
  rw [sourceLaw_integral i hz hf]
  change (1-cutoff i)*f (1/2)+cutoff i*(∫ y in (0:ℝ)..1, g y) = _
  rw [hsplit, hzero, hlow, hhigh]

theorem sourceLaw_mgf (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i)) (theta : ℝ) :
    mgf (fun y : ℝ => y) (sourceLaw i z) (-theta) = laplace i theta z := by
  rw [mgf, sourceLaw_piece_integral i hz
    (show Continuous (fun y : ℝ => Real.exp (-theta*y)) by fun_prop)]
  unfold laplace pieceZ
  simp only [mul_zero, Real.exp_zero, mul_one]
  congr 2
  ring

theorem sourceLaw_score (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i)) (theta : ℝ) :
    (∫ y, (y-rho)*Real.exp (-theta*y) ∂sourceLaw i z) = tiltScore i theta z := by
  rw [sourceLaw_piece_integral i hz
    (show Continuous (fun y : ℝ => (y-rho)*Real.exp (-theta*y)) by fun_prop)]
  unfold tiltScore pieceF
  simp only [mul_zero, Real.exp_zero, mul_one, zero_sub]
  rw [show -theta*(1/2:ℝ) = -theta/2 by ring]
  ring

theorem sourceLaw_integrable (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i))
    {f : ℝ → ℝ} (hf : Continuous f) : Integrable f (sourceLaw i z) := by
  have hi := hf.integrableOn_Icc (μ := sourceLaw i z) (a := (0:ℝ)) (b := 1)
  change Integrable f ((sourceLaw i z).restrict (Icc 0 1)) at hi
  rwa [Measure.restrict_eq_self_of_ae_mem (sourceLaw_bounds i hz)] at hi

theorem sourceLaw_exp_integrable (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i))
    (theta : ℝ) : Integrable (fun y : ℝ => Real.exp (theta*y)) (sourceLaw i z) :=
  integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable (sourceLaw_bounds i hz)

theorem sourceLaw_expSet (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i)) :
    integrableExpSet (fun y : ℝ => y) (sourceLaw i z) = univ := by
  ext theta
  simp only [integrableExpSet, mem_setOf_eq, mem_univ, iff_true]
  exact sourceLaw_exp_integrable i hz theta

theorem sourceLaw_score_moment (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i))
    (theta : ℝ) : tiltScore i theta z =
      (∫ y, y*Real.exp (-theta*y) ∂sourceLaw i z)-
        rho*mgf (fun y : ℝ => y) (sourceLaw i z) (-theta) := by
  rw [← sourceLaw_score i hz theta, mgf, ← integral_const_mul,
    ← integral_sub (sourceLaw_integrable i hz (by fun_prop))
      (sourceLaw_integrable i hz (by fun_prop))]
  congr 1
  funext y
  ring

theorem continuous_tiltScore (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i)) :
    Continuous (fun theta => tiltScore i theta z) := by
  have hm : Continuous (fun theta : ℝ => ∫ y, y*Real.exp (theta*y) ∂sourceLaw i z) := by
    apply continuous_iff_continuousAt.mpr
    intro theta
    have hd := hasDerivAt_integral_pow_mul_exp_real
      (X := fun y : ℝ => y) (μ := sourceLaw i z)
      (t := theta) (by simp only [sourceLaw_expSet i hz, interior_univ, mem_univ]) 1
    simpa only [pow_one] using hd.continuousAt
  have hg := continuous_mgf (sourceLaw_exp_integrable i hz)
  have he : (fun theta => tiltScore i theta z) = fun theta =>
      (∫ y, y*Real.exp (-theta*y) ∂sourceLaw i z)-
        rho*mgf (fun y : ℝ => y) (sourceLaw i z) (-theta) := by
    funext theta
    exact sourceLaw_score_moment i hz theta
  rw [he]
  exact (hm.comp continuous_neg).sub (continuous_const.mul (hg.comp continuous_neg))

end FCAppendix.Affine.Uniform07
