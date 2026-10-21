import FCAppendix.Affine.Uniform06.EntryVector
import FCAppendix.Affine.Uniform06.EntryGaussian
import FCAppendix.Affine.Hybrid.Seed

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryGaussianLaw
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.PayOnce.GaussianResponse
open FCAppendix.Affine.Uniform06.EntryVector
abbrev standardNormal : Measure ℝ := gaussianReal 0 1
local notation "Φ" => cdf standardNormal

def sumFold (a b : ℝ) (p : ℝ×ℝ) : ℝ := a*p.1+b*|p.2|
def law (a b : ℝ) : Measure ℝ := (standardNormal.prod standardNormal).map (sumFold a b)

lemma continuous_sumFold (a b : ℝ) : Continuous (sumFold a b) := by unfold sumFold; fun_prop
instance probability_law (a b : ℝ) : IsProbabilityMeasure (law a b) := by
  unfold law
  exact Measure.isProbabilityMeasure_map (μ := standardNormal.prod standardNormal)
    (continuous_sumFold a b).measurable.aemeasurable

theorem law_eq_standardGaussian_map (a b : ℝ) :
    law a b=(stdGaussian (EuclideanSpace ℝ (Fin 2))).map (fold a b) := by
  have hp := measurePreserving_piFinTwo (fun _ : Fin 2 => standardNormal)
  unfold law
  rw [← hp.map_eq,Measure.map_map (continuous_sumFold a b).measurable hp.measurable,
    ← map_pi_eq_stdGaussian,
    Measure.map_map (continuous_fold a b).measurable (by fun_prop)]
  congr 1

theorem cdf_eq_standardGaussian_sublevel (a b s : ℝ) :
    cdf (law a b) s=
      (stdGaussian (EuclideanSpace ℝ (Fin 2))).real (foldedSublevel a b s) := by
  haveI : IsProbabilityMeasure ((stdGaussian (EuclideanSpace ℝ (Fin 2))).map (fold a b)) := by
    rw [← law_eq_standardGaussian_map]
    infer_instance
  rw [law_eq_standardGaussian_map,cdf_eq_real,Measure.real,
    Measure.map_apply (continuous_fold a b).measurable measurableSet_Iic]
  rfl

theorem cdf_eq_integral {a : ℝ} (ha : 0 < a) (b s : ℝ) :
    cdf (law a b) s=∫ y, Φ ((s-b*|y|)/a) ∂standardNormal := by
  let T : Set (ℝ×ℝ) := {p | sumFold a b p ≤ s}
  have hT : MeasurableSet T := measurableSet_le (continuous_sumFold a b).measurable measurable_const
  have hI : Integrable (T.indicator (fun _ => (1:ℝ))) (standardNormal.prod standardNormal) :=
    (integrable_const (1:ℝ)).indicator hT
  have he : cdf (law a b) s=∫ p, T.indicator (fun _ => (1:ℝ)) p ∂standardNormal.prod standardNormal := by
    rw [cdf_eq_real,law,Measure.real,
      Measure.map_apply (continuous_sumFold a b).measurable measurableSet_Iic,
      integral_indicator_const _ hT,smul_eq_mul,mul_one]
    rfl
  rw [he,integral_prod_symm _ hI]
  apply integral_congr_ae
  filter_upwards [] with y
  have hset : (fun x => T.indicator (fun _ => (1:ℝ)) (x,y)) =
      (Iic ((s-b*|y|)/a)).indicator (fun _ => (1:ℝ)) := by
    funext x
    have hh : a*x+b*|y| ≤ s ↔ x ≤ (s-b*|y|)/a := by
      rw [le_div_iff₀ ha]
      constructor <;> intro h <;> nlinarith
    by_cases hx : x ≤ (s-b*|y|)/a
    · rw [Set.indicator_of_mem (show (x,y) ∈ T from hh.mpr hx),Set.indicator_of_mem (show x ∈ Iic ((s-b*|y|)/a) from hx)]
    · rw [Set.indicator_of_notMem (show (x,y) ∉ T from fun h => hx (hh.mp h)),
        Set.indicator_of_notMem (show x ∉ Iic ((s-b*|y|)/a) from hx)]
  rw [hset,integral_indicator_const _ measurableSet_Iic,smul_eq_mul,mul_one,← cdf_eq_real]

theorem singleton_null {a : ℝ} (ha : a ≠ 0) (b s : ℝ) : law a b {s}=0 := by
  letI : NullSingletonClass standardNormal := nullSingletonClass_gaussianReal (by norm_num)
  have hT : MeasurableSet {p : ℝ×ℝ | sumFold a b p ≠ s} :=
    (measurableSet_eq_fun (continuous_sumFold a b).measurable measurable_const).compl
  have hprod : ∀ᵐ p ∂standardNormal.prod standardNormal, sumFold a b p ≠ s := by
    apply (Measure.ae_prod_iff_ae_ae hT).mpr
    apply (Measure.ae_ae_comm hT).mpr
    apply ae_of_all
    intro y
    filter_upwards [standardNormal.ae_ne ((s-b*|y|)/a)] with x hx hEq
    apply hx
    apply (eq_div_iff ha).2
    dsimp only [sumFold] at hEq
    nlinarith
  rw [law,Measure.map_apply (continuous_sumFold a b).measurable (measurableSet_singleton s)]
  exact measure_eq_zero_iff_ae_notMem.mpr hprod

theorem cdf_moving_tendsto (a b s : ℕ → ℝ) {a0 b0 s0 : ℝ}
    (ha0 : 0 < a0) (ha : ∀ m, 0 < a m)
    (haL : Tendsto a atTop (𝓝 a0)) (hbL : Tendsto b atTop (𝓝 b0))
    (hsL : Tendsto s atTop (𝓝 s0)) :
    Tendsto (fun m => cdf (law (a m) (b m)) (s m)) atTop (𝓝 (cdf (law a0 b0) s0)) := by
  simp_rw [cdf_eq_integral (ha _),cdf_eq_integral ha0]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
  · intro m
    exact ((continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_normalCDF x).continuousAt).comp
      ((continuous_const.sub (continuous_const.mul continuous_abs)).div_const _)).aestronglyMeasurable
  · exact integrable_const _
  · intro m
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (cdf_nonneg standardNormal _)]
      exact cdf_le_one standardNormal _
  · apply Eventually.of_forall
    intro y
    exact (hasDerivAt_normalCDF ((s0-b0*|y|)/a0)).continuousAt.tendsto.comp
      ((hsL.sub (hbL.mul_const |y|)).div haL ha0.ne')

theorem cdf_pos {a : ℝ} (ha : 0 < a) (b s : ℝ) : 0 < cdf (law a b) s := by
  rw [cdf_eq_standardGaussian_sublevel]
  have hcorr : FCAppendix.CorrelationMatrix.corr 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [FCAppendix.CorrelationMatrix.corr]
  haveI := FCAppendix.BoundedVectorApproximation.gaussian_isOpenPosMeasure
    (1 : Matrix (Fin 2) (Fin 2) ℝ) (by
      rw [← hcorr]
      exact FCAppendix.CorrelationMatrix.corr_posDef (r := 0) (by norm_num))
  haveI : (stdGaussian (EuclideanSpace ℝ (Fin 2))).IsOpenPosMeasure := by
    simpa only [multivariateGaussian_zero_one] using
      (inferInstance : (multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsOpenPosMeasure)
  let U : Set (EuclideanSpace ℝ (Fin 2)) := {x | fold a b x < s}
  have hU : IsOpen U := isOpen_lt (continuous_fold a b) continuous_const
  have hne : U.Nonempty := by
    refine ⟨WithLp.toLp 2 ![s/a-1,0],?_⟩
    change a*(s/a-1)+b*|0| < s
    rw [abs_zero,mul_zero,add_zero,mul_sub,mul_div_cancel₀ _ ha.ne',mul_one]
    linarith
  have hsub : U ⊆ foldedSublevel a b s := fun _ hx => (show fold a b _ ≤ s from le_of_lt hx)
  exact ENNReal.toReal_pos
    (ne_of_gt ((hU.measure_pos _ hne).trans_le (measure_mono hsub))) (measure_ne_top _ _)

theorem memLp_sumFold (a b : ℝ) (p : NNReal) : MemLp (sumFold a b) p (standardNormal.prod standardNormal) := by
  have hx : MemLp (fun z : ℝ×ℝ => z.1) p (standardNormal.prod standardNormal) :=
    (memLp_id_gaussianReal p).comp_measurePreserving measurePreserving_fst
  have hy : MemLp (fun z : ℝ×ℝ => z.2) p (standardNormal.prod standardNormal) :=
    (memLp_id_gaussianReal p).comp_measurePreserving measurePreserving_snd
  convert! (hx.const_mul a).add (hy.abs.const_mul b) using 1

end FCAppendix.Affine.Uniform06.EntryGaussianLaw
