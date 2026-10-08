import FCAppendix.Probability.ExponentialTilt
import FCAppendix.PayOnce.GaussianTiltPrefactor

noncomputable section
namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Set Filter Topology
open PayOnce.GaussianTilt
variable {Ω : Type*} [MeasurableSpace Ω]

def standardizedTiltedLaw (μ : Measure Ω) (X : Ω → ℝ) (u r s : ℝ) : Measure ℝ :=
  (μ.tilted (fun ω => u*X ω)).map (fun ω => (X ω-r)/s)

theorem isProbabilityMeasure_standardizedTiltedLaw
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {u r s : ℝ} (ht : Integrable (fun ω => Real.exp (u*X ω)) μ) :
    IsProbabilityMeasure (standardizedTiltedLaw μ X u r s) := by
  letI := isProbabilityMeasure_tilted ht
  exact Measure.isProbabilityMeasure_map ((hX.sub_const r).div_const s).aemeasurable

theorem lower_tail_eq_standardized_tilted_prefactor
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {u r s : ℝ} (ht : Integrable (fun ω => Real.exp (u*X ω)) μ) (hs : 0 < s) :
    μ.real {ω | X ω ≤ r} = Real.exp (cgf X μ u-u*r) *
      ∫ z, negativeHalfExp (-u*s) z ∂standardizedTiltedLaw μ X u r s := by
  have he : MeasurableSet {ω | X ω ≤ r} := measurableSet_le hX measurable_const
  rw [measureReal_eq_reverse_tilt μ ht he,standardizedTiltedLaw,
    integral_map ((hX.sub_const r).div_const s).aemeasurable
      (measurable_negativeHalfExp _).aestronglyMeasurable,
    ← integral_const_mul,← integral_indicator he]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hx : X ω ≤ r
  · have hz : (X ω-r)/s ∈ Iic (0:ℝ) := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hs.le
    rw [indicator_of_mem (show ω ∈ {ω | X ω ≤ r} from hx),negativeHalfExp,indicator_of_mem hz,← Real.exp_add]
    congr 1
    field_simp [hs.ne']
    ring
  · have hz : (X ω-r)/s ∉ Iic (0:ℝ) := by
      exact not_le.mpr (div_pos (sub_pos.mpr (lt_of_not_ge hx)) hs)
    rw [indicator_of_notMem (show ω ∉ {ω | X ω ≤ r} from hx),negativeHalfExp,indicator_of_notMem hz,mul_zero]

theorem strict_lower_tail_eq_standardized_tilted_prefactor
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {u r s : ℝ} (ht : Integrable (fun ω => Real.exp (u*X ω)) μ) (hs : 0 < s) :
    μ.real {ω | X ω < r} = Real.exp (cgf X μ u-u*r) *
      ∫ z, (Iio (0:ℝ)).indicator (fun z => Real.exp ((-u*s)*z)) z
        ∂standardizedTiltedLaw μ X u r s := by
  have he : MeasurableSet {ω | X ω < r} := measurableSet_lt hX measurable_const
  have hm : Measurable ((Iio (0:ℝ)).indicator (fun z => Real.exp ((-u*s)*z))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).indicator measurableSet_Iio
  rw [measureReal_eq_reverse_tilt μ ht he,standardizedTiltedLaw,
    integral_map ((hX.sub_const r).div_const s).aemeasurable hm.aestronglyMeasurable,
    ← integral_const_mul,← integral_indicator he]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hx : X ω < r
  · have hz : (X ω-r)/s ∈ Iio (0:ℝ) := div_neg_of_neg_of_pos (sub_neg.mpr hx) hs
    rw [indicator_of_mem (show ω ∈ {ω | X ω < r} from hx),indicator_of_mem hz,← Real.exp_add]
    congr 1
    field_simp [hs.ne']
    ring
  · have hz : (X ω-r)/s ∉ Iio (0:ℝ) := by
      exact not_lt.mpr (div_nonneg (sub_nonneg.mpr (le_of_not_gt hx)) hs.le)
    rw [indicator_of_notMem (show ω ∉ {ω | X ω < r} from hx),indicator_of_notMem hz,mul_zero]

end FCAppendix.ExponentialTilt
