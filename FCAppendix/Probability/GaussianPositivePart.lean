import FCAppendix.Probability.GaussianMeanConvergence
import FCAppendix.PayOnce.GaussianTruncatedMoments

noncomputable section
namespace FCAppendix.PayOnce.GaussianResponse
open MeasureTheory ProbabilityTheory Set

theorem integral_normal_positivePart (y : ℝ) :
    (∫ z, max (y-z) 0 ∂gaussianReal 0 1) = Bayes.gaussianSuccessPrimitive y := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have he : (fun z : ℝ => gaussianPDFReal 0 1 z * max (y-z) 0) =
      (Iic y).indicator (fun z => y*gaussianPDFReal 0 1 z-z*gaussianPDFReal 0 1 z) := by
    funext z
    by_cases hz : z ≤ y
    · simp only [indicator,mem_Iic,if_pos hz,max_eq_left (sub_nonneg.mpr hz)]
      ring
    · simp only [indicator,mem_Iic,if_neg hz,max_eq_right (sub_nonpos.mpr (le_of_not_ge hz)),mul_zero]
  rw [he,integral_indicator measurableSet_Iic,
    integral_sub ((integrable_gaussianPDFReal 0 1).const_mul y).integrableOn
      integrable_mul_normalPDF.integrableOn,
    integral_const_mul,integral_normalPDF_Iic,integral_mul_normalPDF_Iic]
  exact sub_neg_eq_add _ _

end FCAppendix.PayOnce.GaussianResponse

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem positivePart_sq_le (y z : ℝ) : (max (y-z) 0)^2 ≤ 2*y^2+2*z^2 := by
  by_cases hz : z ≤ y
  · rw [max_eq_left (sub_nonneg.mpr hz)]
    nlinarith [sq_nonneg (y+z)]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hz))]
    norm_num only [zero_pow,OfNat.ofNat_ne_zero]
    positivity

theorem probabilityMeasure_positivePart_mean_tendsto
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hLp : ∀ m, MemLp (fun z : ℝ => z) 2 (μ m : Measure ℝ))
    (hν : MemLp (fun z : ℝ => z) 2 (ν : Measure ℝ))
    (K : ℝ) (hK : ∀ m, (∫ z : ℝ, z^2 ∂(μ m : Measure ℝ)) ≤ K) (y : ℝ) :
    Tendsto (fun m => ∫ z : ℝ, max (y-z) 0 ∂(μ m : Measure ℝ)) atTop
      (𝓝 (∫ z : ℝ, max (y-z) 0 ∂(ν : Measure ℝ))) := by
  have hc : Continuous (fun z : ℝ => max (y-z) 0) := by fun_prop
  let μ' := fun m => (μ m).map hc.measurable.aemeasurable
  let ν' := ν.map hc.measurable.aemeasurable
  have hweak' : Tendsto μ' atTop (𝓝 ν') :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hweak hc
  have hLp' m : MemLp (fun z : ℝ => z) 2 (μ' m : Measure ℝ) := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id hc.measurable.aemeasurable).mpr
    exact ((memLp_const y).sub (hLp m)).pos_part
  have hν' : MemLp (fun z : ℝ => z) 2 (ν' : Measure ℝ) := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id hc.measurable.aemeasurable).mpr
    exact ((memLp_const y).sub hν).pos_part
  have hK' m : (∫ z : ℝ, z^2 ∂(μ' m : Measure ℝ)) ≤ 2*y^2+2*K := by
    change (∫ z : ℝ, z^2 ∂(μ m : Measure ℝ).map (fun z => max (y-z) 0)) ≤ _
    rw [integral_map hc.measurable.aemeasurable (by fun_prop)]
    have hi : Integrable (fun z : ℝ => (max (y-z) 0)^2) (μ m : Measure ℝ) :=
      ((memLp_const y).sub (hLp m)).pos_part.integrable_sq
    have hj : Integrable (fun z : ℝ => 2*y^2+2*z^2) (μ m : Measure ℝ) :=
      (integrable_const _).add ((hLp m).integrable_sq.const_mul 2)
    have hh := integral_mono hi hj (positivePart_sq_le y)
    rw [integral_add (integrable_const _) ((hLp m).integrable_sq.const_mul 2),
      integral_const_mul,integral_const,probReal_univ,one_smul] at hh
    simp only [integral_const_mul] at hh
    linarith [hK m]
  have hh := probabilityMeasure_mean_tendsto_of_secondMoment_bound μ' ν' hweak' hLp' hν'
    (2*y^2+2*K) hK'
  convert hh using 1
  · funext m
    exact (integral_map hc.measurable.aemeasurable aestronglyMeasurable_id).symm
  · congr 1
    exact (integral_map hc.measurable.aemeasurable aestronglyMeasurable_id).symm

theorem gaussian_positivePart_mean_tendsto
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (X : (m : ℕ) → Ω m → ℝ) (hm : ∀ m, Measurable (X m))
    (hLp : ∀ m, MemLp (X m) 2 (μ m)) (K : ℝ)
    (hK : ∀ m, (∫ ω, (X m ω)^2 ∂μ m) ≤ K)
    (hcdf : ∀ z : ℝ, Tendsto (fun m => cdf ((μ m).map (X m)) z) atTop
      (𝓝 (cdf (gaussianReal 0 1) z))) (y : ℝ) :
    Tendsto (fun m => ∫ ω, max (y-X m ω) 0 ∂μ m) atTop
      (𝓝 (Bayes.gaussianSuccessPrimitive y)) := by
  let laws : ℕ → ProbabilityMeasure ℝ := fun m =>
    ⟨(μ m).map (X m),Measure.isProbabilityMeasure_map (hm m).aemeasurable⟩
  let normal : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1,inferInstance⟩
  have hweak := probabilityMeasure_tendsto_of_cdf laws normal hcdf
  have hL m : MemLp (fun z : ℝ => z) 2 (laws m : Measure ℝ) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hm m).aemeasurable).mpr (hLp m)
  have hLK m : (∫ z : ℝ, z^2 ∂(laws m : Measure ℝ)) ≤ K := by
    change (∫ z : ℝ, z^2 ∂(μ m).map (X m)) ≤ K
    rw [integral_map (hm m).aemeasurable (by fun_prop)]
    exact hK m
  have hh := probabilityMeasure_positivePart_mean_tendsto laws normal hweak hL
    (memLp_id_gaussianReal 2) K hLK y
  have hc : Measurable (fun z : ℝ => max (y-z) 0) := by fun_prop
  simpa only [laws,normal,ProbabilityMeasure.coe_mk,
    integral_map (hm _).aemeasurable hc.aestronglyMeasurable,
    PayOnce.GaussianResponse.integral_normal_positivePart] using hh

theorem gaussian_positivePart_mean_tendsto_of_eventual_bound
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (X : (m : ℕ) → Ω m → ℝ) (K : ℝ)
    (hbound : ∀ᶠ m in atTop, Measurable (X m) ∧ MemLp (X m) 2 (μ m) ∧
      (∫ ω, (X m ω)^2 ∂μ m) ≤ K)
    (hcdf : ∀ z : ℝ, Tendsto (fun m => cdf ((μ m).map (X m)) z) atTop
      (𝓝 (cdf (gaussianReal 0 1) z))) (y : ℝ) :
    Tendsto (fun m => ∫ ω, max (y-X m ω) 0 ∂μ m) atTop
      (𝓝 (Bayes.gaussianSuccessPrimitive y)) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp hbound
  apply (tendsto_add_atTop_iff_nat T).mp
  exact gaussian_positivePart_mean_tendsto (fun m => μ (m+T)) (fun m => X (m+T))
    (fun m => (hT (m+T) (by omega)).1) (fun m => (hT (m+T) (by omega)).2.1) K
    (fun m => (hT (m+T) (by omega)).2.2)
    (fun z => (hcdf z).comp (tendsto_add_atTop_nat T)) y

theorem integral_positivePart_parameter_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (y z : ℝ) :
    |(∫ ω, max (y-X ω) 0 ∂μ)-(∫ ω, max (z-X ω) 0 ∂μ)| ≤ |y-z| := by
  have hy : Integrable (fun ω => max (y-X ω) 0) μ :=
    ((integrable_const y).sub hX).sup (integrable_const 0)
  have hz : Integrable (fun ω => max (z-X ω) 0) μ :=
    ((integrable_const z).sub hX).sup (integrable_const 0)
  rw [← integral_sub hy hz]
  have hh := (abs_integral_le_integral_abs (f := fun ω =>
    max (y-X ω) 0-max (z-X ω) 0)).trans
    (integral_mono (hy.sub hz).abs (integrable_const |y-z|) (fun ω => by
      simpa only [sub_sub_sub_cancel_right] using abs_max_sub_max_le_abs (y-X ω) (z-X ω) 0))
  simpa only [integral_const,probReal_univ,one_smul] using hh

theorem gaussian_positivePart_moving_mean_tendsto
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (X : (m : ℕ) → Ω m → ℝ) (K : ℝ)
    (hbound : ∀ᶠ m in atTop, Measurable (X m) ∧ MemLp (X m) 2 (μ m) ∧
      (∫ ω, (X m ω)^2 ∂μ m) ≤ K)
    (hcdf : ∀ z : ℝ, Tendsto (fun m => cdf ((μ m).map (X m)) z) atTop
      (𝓝 (cdf (gaussianReal 0 1) z)))
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) :
    Tendsto (fun m => ∫ ω, max (y m-X m ω) 0 ∂μ m) atTop
      (𝓝 (Bayes.gaussianSuccessPrimitive z)) := by
  have hfixed := gaussian_positivePart_mean_tendsto_of_eventual_bound μ X K hbound hcdf z
  have he : Tendsto (fun m => (∫ ω, max (y m-X m ω) 0 ∂μ m)-
      (∫ ω, max (z-X m ω) 0 ∂μ m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_
      (show Tendsto (fun m => |y m-z|) atTop (𝓝 0) from by
        simpa only [sub_self,abs_zero] using (hy.sub_const z).abs)
    filter_upwards [hbound] with m hm
    simpa only [Real.norm_eq_abs] using
      integral_positivePart_parameter_bound (μ m) (hm.2.1.integrable (by norm_num)) (y m) z
  simpa only [sub_add_cancel,zero_add] using he.add hfixed

end FCAppendix.Probability
