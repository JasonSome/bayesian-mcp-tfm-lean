import FCAppendix.Probability.EmpiricalMean
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.AboveEntry
open MeasureTheory ProbabilityTheory Filter Topology Set

variable {Ω : Type*} [MeasurableSpace Ω]

lemma positivePart_sq_distance {D δ : ℝ} (hδ : 0 ≤ δ) :
    (max D 0-δ)^2 ≤ (D-δ)^2 := by
  by_cases hD : 0 ≤ D
  · rw [max_eq_left hD]
  · rw [max_eq_right (le_of_not_ge hD)]
    have hD' : D ≤ 0 := le_of_not_ge hD
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hD' hδ]

lemma balanced_positivePart_error {W S Y δ A : ℝ}
    (hδ : 0 ≤ δ) (_hA : 0 ≤ A) (hS : 0 ≤ S) (hSY : S ≤ A*|Y|) :
    (max (W-S) 0-δ)^2 ≤ 2*(W-δ)^2+2*A^2*Y^2 := by
  have hclip := positivePart_sq_distance (D := W-S) hδ
  have hSsq : S^2 ≤ A^2*Y^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hSY) (add_nonneg (by positivity) hS)
    nlinarith [sq_abs Y]
  nlinarith [sq_nonneg ((W-δ)+S)]

theorem normalized_deficit_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W S Y : Ω → ℝ) {δ A n : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hW : MemLp W 2 μ) (hS : MemLp S 2 μ) (hY : MemLp Y 2 μ)
    (hS0 : ∀ᵐ ω ∂μ, 0 ≤ S ω)
    (hSY : ∀ᵐ ω ∂μ, S ω ≤ A*|Y ω|)
    (hVW : (∫ ω, (W ω-δ)^2 ∂μ) ≤ n/4)
    (hVY : (∫ ω, (Y ω)^2 ∂μ) ≤ n) :
    (∫ ω, (max (W ω-S ω) 0/δ-1)^2 ∂μ) ≤
      (1/2+2*A^2)*n/δ^2 := by
  have hLp := (hW.sub hS).pos_part
  have he : (fun ω => (max (W ω-S ω) 0/δ-1)^2) =
      (fun ω => (max (W ω-S ω) 0-δ)^2/δ^2) := by
    funext ω
    field_simp [hδ.ne']
  rw [he,integral_div]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hδ)).2
  have hpoint : (∫ ω, (max (W ω-S ω) 0-δ)^2 ∂μ) ≤
      ∫ ω, 2*(W ω-δ)^2+2*A^2*(Y ω)^2 ∂μ := by
    apply integral_mono_ae (hLp.sub (memLp_const δ)).integrable_sq
      (((hW.sub (memLp_const δ)).integrable_sq.const_mul 2).add
        (hY.integrable_sq.const_mul (2*A^2)))
    filter_upwards [hS0,hSY] with ω hω hω'
    exact balanced_positivePart_error hδ.le hA hω hω'
  have hadd := integral_add ((hW.sub (memLp_const δ)).integrable_sq.const_mul 2)
    (hY.integrable_sq.const_mul (2*A^2))
  simp only [Pi.sub_apply] at hadd
  rw [hadd,integral_const_mul,integral_const_mul] at hpoint
  have hY' := mul_le_mul_of_nonneg_left hVY (show 0 ≤ 2*A^2 by positivity)
  nlinarith [hpoint,hVW,hY']

theorem mean_distance_le_sqrt_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) :
    |(∫ ω, Z ω ∂μ)-1| ≤ Real.sqrt (∫ ω, (Z ω-1)^2 ∂μ) := by
  have hdiff := hZ.sub (memLp_const (1:ℝ))
  have hvar := variance_nonneg (fun ω => Z ω-1) μ
  have hvariance := variance_eq_sub hdiff
  change variance (fun ω => Z ω-1) μ = _ at hvariance
  simp only [Pi.sub_apply, Pi.pow_apply] at hvariance
  rw [hvariance] at hvar
  have hmean : (∫ ω, Z ω-1 ∂μ) = (∫ ω, Z ω ∂μ)-1 := by
    rw [integral_sub (hZ.integrable (by norm_num)) (integrable_const _)]; simp
  rw [hmean] at hvar
  have hnon : 0 ≤ ∫ ω, (Z ω-1)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  apply (Real.le_sqrt (abs_nonneg _) hnon).2
  simpa only [sq_abs,Pi.pow_apply] using (sub_nonneg.mp hvar)

theorem positive_probability_complement_le_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hm : Measurable Z) (hZ : MemLp Z 2 μ)
    (hZ0 : ∀ᵐ ω ∂μ, 0 ≤ Z ω) :
    0 ≤ 1-μ.real {ω | 0 < Z ω} ∧
      1-μ.real {ω | 0 < Z ω} ≤ ∫ ω, (Z ω-1)^2 ∂μ := by
  have hs : MeasurableSet {ω | 0 < Z ω} := measurableSet_lt measurable_const hm
  have hc : 1-μ.real {ω | 0 < Z ω} = μ.real ({ω | 0 < Z ω}ᶜ) :=
    (probReal_compl_eq_one_sub hs).symm
  rw [hc]
  refine ⟨measureReal_nonneg,?_⟩
  have he : μ.real ({ω | 0 < Z ω}ᶜ) =
      ∫ ω, ({ω | 0 < Z ω}ᶜ).indicator (fun _ => (1:ℝ)) ω ∂μ := by
    rw [integral_indicator_const _ hs.compl,smul_eq_mul,mul_one]
  rw [he]
  apply integral_mono_ae ((integrable_const (1:ℝ)).indicator hs.compl)
    (hZ.sub (memLp_const (1:ℝ))).integrable_sq
  filter_upwards [hZ0] with ω hω
  by_cases hp : 0 < Z ω
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < Z ω}ᶜ from by simpa using hp)]
    exact sq_nonneg _
  · have hz : Z ω=0 := le_antisymm (le_of_not_gt hp) hω
    simp [hz]

theorem ratio_tendsto_one_of_L2
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (Z : (m : ℕ) → Ω m → ℝ)
    (hm : ∀ m, Measurable (Z m)) (hZ : ∀ m, MemLp (Z m) 2 (μ m))
    (hZ0 : ∀ m, ∀ᵐ ω ∂μ m, 0 ≤ Z m ω)
    (herr : Tendsto (fun m => ∫ ω, (Z m ω-1)^2 ∂μ m) atTop (𝓝 0)) :
    Tendsto (fun m => (∫ ω, Z m ω ∂μ m)) atTop (𝓝 1) ∧
    Tendsto (fun m => (μ m).real {ω | 0 < Z m ω}) atTop (𝓝 1) ∧
    Tendsto (fun m => (∫ ω, (Z m ω)^2 ∂μ m)) atTop (𝓝 1) ∧
    Tendsto (fun m => (∫ ω, Z m ω ∂μ m)^2 /
      ((μ m).real {ω | 0 < Z m ω}*(∫ ω, (Z m ω)^2 ∂μ m))) atTop (𝓝 1) := by
  have hmeanErr : Tendsto (fun m => |(∫ ω, Z m ω ∂μ m)-1|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun m => mean_distance_le_sqrt_error (μ m) (hZ m))
    simpa using herr.sqrt
  have hmean : Tendsto (fun m => ∫ ω, Z m ω ∂μ m) atTop (𝓝 1) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hmeanErr)
  have hprobErr : Tendsto (fun m => 1-(μ m).real {ω | 0 < Z m ω}) atTop (𝓝 0) :=
    squeeze_zero
      (fun m => (positive_probability_complement_le_error (μ m) (hm m) (hZ m) (hZ0 m)).1)
      (fun m => (positive_probability_complement_le_error (μ m) (hm m) (hZ m) (hZ0 m)).2) herr
  have hprob : Tendsto (fun m => (μ m).real {ω | 0 < Z m ω}) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hprobErr
  have hsecondIdentity (m : ℕ) :
      (∫ ω, (Z m ω)^2 ∂μ m) =
      (∫ ω, (Z m ω-1)^2 ∂μ m)+2*(∫ ω, Z m ω ∂μ m)-1 := by
    have he : (fun ω => (Z m ω-1)^2) =
        (fun ω => (Z m ω)^2-2*Z m ω+1) := by funext ω; ring
    have hadd := integral_add ((hZ m).integrable_sq.sub
      (((hZ m).integrable (by norm_num)).const_mul 2)) (integrable_const (1 : ℝ))
    have hsub := integral_sub (hZ m).integrable_sq
      (((hZ m).integrable (by norm_num)).const_mul 2)
    simp only [Pi.sub_apply] at hadd
    rw [he,hadd,hsub,integral_const_mul]
    simp
    ring
  have hsecond : Tendsto (fun m => ∫ ω, (Z m ω)^2 ∂μ m) atTop (𝓝 1) := by
    simp_rw [hsecondIdentity]
    convert! (herr.add (tendsto_const_nhds.mul hmean)).sub_const 1 using 1; norm_num
  refine ⟨hmean,hprob,hsecond,?_⟩
  convert! (hmean.pow 2).div (hprob.mul hsecond) (by norm_num : (1:ℝ)*1 ≠ 0) using 1
  norm_num

end FCAppendix.Affine.Uniform06.AboveEntry
