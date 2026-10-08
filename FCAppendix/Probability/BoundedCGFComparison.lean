import FCAppendix.Probability.MeanZeroTilt

namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Set Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω]

theorem exp_mul_gap_lower {a u x y : ℝ}
    (hu : u ≤ 0) (hua : -a ≤ u) (hxy : x ≤ y) (hy : y ∈ Icc (0:ℝ) 1) :
    Real.exp (-a)*|u| *(y-x) ≤ Real.exp (u*x)-Real.exp (u*y) := by
  have harg : u*y+u*(x-y) = u*x := by ring
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u*(x-y))) (Real.exp_pos (u*y)).le
  rw [← Real.exp_add,harg] at he
  have huy : -a ≤ u*y := hua.trans (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hu (sub_nonneg.mpr hy.2)])
  have ha := Real.exp_le_exp.mpr huy
  rw [abs_of_nonpos hu]
  nlinarith [mul_le_mul_of_nonneg_right ha (mul_nonneg (neg_nonneg.mpr hu) (sub_nonneg.mpr hxy))]

theorem cgf_gap_lower_of_unitInterval_order
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1)
    (hYb : ∀ᵐ ω ∂μ, Y ω ∈ Icc (0:ℝ) 1)
    (hXY : ∀ᵐ ω ∂μ, X ω ≤ Y ω) {a u : ℝ} (hu : u ≤ 0) (hua : -a ≤ u) :
    Real.exp (-a)*|u| *(∫ ω, Y ω-X ω ∂μ) ≤ cgf X μ u-cgf Y μ u := by
  have hXi := Integrable.of_mem_Icc 0 1 hX.aemeasurable hXb
  have hYi := Integrable.of_mem_Icc 0 1 hY.aemeasurable hYb
  have hXe := integrable_exp_mul_of_bounded μ hX.aemeasurable hXb u
  have hYe := integrable_exp_mul_of_bounded μ hY.aemeasurable hYb u
  have hXp := mgf_pos hXe
  have hYp := mgf_pos hYe
  have hXone : mgf X μ u ≤ 1 := by
    have hh := integral_mono_ae hXe (integrable_const (1:ℝ)) (by
      filter_upwards [hXb] with ω hω
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hu hω.1))
    simpa only [integral_const,probReal_univ,one_smul,mgf] using hh
  have hi : Real.exp (-a)*|u| *(∫ ω, Y ω-X ω ∂μ) ≤ mgf X μ u-mgf Y μ u := by
    have hh := integral_mono_ae ((hYi.sub hXi).const_mul (Real.exp (-a)*|u|))
      (hXe.sub hYe) (by
        filter_upwards [hYb,hXY] with ω hω hxy
        exact exp_mul_gap_lower hu hua hxy hω)
    simpa only [integral_const_mul,Pi.sub_apply,integral_sub hXe hYe,mgf] using hh
  have hgap : 0 ≤ Real.exp (-a)*|u| *(∫ ω, Y ω-X ω ∂μ) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      (integral_nonneg_of_ae (hXY.mono fun _ h => sub_nonneg.mpr h))
  have hlog := Real.log_le_sub_one_of_pos (div_pos hYp hXp)
  rw [Real.log_div hYp.ne' hXp.ne'] at hlog
  have hfrac : mgf Y μ u/mgf X μ u-1 ≤ -(Real.exp (-a)*|u| *(∫ ω, Y ω-X ω ∂μ)) := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hXp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hXone hgap]
  exact (by dsimp only [cgf]; linarith [hlog.trans hfrac])

theorem tilted_rate_gap_lower_of_unitInterval_order
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1)
    (hYb : ∀ᵐ ω ∂μ, Y ω ∈ Icc (0:ℝ) 1)
    (hXY : ∀ᵐ ω ∂μ, X ω ≤ Y ω) {a u v r q : ℝ}
    (hu : u ≤ 0) (hua : -a ≤ u)
    (hmean : (∫ ω, Y ω ∂μ.tilted (fun ω => v*Y ω)) = q) :
    Real.exp (-a)*|u| *(∫ ω, Y ω-X ω ∂μ)+|u| *(r-q) ≤
      (v*q-cgf Y μ v)-(u*r-cgf X μ u) := by
  have hg := cgf_gap_lower_of_unitInterval_order μ hX hY hXb hYb hXY hu hua
  have hm := cgf_sub_linear_min_of_tilted_mean μ hY hYb hmean u
  rw [abs_of_nonpos hu] at hg ⊢
  nlinarith

end FCAppendix.ExponentialTilt
