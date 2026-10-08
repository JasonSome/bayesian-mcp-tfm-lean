import FCAppendix.Finite.PPICentral

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

def gaussianSuccessPrimitive (x : ℝ) : ℝ :=
  x * cdf (gaussianReal 0 1) x + gaussianPDFReal 0 1 x

theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hh := (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp).const_mul
    (1 / Real.sqrt (2 * Real.pi))
  have he : gaussianPDFReal 0 1 = fun y => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-y ^ 2 / 2) := by
    funext y
    simp [gaussianPDFReal]
  rw [he]
  apply hh.congr_deriv
  dsimp only [Pi.pow_apply, Pi.neg_apply, id_eq]
  norm_num
  ring

theorem hasDerivAt_gaussianSuccessPrimitive (x : ℝ) :
    HasDerivAt gaussianSuccessPrimitive (cdf (gaussianReal 0 1) x) x := by
  have hh := ((hasDerivAt_id x).mul (hasDerivAt_Φ x)).add
    (hasDerivAt_standardGaussianPDF x)
  change HasDerivAt (id * (fun x => cdf (gaussianReal 0 1) x) + gaussianPDFReal 0 1) _ x
  apply hh.congr_deriv
  change 1 * cdf (gaussianReal 0 1) x + x * gaussianPDFReal 0 1 x +
    -x * gaussianPDFReal 0 1 x = cdf (gaussianReal 0 1) x
  ring

theorem integral_standardGaussianCDF (a b : ℝ) :
    (∫ x in a..b, cdf (gaussianReal 0 1) x) =
      gaussianSuccessPrimitive b - gaussianSuccessPrimitive a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_gaussianSuccessPrimitive x) (continuous_Φ.intervalIntegrable a b)

theorem gaussianSuccessPrimitive_neg_bounds {R : ℝ} (hR : 0 < R) :
    0 ≤ gaussianSuccessPrimitive (-R) ∧
      gaussianSuccessPrimitive (-R) ≤ gaussianPDFReal 0 1 R := by
  have hM := one_sub_Φ_le_φ_div hR
  change 1 - cdf (gaussianReal 0 1) R ≤ gaussianPDFReal 0 1 R / R at hM
  have hpdf : gaussianPDFReal 0 1 (-R) = gaussianPDFReal 0 1 R := by
    simp [gaussianPDFReal]
  have hneg : cdf (gaussianReal 0 1) (-R) = 1 - cdf (gaussianReal 0 1) R := Φ_neg R
  rw [gaussianSuccessPrimitive, hpdf, hneg]
  have hm := (le_div_iff₀ hR).mp hM
  constructor
  · nlinarith
  · nlinarith [cdf_le_one (gaussianReal 0 1) R]

theorem gaussianSuccessPrimitive_neg_tendsto_zero :
    Tendsto (fun R => gaussianSuccessPrimitive (-R)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun R : ℝ => R ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hexp : Tendsto (fun R : ℝ => Real.exp (-(R ^ 2 / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hsq.atTop_div_const (by norm_num)))
  have hpdf : Tendsto (fun R => gaussianPDFReal 0 1 R) atTop (𝓝 0) := by
    have hh := hexp.const_mul (1 / Real.sqrt (2 * Real.pi))
    simpa only [mul_zero, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, neg_div, one_div] using hh
  exact squeeze_zero' ((eventually_gt_atTop (0 : ℝ)).mono fun _ hR =>
    (gaussianSuccessPrimitive_neg_bounds hR).1)
    ((eventually_gt_atTop (0 : ℝ)).mono fun _ hR => (gaussianSuccessPrimitive_neg_bounds hR).2) hpdf

theorem integral_standardGaussianCDF_from_neg_tendsto (x : ℝ) :
    Tendsto (fun R => ∫ y in (-R)..x, cdf (gaussianReal 0 1) y) atTop
      (𝓝 (gaussianSuccessPrimitive x)) := by
  simp_rw [integral_standardGaussianCDF]
  simpa only [sub_zero] using gaussianSuccessPrimitive_neg_tendsto_zero.const_sub
    (gaussianSuccessPrimitive x)

end FCAppendix.Bayes
