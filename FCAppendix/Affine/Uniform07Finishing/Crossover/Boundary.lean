import FCAppendix.Affine.Uniform07Finishing.Crossover.Secant
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set Filter Topology

theorem left_comparison_derivative_lower
    {f : ℝ→ℝ} {f' left b error : ℝ}
    (hlb : left< b) (hf : HasDerivAt f f' b)
    (hmax : ∀ z∈Ioo left b, f z≤ f b+error*(b-z)) :
    -error≤ f' := by
  have hslope : Tendsto (slope f b) (𝓝[<] b) (𝓝 f') :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
  have hL : ∀ᶠ z in 𝓝[<] b, left< z :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlb)
  have hbound : ∀ᶠ z in 𝓝[<] b, -error≤ slope f b z := by
    filter_upwards [self_mem_nhdsWithin,hL] with z hzb hlz
    have hmax' := hmax z ⟨hlz,hzb⟩
    have hden : z-b<0 := sub_neg.mpr hzb
    change -error≤(z-b)⁻¹*(f z-f b)
    rw [←div_eq_inv_mul]
    apply (le_div_iff_of_neg hden).2
    nlinarith [hmax']
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hslope hbound

theorem left_canonical_comparison_of_total_optimum
    {f r : ℝ→ℝ} {left b error : ℝ}
    (hopt : ∀ z∈Ioo left b, f z+r z≤ f b+r b)
    (hcorrection : ∀ z∈Ioo left b, |r z-r b|≤ error*(b-z)) :
    ∀ z∈Ioo left b, f z≤ f b+error*(b-z) := by
  intro z hz
  have ho := hopt z hz
  have hc := (abs_le.mp (hcorrection z hz)).1
  linarith

def gapPayoff (eta w p : ℝ) (C D : ℝ→ℝ) (z : ℝ) : ℝ :=
  (w-z)*(2*(p+C z)-D z)-eta*z*D z

theorem gapPayoff_hasDerivAt
    {eta w p b c' d' : ℝ} {C D : ℝ→ℝ}
    (hC : HasDerivAt C c' b) (hD : HasDerivAt D d' b) :
    HasDerivAt (gapPayoff eta w p C D)
      ((w-b)*(2*c'-d')-
        barrierNumerator eta b (p+C b) (D b) d') b := by
  have hRent := (hasDerivAt_id b).const_sub w
  have hSuccess := ((hC.const_add p).const_mul 2).sub hD
  have hCost := ((hasDerivAt_id b).const_mul eta).mul hD
  convert! (hRent.mul hSuccess).sub hCost using 1;
    simp only [barrierNumerator,id_eq,Pi.sub_apply]; ring

theorem right_gap_reset_of_common_type_optimality
    {eta w p b left c' d' totalDen error : ℝ}
    {C D r : ℝ→ℝ}
    (hlb : left< b) (hC : HasDerivAt C c' b) (hD : HasDerivAt D d' b)
    (hgapDen : 0<2*c'-d') (hden : 2*c'-d'≤ totalDen)
    (hN : 0≤ barrierNumerator eta b (p+C b) (D b) d'-error)
    (hopt : ∀ z∈Ioo left b,
      gapPayoff eta w p C D z+r z≤ gapPayoff eta w p C D b+r b)
    (hcorrection : ∀ z∈Ioo left b, |r z-r b|≤ error*(b-z)) :
    barrierNumerator eta b (p+C b) (D b) d'/totalDen-
      error/totalDen≤ w-b := by
  have hleft := left_comparison_derivative_lower hlb (gapPayoff_hasDerivAt hC hD)
    (left_canonical_comparison_of_total_optimum hopt hcorrection)
  apply gap_reset_with_error hgapDen hden hN
  linarith [hleft]

end FCAppendix.Affine.Uniform07Finishing.Crossover
