import FCAppendix.Affine.Uniform06.RootDerivativeIntegral
import FCAppendix.Affine.Uniform06.LiteralPrefixStieltjes

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.MaskedRootDerivative

open MeasureTheory Set Filter Topology LowBody
open LiteralExperiment ActualRootDerivative

attribute [local irreducible] FCAppendix.Affine.EqualCapacity.positiveMarginal derivative

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def slope (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) (b : ℝ) : ℝ :=
  if j ∈ T.support \ E then derivative ξ (small T) (maskedBids T B E) j b else 0

omit [Fintype ι] in
theorem masked_update (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) (hj : j ∈ T.support \ E) (b : ℝ) :
    maskedBids T (Function.update B j b) E=Function.update (maskedBids T B E) j b := by
  funext k
  by_cases hk : k=j
  · simp [hk,maskedBids,hj]
  · simp [maskedBids,Function.update_of_ne hk]

omit [Fintype ι] in
theorem masked_update_absent (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) (hj : j ∉ T.support \ E) (b : ℝ) :
    maskedBids T (Function.update B j b) E=maskedBids T B E := by
  funext k
  by_cases hk : k=j
  · simp [hk,maskedBids,hj]
  · simp [maskedBids,Function.update_of_ne hk]

theorem complement_zero_absent (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) (hj : j ∉ T.support \ E) :
    complementMarginal ξ T B E j=0 := by
  unfold complementMarginal EqualCapacity.positiveMarginal
  apply EqualCapacity.onSupport_outside
  simp [Existence.PayOnceBounded.mem_positiveSupport,maskedBids,hj]

theorem actual_masked_derivatives_ae {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι) (j : ι)
    (hB : ∀ k,k ≠ j → 0 ≤ B k) :
    ∀ᵐ b ∂volume, 0 < b →
      HasDerivAt (fun a => complementMarginal ξ T (Function.update B j a) E j)
        (slope ξ T B E j b) b ∧
      HasDerivAt (fun a => (complementMarginal ξ T (Function.update B j a) E j)^2)
        (2*complementMarginal ξ T (Function.update B j b) E j*slope ξ T B E j b) b := by
  by_cases hj : j ∈ T.support \ E
  · have hmask : ∀ k,k ≠ j → 0 ≤ maskedBids T B E k := by
      intro k hk
      unfold maskedBids
      split_ifs
      · exact hB k hk
      · rfl
    filter_upwards [actual_first_second_derivatives_ae hξ hξ1 (small T)
      (maskedBids T B E) j hmask] with b hb hb0
    simpa only [complementMarginal,masked_update T B E j hj,
      slope,if_pos hj,marginal] using! hb hb0
  · exact ae_of_all _ fun b _ => by
      simp only [complement_zero_absent ξ T _ E j hj,slope,if_neg hj,mul_zero,
        zero_pow (by decide : 2 ≠ 0)]
      exact ⟨hasDerivAt_const b 0,hasDerivAt_const b 0⟩

theorem measurable_slope {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (E : Finset ι) (j : ι) :
    Measurable (fun p : (ι → ℝ) × ℝ => slope ξ T p.1 E j p.2) := by
  by_cases hj : j ∈ T.support \ E
  · simp only [slope,if_pos hj]
    exact (RootDerivativeIntegral.measurable_derivative ξ (small T) j hξ hξ1).comp
      (((LiteralKernelMeasurable.measurable_maskedBids T E).comp measurable_fst).prodMk measurable_snd)
  · simp only [slope,if_neg hj]
    exact measurable_const

theorem actual_masked_fixed_price_ae {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (E : Finset ι) (j : ι)
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ B ∂μ,∀ k,0 ≤ B k) :
    ∀ᵐ b ∂volume,0 < b → ∀ᵐ B ∂μ,
      HasDerivAt (fun a => complementMarginal ξ T (Function.update B j a) E j)
        (slope ξ T B E j b) b := by
  by_cases hj : j ∈ T.support \ E
  · have hm : Measurable (fun B : ι → ℝ => maskedBids T B E) :=
      LiteralKernelMeasurable.measurable_maskedBids T E
    have hnon : ∀ᵐ B ∂μ.map (fun B => maskedBids T B E),∀ k,0 ≤ B k := by
      apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
      filter_upwards [hμ] with B hB k
      unfold maskedBids
      split_ifs
      · exact hB k
      · rfl
    filter_upwards [RootDerivativeIntegral.actual_fixed_price_derivative_ae hξ hξ1
      (small T) j (μ.map (fun B => maskedBids T B E)) hnon] with b hb hb0
    have hh := ae_of_ae_map hm.aemeasurable (hb hb0)
    filter_upwards [hh] with B hB
    simpa only [complementMarginal,masked_update T B E j hj,slope,if_pos hj,marginal] using! hB
  · exact ae_of_all _ fun b _ => ae_of_all _ fun B => by
      simp only [complement_zero_absent ξ T _ E j hj,slope,if_neg hj]
      exact hasDerivAt_const b 0

theorem masked_slope_bounds {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hb : 0 < b)
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι) (j : ι) :
    0 ≤ slope ξ T B E j b ∧ slope ξ T B E j b ≤ 1/(ξ*b) := by
  unfold slope
  split_ifs
  · exact actual_derivative_bounds hξ hξ1 (small T) (maskedBids T B E) j hb
  · exact ⟨le_rfl,by positivity⟩

end FCAppendix.Affine.Uniform06.MaskedRootDerivative
