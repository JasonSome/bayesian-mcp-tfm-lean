import FCAppendix.PayOnce.KernelPriceSlope
import FCAppendix.PayOnce.KernelLawConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory ProbabilityTheory Filter Topology Set CommonList
open OwnImpact KernelTailEvent KernelLawConvergence

theorem integrable_real_kernel (G : Measure ℝ) [IsFiniteMeasure G]
    {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) :
    Integrable (fun b => kernel n b L) G := by
  apply Integrable.of_bound (continuous_kernel_bid hn hL).aestronglyMeasurable 1
  exact Eventually.of_forall fun b => by
    rw [Real.norm_eq_abs,abs_of_nonneg (kernel_bounds hn hL b).1]
    exact (kernel_bounds hn hL b).2

theorem hasDerivAt_integral_kernel (G : Measure ℝ) [IsFiniteMeasure G]
    {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L)
    (hzero : G {L} = 0) (hone : G {(n:ℝ)*L} = 0) :
    HasDerivAt (fun T => ∫ b, kernel n b T ∂G)
      (-(∫ b, kernelPriceSlope n b L ∂G)) L := by
  have hh : 0 < L/2 := by positivity
  have hs : Ioi (L/2) ∈ 𝓝 L := Ioi_mem_nhds (by linarith)
  have hm : ∀ᶠ T in 𝓝 L, AEStronglyMeasurable (fun b => kernel n b T) G := by
    filter_upwards [eventually_gt_nhds hL] with T hT
    exact (continuous_kernel_bid hn hT).aestronglyMeasurable
  have hlip : ∀ᵐ b ∂G, LipschitzOnWith (Real.nnabs ((n:ℝ)/(L/2)))
      (kernel n b) (Ioi (L/2)) := Eventually.of_forall fun b => by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq,Real.coe_nnabs,abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) hh.le)]
      using kernel_price_difference hn hh hx.le hy.le b
  have hd : ∀ᵐ b ∂G, HasDerivAt (kernel n b) (-kernelPriceSlope n b L) L := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero,
      measure_eq_zero_iff_ae_notMem.mp hone] with b hb0 hb1
    exact hasDerivAt_kernel_price_slope hn hL
      (by simpa only [mem_singleton_iff] using hb0)
      (by simpa only [mem_singleton_iff] using hb1)
  have ht := hasDerivAt_integral_of_dominated_loc_of_lip hs hm
    (integrable_real_kernel G hn hL) (measurable_kernelPriceSlope hn hL).neg.aestronglyMeasurable
    hlip (integrable_const ((n:ℝ)/(L/2))) hd
  simpa only [Pi.neg_apply,integral_neg] using ht.2

theorem exists_integral_kernel_slope_between (G : Measure ℝ) [IsFiniteMeasure G]
    {n : ℕ} (hn : 2 ≤ n) (hatom : ∀ b : ℝ, 0 < b → G {b} = 0)
    {S U : ℝ} (hS : 0 < S) (hU : 0 < U) (hne : S ≠ U) :
    ∃ T, min S U ≤ T ∧ T ≤ max S U ∧
      ((∫ b, kernel n b U ∂G)-(∫ b, kernel n b S ∂G))/(U-S) =
        -(∫ b, kernelPriceSlope n b T ∂G) := by
  have hd (T : ℝ) (hT : 0 < T) := hasDerivAt_integral_kernel G hn hT
    (hatom T hT) (hatom ((n:ℝ)*T) (mul_pos (Nat.cast_pos.mpr (by omega)) hT))
  have aux {a b : ℝ} (ha : 0 < a) (hab : a < b) :
      ∃ T ∈ Ioo a b, -(∫ x, kernelPriceSlope n x T ∂G) =
        ((∫ x, kernel n x b ∂G)-(∫ x, kernel n x a ∂G))/(b-a) := by
    apply exists_hasDerivAt_eq_slope (fun T => ∫ x, kernel n x T ∂G)
      (fun T => -(∫ x, kernelPriceSlope n x T ∂G)) hab
    · intro T hT
      exact (hd T (ha.trans_le hT.1)).continuousAt.continuousWithinAt
    · intro T hT
      exact hd T (ha.trans hT.1)
  rcases lt_or_gt_of_ne hne with hSU | hUS
  · obtain ⟨T,hT,he⟩ := aux hS hSU
    exact ⟨T,by simpa only [min_eq_left hSU.le] using hT.1.le,
      by simpa only [max_eq_right hSU.le] using hT.2.le,he.symm⟩
  · obtain ⟨T,hT,he⟩ := aux hU hUS
    refine ⟨T,by simpa only [min_eq_right hUS.le] using hT.1.le,
      by simpa only [max_eq_left hUS.le] using hT.2.le,?_⟩
    rw [he]
    exact div_eq_div_iff (sub_ne_zero.mpr hne.symm) (sub_ne_zero.mpr hne) |>.mpr (by ring)

theorem tendsto_integral_kernel_increment
    (G : ℕ → Measure ℝ) [∀ t, IsFiniteMeasure (G t)]
    {n : ℕ} (hn : 2 ≤ n) {L A : ℝ} (hL : 0 < L)
    (hatom : ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b → G t {b} = 0)
    (hmean : ∀ T : ℕ → ℝ, Tendsto T atTop (𝓝 L) →
      Tendsto (fun t => ∫ b, kernelPriceSlope n b (T t) ∂G t) atTop (𝓝 A))
    {S U : ℕ → ℝ} (hS : Tendsto S atTop (𝓝 L)) (hU : Tendsto U atTop (𝓝 L))
    (hne : ∀ᶠ t in atTop, S t ≠ U t) :
    Tendsto (fun t => ((∫ b, kernel n b (U t) ∂G t)-(∫ b, kernel n b (S t) ∂G t))/(U t-S t))
      atTop (𝓝 (-A)) := by
  classical
  let P : ℕ → ℝ → Prop := fun t T => min (S t) (U t) ≤ T ∧ T ≤ max (S t) (U t) ∧
    ((∫ b, kernel n b (U t) ∂G t)-(∫ b, kernel n b (S t) ∂G t))/(U t-S t) =
      -(∫ b, kernelPriceSlope n b T ∂G t)
  have hex : ∀ᶠ t in atTop, ∃ T, P t T := by
    filter_upwards [hatom,hS.eventually (eventually_gt_nhds hL),
      hU.eventually (eventually_gt_nhds hL),hne] with t ht hs hu he
    exact exists_integral_kernel_slope_between (G t) hn ht hs hu he
  let T : ℕ → ℝ := fun t => if ht : ∃ T, P t T then Classical.choose ht else S t
  have hT : ∀ᶠ t in atTop, P t (T t) := by
    filter_upwards [hex] with t ht
    simpa only [T,dif_pos ht] using Classical.choose_spec ht
  have hTL : Tendsto T atTop (𝓝 L) := by
    have hlo : Tendsto (fun t => min (S t) (U t)) atTop (𝓝 L) := by
      simpa only [min_self] using hS.min hU
    have hhi : Tendsto (fun t => max (S t) (U t)) atTop (𝓝 L) := by
      simpa only [max_self] using hS.max hU
    exact hlo.squeeze' hhi (hT.mono fun _ ht => ht.1) (hT.mono fun _ ht => ht.2.1)
  apply (hmean T hTL).neg.congr'
  exact hT.mono fun _ ht => ht.2.2.symm

end FCAppendix.PayOnce.KernelDemand
