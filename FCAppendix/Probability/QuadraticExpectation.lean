import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace FCAppendix.Probability
open MeasureTheory Set Filter Topology Real

theorem quadratic_remainder_of_derivative_lipschitz
    {f f' : ℝ → ℝ} {ℓ u K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x ∈ Icc ℓ u, HasDerivAt f (f' x) x)
    (hlip : ∀ x ∈ Icc ℓ u, ∀ y ∈ Icc ℓ u, |f' x-f' y| ≤ K*|x-y|)
    {p q : ℝ} (hp : p ∈ Icc ℓ u) (hq : q ∈ Icc ℓ u) :
    |f p-f q-f' q*(p-q)| ≤ K*(p-q)^2 := by
  let s := Icc (min p q) (max p q)
  have hsub : s ⊆ Icc ℓ u := fun _ hz =>
    ⟨(le_min hp.1 hq.1).trans hz.1,hz.2.trans (max_le hp.2 hq.2)⟩
  have hp' : p ∈ s := ⟨min_le_left _ _,le_max_left _ _⟩
  have hq' : q ∈ s := ⟨min_le_right _ _,le_max_right _ _⟩
  have hd (z : ℝ) (hz : z ∈ s) : |z-q| ≤ |p-q| := by
    rcases le_total p q with hpq | hqp
    · have hz' : z ∈ Icc p q := by simpa only [s,min_eq_left hpq,max_eq_right hpq] using hz
      rw [abs_of_nonpos (sub_nonpos.mpr hz'.2),abs_of_nonpos (sub_nonpos.mpr hpq)]
      linarith [hz'.1]
    · have hz' : z ∈ Icc q p := by simpa only [s,min_eq_right hqp,max_eq_left hqp] using hz
      rw [abs_of_nonneg (sub_nonneg.mpr hz'.1),abs_of_nonneg (sub_nonneg.mpr hqp)]
      linarith [hz'.2]
  let g := fun z => f z-f q-f' q*(z-q)
  have hg (z : ℝ) (hz : z ∈ s) : HasDerivWithinAt g (f' z-f' q) s z := by
    have hh := ((hf z (hsub hz)).sub_const (f q)).sub
      (((hasDerivAt_id z).sub_const q).const_mul (f' q))
    simpa only [g,mul_one,Pi.sub_def,id_eq] using hh.hasDerivWithinAt
  have hb (z : ℝ) (hz : z ∈ s) : ‖f' z-f' q‖ ≤ K*|p-q| := by
    rw [Real.norm_eq_abs]
    exact (hlip z (hsub hz) q hq).trans (mul_le_mul_of_nonneg_left (hd z hz) hK)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hb
    (convex_Icc (min p q) (max p q)) hq' hp'
  have he : |p-q| *|p-q| = (p-q)^2 := by rw [← sq_abs]; ring
  simpa only [g,sub_self,mul_zero,sub_zero,Real.norm_eq_abs,mul_assoc,he] using hh

theorem exists_unit_quadratic_taylor {f : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0:ℝ) 1, ContDiffAt ℝ 2 f x) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      (∀ p ∈ Icc (0:ℝ) 1, |deriv f p| ≤ A) ∧
      ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
        |f p-f q-deriv f q*(p-q)| ≤ K*(p-q)^2 := by
  have hs : ContDiffOn ℝ 1 (deriv f) (Icc (0:ℝ) 1) := fun x hx =>
    ((hf x hx).derivWithin (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).contDiffWithinAt
  obtain ⟨K,hK⟩ := hs.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 1) isCompact_Icc
  let K' : ℝ := (K:ℝ)+1
  have hK' : 0 < K' := by dsimp [K']; positivity
  have hlip (p : ℝ) (hp : p ∈ Icc (0:ℝ) 1) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1) :
      |deriv f p-deriv f q| ≤ K'*|p-q| := by
    have hh := hK.dist_le_mul p hp q hq
    rw [Real.dist_eq,Real.dist_eq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [K']; linarith) (abs_nonneg _))
  refine ⟨|deriv f 0|+K'+1,K',by positivity,hK',?_,?_⟩
  · intro p hp
    have hh := hlip p hp 0 (by norm_num)
    simp only [sub_zero,abs_of_nonneg hp.1] at hh
    have htri := abs_sub_le (deriv f p) (deriv f 0) 0
    simp only [sub_zero] at htri
    have hmul := mul_le_of_le_one_right hK'.le hp.2
    linarith
  · intro p hp q hq
    exact quadratic_remainder_of_derivative_lipschitz hK'.le
      (fun x hx => ((hf x hx).differentiableAt (by norm_num)).hasDerivAt) hlip hp hq

theorem integral_quadratic_error_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (f : ℝ → ℝ)
    {a d K : ℝ} (hX : Integrable X μ) (hX2 : Integrable (fun z => (X z-a)^2) μ)
    (hF : Integrable (fun z => f (X z)) μ)
    (herror : ∀ z, |f (X z)-f a-d*(X z-a)| ≤ K*(X z-a)^2) :
    |(∫ z, f (X z) ∂μ)-f a| ≤
      |d| *|(∫ z, X z-a ∂μ)|+K*(∫ z, (X z-a)^2 ∂μ) := by
  have hΔ : Integrable (fun z => X z-a) μ := hX.sub (integrable_const a)
  let R := fun z => f (X z)-f a-d*(X z-a)
  have hF0 : Integrable (fun z => f (X z)-f a) μ := hF.sub (integrable_const (f a))
  have hR : Integrable R μ := hF0.sub (hΔ.const_mul d)
  have he : (∫ z, R z ∂μ) = (∫ z, f (X z) ∂μ)-f a-d*(∫ z, X z-a ∂μ) := by
    dsimp only [R]
    rw [integral_sub hF0 (hΔ.const_mul d),
      integral_sub hF (integrable_const (f a)),integral_const_mul]
    simp
  have hb := (abs_integral_le_integral_abs (f := R)).trans
    (integral_mono hR.abs (hX2.const_mul K) herror)
  rw [he,integral_const_mul] at hb
  have hh := abs_sub_le ((∫ z, f (X z) ∂μ)-f a) (d*(∫ z, X z-a ∂μ)) 0
  simp only [sub_zero] at hh
  rw [abs_mul] at hh
  linarith

theorem tendsto_normalized_error_of_quadratic_bound
    {A K : ℝ} {δ m v e : ℕ → ℝ}
    (hδ : ∀ᶠ t in atTop, 0 < δ t)
    (hm : Tendsto (fun t => m t/δ t) atTop (𝓝 0))
    (hv : Tendsto (fun t => v t/δ t) atTop (𝓝 0))
    (he : ∀ᶠ t in atTop, |e t| ≤ A*|m t|+K*v t) :
    Tendsto (fun t => e t/δ t) atTop (𝓝 0) := by
  have hright : Tendsto (fun t => A*|m t/δ t|+K*(v t/δ t)) atTop (𝓝 0) := by
    simpa only [abs_zero,mul_zero,add_zero] using (hm.abs.const_mul A).add (hv.const_mul K)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun t => norm_nonneg _) ?_ hright
  filter_upwards [hδ,he] with t hδt het
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hδt]
  have hh := div_le_div_of_nonneg_right het hδt.le
  simpa only [add_div,mul_div_assoc,abs_div,abs_of_pos hδt] using hh

theorem tendsto_div_scale_of_quadratic_bound {δ v : ℕ → ℝ} {K : ℝ}
    (hδ : ∀ᶠ t in atTop, 0 < δ t) (hδlim : Tendsto δ atTop (𝓝 0))
    (hv : ∀ᶠ t in atTop, 0 ≤ v t ∧ v t ≤ K*(δ t)^2) :
    Tendsto (fun t => v t/δ t) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hδlim.const_mul K)
  · filter_upwards [hδ,hv] with t hδt hvt
    exact div_nonneg hvt.1 hδt.le
  · filter_upwards [hδ,hv] with t hδt hvt
    apply (div_le_iff₀ hδt).mpr
    nlinarith [hvt.2]

end FCAppendix.Probability
