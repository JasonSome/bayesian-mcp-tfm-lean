import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryHazard
open MeasureTheory Set Filter Topology

theorem reverse_hazard_antitone (f F k : ℝ → ℝ)
    (hf : ∀ x, 0 < f x) (hF : ∀ x, 0 < F x)
    (hdf : ∀ x, HasDerivAt f (k x*f x) x)
    (hdF : ∀ x, HasDerivAt F (f x) x)
    (hfi : Integrable f) (hdfi : Integrable (fun x => k x*f x))
    (hfbot : Tendsto f atBot (𝓝 0)) (hFbot : Tendsto F atBot (𝓝 0))
    (hk : Antitone k) : Antitone (fun x => f x/F x) := by
  have hbound (x : ℝ) : k x*F x ≤ f x := by
    have hI : (∫ y in Iic x, f y) = F x := by
      have he := integral_Iic_of_hasDerivAt_of_tendsto'
        (fun y (_ : y ∈ Iic x) => hdF y) hfi.integrableOn hFbot
      simpa only [sub_zero] using he
    have hD : (∫ y in Iic x, k y*f y) = f x := by
      have he := integral_Iic_of_hasDerivAt_of_tendsto'
        (fun y (_ : y ∈ Iic x) => hdf y) hdfi.integrableOn hfbot
      simpa only [sub_zero] using he
    have hm := integral_mono_ae (hfi.const_mul (k x)).integrableOn hdfi.integrableOn
      (show ∀ᵐ y ∂volume.restrict (Iic x), k x*f y ≤ k y*f y from by
        filter_upwards [self_mem_ae_restrict measurableSet_Iic] with y hy
        exact mul_le_mul_of_nonneg_right (hk hy) (hf y).le)
    rw [integral_const_mul,hI,hD] at hm
    exact hm
  apply antitone_of_deriv_nonpos
    (fun x => ((hdf x).div (hdF x) (hF x).ne').differentiableAt)
  intro x
  rw [((hdf x).div (hdF x) (hF x).ne').deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (hbound x) (hf x).le
  nlinarith [hh]

theorem finite_increment_subadditive (L g : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt L (g x) x) (hg : Antitone g)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    L (x+y)-L x ≤ L y-L 0 := by
  let q : ℝ → ℝ := fun t => L (x+t)-L t
  have hq (t : ℝ) : HasDerivAt q (g (x+t)-g t) t := by
    have hinner : HasDerivAt (fun s : ℝ => x+s) 1 t := by
      simpa using (hasDerivAt_id t).const_add x
    exact ((hd (x+t)).comp t hinner).sub (hd t) |>.congr_deriv (by ring)
  have ha : Antitone q := by
    apply antitone_of_deriv_nonpos (fun t => (hq t).differentiableAt)
    intro t
    rw [(hq t).deriv]
    exact sub_nonpos.mpr (hg (by linarith : t ≤ x+t))
  have he := ha hy
  dsimp only [q] at he
  simp only [add_zero] at he
  linarith

theorem conditional_shortfall_survival_submul (f F : ℝ → ℝ)
    (hF : ∀ x, 0 < F x) (hdF : ∀ x, HasDerivAt F (f x) x)
    (hhazard : Antitone (fun x => f x/F x)) (z : ℝ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    F (z-(x+y))/F z ≤ (F (z-x)/F z)*(F (z-y)/F z) := by
  let L : ℝ → ℝ := fun t => Real.log (F (z-t))-Real.log (F z)
  let g : ℝ → ℝ := fun t => -(f (z-t)/F (z-t))
  have hd (t : ℝ) : HasDerivAt L (g t) t := by
    have hinner : HasDerivAt (fun s : ℝ => z-s) (-1) t := by
      convert! (hasDerivAt_id t).const_sub z using 1
    have hh := (((hdF (z-t)).log (hF (z-t)).ne').comp t hinner).sub_const (Real.log (F z))
    exact hh.congr_deriv (by dsimp [g]; ring)
  have hg : Antitone g := by
    intro s t hst
    dsimp [g]
    exact neg_le_neg (hhazard (by linarith : z-t ≤ z-s))
  have hh := finite_increment_subadditive L g hd hg hx hy
  have hL0 : L 0=0 := by simp [L]
  rw [hL0] at hh
  have hex := Real.exp_le_exp.mpr (show L (x+y) ≤ L x+L y by linarith)
  have he (t : ℝ) : Real.exp (L t)=F (z-t)/F z := by
    dsimp [L]
    rw [Real.exp_sub,Real.exp_log (hF _),Real.exp_log (hF _)]
  rw [Real.exp_add,he,he,he] at hex
  exact hex

lemma integral_shift_Ici (S : ℝ → ℝ) (x : ℝ) :
    (∫ y in Ici (0 : ℝ), S (x+y)) = ∫ y in Ici x, S y := by
  rw [← integral_indicator measurableSet_Ici,← integral_indicator measurableSet_Ici]
  have he : (fun y => (Ici (0 : ℝ)).indicator (fun y => S (x+y)) y) =
      (fun y => (Ici x).indicator S (x+y)) := by
    funext y
    by_cases hy : 0 ≤ y
    · have hxy : x ≤ x+y := by linarith
      simp [hy,hxy]
    · have hxy : ¬x ≤ x+y := by linarith
      simp [hy,hxy]
  rw [he]
  exact integral_add_left_eq_self ((Ici x).indicator S) x

private def triangle (S : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (Icc (0 : ℝ) y).indicator (fun _ => S y) x

private lemma triangle_integral (S : ℝ → ℝ) (y : ℝ) :
    (∫ x, triangle S x y) = max y 0*S y := by
  simp only [triangle]
  rw [integral_indicator_const _ measurableSet_Icc,smul_eq_mul]
  simp only [Measure.real,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal']

theorem survival_weighted_integral_le_square (S : ℝ → ℝ)
    (hSm : Measurable S) (hS0 : ∀ x, 0 ≤ x → 0 ≤ S x)
    (hSi : IntegrableOn S (Ici (0 : ℝ)))
    (hSxi : Integrable (fun x => max x 0*S x))
    (hsub : ∀ x y, 0 ≤ x → 0 ≤ y → S (x+y) ≤ S x*S y) :
    (∫ x in Ici (0 : ℝ), x*S x) ≤ (∫ x in Ici (0 : ℝ), S x)^2 := by
  have hTm : Measurable (Function.uncurry (triangle S)) := by
    simp only [Function.uncurry_def,triangle,Set.indicator_apply,Set.mem_Icc]
    apply Measurable.ite
      ((measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_snd))
      (hSm.comp measurable_snd) measurable_const
  have hTnon (x y : ℝ) : 0 ≤ triangle S x y := by
    by_cases h : x ∈ Icc (0 : ℝ) y
    · rw [triangle,indicator_of_mem h]
      exact hS0 y (h.1.trans h.2)
    · simp [triangle,h]
  have hTslice (y : ℝ) : Integrable (fun x => triangle S x y) := by
    exact (integrable_indicator_iff measurableSet_Icc).2 (integrable_const (S y))
  have hTnorm (y : ℝ) : (∫ x, ‖triangle S x y‖) = max y 0*S y := by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hTnon _ _)]
    exact triangle_integral S y
  have hTi : Integrable (Function.uncurry (triangle S)) (volume.prod volume) := by
    apply (integrable_prod_iff' hTm.aestronglyMeasurable).2
    refine ⟨Eventually.of_forall hTslice,?_⟩
    simpa only [Function.uncurry_def,hTnorm] using hSxi
  have houter : (∫ x, ∫ y, triangle S x y) = ∫ y, max y 0*S y := by
    rw [integral_integral_swap hTi]
    simp_rw [triangle_integral]
  have hweighted : (∫ y, max y 0*S y) = ∫ y in Ici (0 : ℝ), y*S y := by
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : 0 ≤ y
    · simp [hy]
    · simp [hy,max_eq_right (le_of_not_ge hy)]
  have hinner (x : ℝ) : (∫ y, triangle S x y) =
      (Ici (0 : ℝ)).indicator (fun x => ∫ y in Ici x, S y) x := by
    by_cases hx : 0 ≤ x
    · rw [indicator_of_mem (show x ∈ Ici (0:ℝ) from hx),← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hxy : x ≤ y <;> simp [triangle,hx,hxy]
    · simp [triangle,hx]
  have hbound (x : ℝ) : (∫ y, triangle S x y) ≤
      (Ici (0 : ℝ)).indicator (fun x => S x*(∫ y in Ici (0:ℝ), S y)) x := by
    rw [hinner]
    by_cases hx : 0 ≤ x
    · simp only [indicator_of_mem (show x ∈ Ici (0:ℝ) from hx)]
      rw [← integral_shift_Ici]
      have hleft : IntegrableOn (fun y => S (x+y)) (Ici (0:ℝ)) := by
        apply Integrable.mono' (hSi.const_mul (S x))
          (hSm.comp (measurable_const.add measurable_id)).aestronglyMeasurable.restrict
        filter_upwards [self_mem_ae_restrict measurableSet_Ici] with y hy
        simp only [Function.comp_apply,Pi.add_apply,id_eq]
        rw [Real.norm_eq_abs,abs_of_nonneg (hS0 (x+y) (add_nonneg hx hy))]
        exact hsub x y hx hy
      have hi := integral_mono_ae hleft (hSi.const_mul (S x))
        (show ∀ᵐ y ∂volume.restrict (Ici (0:ℝ)), S (x+y) ≤ S x*S y from by
          filter_upwards [self_mem_ae_restrict measurableSet_Ici] with y hy
          exact hsub x y hx hy)
      simpa only [integral_const_mul] using hi
    · simp [hx]
  have hright : Integrable ((Ici (0:ℝ)).indicator
      (fun x => S x*(∫ y in Ici (0:ℝ), S y))) := by
    exact (integrable_indicator_iff measurableSet_Ici).2
      (hSi.mul_const (∫ y in Ici (0:ℝ), S y))
  have hleft : Integrable (fun x => ∫ y, triangle S x y) := by
    simpa only [Function.uncurry_def] using hTi.integral_prod_left
  have hi := integral_mono hleft hright hbound
  rw [houter,hweighted,integral_indicator measurableSet_Ici,integral_mul_const] at hi
  simpa only [pow_two] using hi

theorem survival_second_moment_le_two_mean_sq (S : ℝ → ℝ)
    (hSm : Measurable S) (hS0 : ∀ x, 0 ≤ x → 0 ≤ S x)
    (hSi : IntegrableOn S (Ici (0 : ℝ)))
    (hSxi : Integrable (fun x => max x 0*S x))
    (hsub : ∀ x y, 0 ≤ x → 0 ≤ y → S (x+y) ≤ S x*S y) :
    2*(∫ x in Ici (0 : ℝ), x*S x) ≤ 2*(∫ x in Ici (0 : ℝ), S x)^2 :=
  mul_le_mul_of_nonneg_left (survival_weighted_integral_le_square S hSm hS0 hSi hSxi hsub)
    (by norm_num)

end FCAppendix.Affine.Uniform06.EntryHazard
