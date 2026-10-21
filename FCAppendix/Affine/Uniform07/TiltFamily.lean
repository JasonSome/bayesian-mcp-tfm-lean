import FCAppendix.Affine.Uniform07.TiltUniqueness
import FCAppendix.Affine.Uniform07.SourceAcceptance

namespace FCAppendix.Affine.Uniform07
open MeasureTheory ProbabilityTheory Set

private theorem normalizedBid_pos (i : Row) {y : ℝ} (hy : 0<y) :
    0<normalizedBid i y := by
  have hx : 0<x i := by cases i <;> norm_num [x,xQ]
  have hk : 0<kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  unfold normalizedBid
  split_ifs
  · exact hy
  · exact div_pos (mul_pos hx hy) (add_pos (mul_pos hk hy) (mul_pos (xi_pos i) hx))

private theorem normalizedAcceptance_antitone (i : Row) {z₁ z₂ y : ℝ}
    (h₁ : z₁∈Icc (1/2) (x i)) (h₂ : z₂∈Icc (1/2) (x i)) (hz : z₁≤z₂)
    (hy : y∈Ioc 0 1) : normalizedAcceptance i z₂ y≤normalizedAcceptance i z₁ y := by
  rw [normalizedAcceptance_eq_source i h₁ hy,normalizedAcceptance_eq_source i h₂ hy]
  exact max_le_max le_rfl (div_le_div_of_nonneg_right
    (sub_le_sub_left (div_le_div_of_nonneg_right hz (normalizedBid_pos i hy.1).le) 1)
    (xi_pos i).le)

private theorem tiltIntegrand_derivative (theta y : ℝ) :
    HasDerivAt (fun u : ℝ => (u-rho)*Real.exp (-theta*u))
      (Real.exp (-theta*y)*(1-theta*(y-rho))) y := by
  have h₁ := (hasDerivAt_id y).sub_const rho
  have h₂ := (Real.hasDerivAt_exp (-theta*y)).comp y
    ((hasDerivAt_id y).const_mul (-theta))
  convert h₁.mul h₂ using 1 <;> first | rfl | ext a b | (simp only [Function.comp_apply,id_eq]; ring)

private theorem tiltIntegrand_monotone {theta : ℝ} (htheta : theta∈Icc (0:ℝ) (7/5)) :
    MonotoneOn (fun u : ℝ => (u-rho)*Real.exp (-theta*u)) (Icc (0:ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (by fun_prop) (by fun_prop)
  intro y hy
  rw [(tiltIntegrand_derivative theta y).deriv]
  apply mul_nonneg (Real.exp_pos _).le
  have hy' := interior_subset hy
  have hh := mul_nonneg htheta.1 (sub_nonneg.mpr hy'.2)
  dsimp [rho]
  nlinarith [htheta.1,htheta.2]

private theorem source_score_uniform_integral (i : Row) {z : ℝ}
    (hz : z∈Icc (1/2) (x i)) (theta : ℝ) :
    tiltScore i theta z=(1-cutoff i)*(1/2-rho)*Real.exp (-theta/2)+cutoff i*
      ∫ y, (normalizedAcceptance i z y-rho)*Real.exp (-theta*normalizedAcceptance i z y)
        ∂uniformLaw := by
  have hf : Continuous (fun u : ℝ => (u-rho)*Real.exp (-theta*u)) := by fun_prop
  rw [←sourceLaw_score i hz theta]
  have h := sourceLaw_integral i hz hf
  rw [←lowerSourceLaw_integral i z hf,lowerSourceLaw,
    integral_map (measurable_normalizedAcceptance i z).aemeasurable
      hf.measurable.aestronglyMeasurable] at h
  convert h using 1
  ring

theorem source_score_antitone (i : Row) {z₁ z₂ theta : ℝ}
    (h₁ : z₁∈Icc (1/2) (x i)) (h₂ : z₂∈Icc (1/2) (x i))
    (hz : z₁≤z₂) (htheta : theta∈Icc (0:ℝ) (7/5)) :
    tiltScore i theta z₂≤tiltScore i theta z₁ := by
  rw [source_score_uniform_integral i h₁ theta,source_score_uniform_integral i h₂ theta]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (cutoff_pos i).le
  have hf : Continuous (fun u : ℝ => (u-rho)*Real.exp (-theta*u)) := by fun_prop
  have hi (z : ℝ) (hz : z∈Icc (1/2) (x i)) :
      Integrable (fun y => (normalizedAcceptance i z y-rho)*
        Real.exp (-theta*normalizedAcceptance i z y)) uniformLaw :=
    (lowerSourceLaw_integrable i hz hf).comp_aemeasurable
      (measurable_normalizedAcceptance i z).aemeasurable
  apply integral_mono_ae (hi z₂ h₂) (hi z₁ h₁)
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc] with y hy
  by_cases hy0 : y=0
  · subst y
    have hz₁ : 0≤z₁ := by linarith [h₁.1]
    have hz₂ : 0≤z₂ := by linarith [h₂.1]
    simp [normalizedAcceptance,hz₁,hz₂]
  · exact tiltIntegrand_monotone htheta
      (normalizedAcceptance_bounds i h₂ hy) (normalizedAcceptance_bounds i h₁ hy)
      (normalizedAcceptance_antitone i h₁ h₂ hz ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0),hy.2⟩)

noncomputable def sourceZhi : Row → ℝ | .first => 371/500 | .second => 347/500

theorem exists_unique_source_tilt_on_crossover (i : Row) {z : ℝ}
    (hz : z∈Icc (1/2) (sourceZhi i)) :
    ∃ theta∈Ioo (1/50:ℝ) (7/5), tiltScore i theta z=0 ∧
      canonicalRate i z=objective i theta z ∧
      (∀ s : ℝ, s≠theta → objective i s z<objective i theta z) ∧
      (∀ s : ℝ, tiltScore i s z=0 → s=theta) := by
  have hihi : sourceZhi i≤x i := by cases i <;> norm_num [sourceZhi,x,xQ]
  have hzhi : sourceZhi i∈Icc (1/2) (x i) :=
    ⟨by cases i <;> norm_num [sourceZhi],hihi⟩
  have hzx : z∈Icc (1/2) (x i) := ⟨hz.1,hz.2.trans hihi⟩
  have hleft : 0<tiltScore i (1/50) z := by
    have hm := source_score_antitone i hzx hzhi hz.2 (by norm_num : (1/50:ℝ)∈Icc 0 (7/5))
    have hh : 0<tiltScore i (1/50) (sourceZhi i) := by
      cases i
      · exact (by norm_num : (0:ℝ)<13661/10^10).trans first_tilt_low
      · exact (by norm_num : (0:ℝ)<19361/10^10).trans second_tilt_low
    exact hh.trans_le hm
  have hright : tiltScore i (7/5) z<0 := by
    have hhalf : (1/2:ℝ)∈Icc (1/2) (x i) := ⟨le_rfl,by cases i <;> norm_num [x,xQ]⟩
    have hm := source_score_antitone i hhalf hzx hz.1 (by norm_num : (7/5:ℝ)∈Icc 0 (7/5))
    have hh : tiltScore i (7/5) (1/2)<0 := by
      cases i
      · exact first_tilt_high.trans (by norm_num)
      · exact second_tilt_high.trans (by norm_num)
    exact hm.trans_lt hh
  obtain ⟨theta,htheta,hroot⟩ := exists_source_tilt i hzx (by norm_num) hleft hright
  refine ⟨theta,htheta,hroot,source_tilt_rate i hzx (by linarith [htheta.1]) hroot,?_,?_⟩
  · intro s hs
    exact source_tilt_strict_global_max i hzx hroot hs
  · intro s hs
    exact source_tilt_unique i hzx hs hroot
end FCAppendix.Affine.Uniform07
