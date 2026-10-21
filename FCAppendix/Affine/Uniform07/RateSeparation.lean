import FCAppendix.Affine.Uniform07.RateCrossover

noncomputable section
namespace FCAppendix.Affine.Uniform07
open MeasureTheory ProbabilityTheory Set

private theorem exp_gap {theta u₁ u₂ : ℝ}
    (htheta : theta∈Icc (0:ℝ) (7/5)) (hu₁ : u₁∈Icc (0:ℝ) 1)
    (_hu₂ : u₂∈Icc (0:ℝ) 1) (hu : u₂≤u₁) :
    theta*Real.exp (-(7/5:ℝ))*(u₁-u₂) ≤ Real.exp (-theta*u₂)-Real.exp (-theta*u₁) := by
  have hd : 0≤theta*(u₁-u₂) := mul_nonneg htheta.1 (sub_nonneg.mpr hu)
  have he : Real.exp (-(7/5:ℝ))≤Real.exp (-theta*u₁) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_nonneg htheta.1 (sub_nonneg.mpr hu₁.2)
    nlinarith [htheta.2]
  have ht := Real.add_one_le_exp (theta*(u₁-u₂))
  calc
    _ = Real.exp (-(7/5:ℝ))*(theta*(u₁-u₂)) := by ring
    _ ≤ Real.exp (-theta*u₁)*(theta*(u₁-u₂)) := mul_le_mul_of_nonneg_right he hd
    _ ≤ Real.exp (-theta*u₁)*(Real.exp (theta*(u₁-u₂))-1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_sub,mul_one,←Real.exp_add]
      congr 1
      ring

private def highSlope (i : Row) : ℝ := kappa i/(xi i*x i)+1

private theorem highSlope_pos (i : Row) : 0<highSlope i := by
  cases i <;> norm_num [highSlope,kappa,kappaQ,xi,xiQ,x,xQ,etaQ]

private theorem high_acceptance_gap (i : Row) {z₁ z₂ y : ℝ}
    (h₁ : z₁∈Icc (1/2) (x i)) (h₂ : z₂∈Icc (1/2) (x i))
    (hz : z₁≤z₂) (hy : y∈Ioc (x i) 1) :
    highSlope i*(z₂-z₁) ≤ normalizedAcceptance i z₁ y-normalizedAcceptance i z₂ y := by
  have hx : 0<x i := by cases i <;> norm_num [x,xQ]
  have hyp : 0<y := hx.trans hy.1
  have hxi := xi_pos i
  have hzi₁ : ¬y≤z₁ := not_le.mpr (h₁.2.trans_lt hy.1)
  have hzi₂ : ¬y≤z₂ := not_le.mpr (h₂.2.trans_lt hy.1)
  have hxy : ¬y≤x i := not_le.mpr hy.1
  have hid : normalizedAcceptance i z₁ y-normalizedAcceptance i z₂ y=
      (z₂-z₁)*(kappa i/(xi i*x i)+1/y) := by
    simp only [normalizedAcceptance,if_neg hzi₁,if_neg hzi₂,if_neg hxy,pieceP]
    field_simp
    ring
  have hy1 : 1≤1/y := (le_div_iff₀ hyp).2 (by simpa using hy.2)
  rw [hid]
  have hh := mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hy1)
  dsimp [highSlope]
  nlinarith

private theorem high_interval_mass (i : Row) : uniformLaw.real (Ioc (x i) 1)=1-x i := by
  have hx : (x i)∈Icc (0:ℝ) 1 := by cases i <;> norm_num [x,xQ]
  unfold uniformLaw
  rw [measureReal_restrict_apply measurableSet_Ioc]
  have he : Ioc (x i) 1∩Icc (0:ℝ) 1=Ioc (x i) 1 :=
    inter_eq_left.mpr (fun _ hy => ⟨hx.1.trans hy.1.le,hy.2⟩)
  rw [he,Real.volume_real_Ioc_of_le hx.2]

private theorem laplace_increment_lower (i : Row) {z₁ z₂ theta : ℝ}
    (h₁ : z₁∈Icc (1/2) (x i)) (h₂ : z₂∈Icc (1/2) (x i))
    (hz : z₁≤z₂) (htheta : theta∈Icc (0:ℝ) (7/5)) :
    cutoff i*theta*Real.exp (-(7/5:ℝ))*(1-x i)*highSlope i*(z₂-z₁) ≤
      laplace i theta z₂-laplace i theta z₁ := by
  let E := fun z y : ℝ => Real.exp (-theta*normalizedAcceptance i z y)
  let K := theta*Real.exp (-(7/5:ℝ))*highSlope i*(z₂-z₁)
  have hf : Continuous (fun u : ℝ => Real.exp (-theta*u)) := by fun_prop
  have hi (z : ℝ) (hz : z∈Icc (1/2) (x i)) : Integrable (E z) uniformLaw :=
    (lowerSourceLaw_integrable i hz hf).comp_aemeasurable
      (measurable_normalizedAcceptance i z).aemeasurable
  have hpoint : (Ioc (x i) 1).indicator (fun _ : ℝ => K) ≤ᵐ[uniformLaw]
      fun y => E z₂ y-E z₁ y := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc] with y hy
    have hp : normalizedAcceptance i z₂ y≤normalizedAcceptance i z₁ y := by
      by_cases hy0 : y=0
      · subst y
        have hz₁ : 0≤z₁ := by linarith [h₁.1]
        have hz₂ : 0≤z₂ := by linarith [h₂.1]
        simp [normalizedAcceptance,hz₁,hz₂]
      · exact source_acceptance_antitone i h₁ h₂ hz
          ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0),hy.2⟩
    by_cases hh : y∈Ioc (x i) 1
    · rw [indicator_of_mem hh]
      have hgap := exp_gap htheta (normalizedAcceptance_bounds i h₁ hy)
        (normalizedAcceptance_bounds i h₂ hy) hp
      have hhigh := mul_le_mul_of_nonneg_left (high_acceptance_gap i h₁ h₂ hz hh)
        (mul_nonneg htheta.1 (Real.exp_pos (-(7/5:ℝ))).le)
      change K ≤ _
      calc
        K = (theta*Real.exp (-(7/5:ℝ)))*(highSlope i*(z₂-z₁)) := by dsimp [K]; ring
        _ ≤ _ := hhigh.trans hgap
    · rw [indicator_of_notMem hh]
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr htheta.1)))
  have hint := integral_mono_ae ((integrable_const K).indicator measurableSet_Ioc)
    ((hi z₂ h₂).sub (hi z₁ h₁)) hpoint
  rw [integral_indicator measurableSet_Ioc,integral_const,
    measureReal_restrict_apply MeasurableSet.univ,univ_inter,high_interval_mass i,smul_eq_mul] at hint
  change (1-x i)*K ≤ ∫ y, E z₂ y-E z₁ y ∂uniformLaw at hint
  rw [integral_sub (hi z₂ h₂) (hi z₁ h₁)] at hint
  rw [source_laplace_uniform_integral i h₁ theta,source_laplace_uniform_integral i h₂ theta]
  have hmul := mul_le_mul_of_nonneg_left hint (cutoff_pos i).le
  dsimp [E,K] at hmul
  nlinarith

private theorem laplace_le_one (i : Row) {z theta : ℝ}
    (hz : z∈Icc (1/2) (x i)) (htheta : 0≤theta) : laplace i theta z≤1 := by
  rw [←sourceLaw_mgf i hz theta]
  have h := integral_mono_ae (sourceLaw_exp_integrable i hz (-theta)) (integrable_const (1:ℝ))
    ((sourceLaw_bounds i hz).mono (fun y hy => by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta) hy.1))
  simpa only [mgf,integral_const,probReal_univ,smul_eq_mul,one_mul] using h

private theorem log_increment_lower {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b≤1) :
    b-a≤Real.log b-Real.log a := by
  have hbp := ha.trans_le hab
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hbp ha)
  rw [Real.log_div hbp.ne' ha.ne',inv_div] at hl
  have he : 1-a/b=(b-a)/b := by field_simp
  rw [he] at hl
  have hq : b-a≤(b-a)/b := (le_div_iff₀ hbp).2 (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hb)])
  exact hq.trans hl

private theorem source_lower_slope_identity (i : Row) :
    (1/50:ℝ)*Real.exp (-(7/5:ℝ))*(1-x i)*highSlope i=slopeRatioLower i/500 := by
  cases i <;> norm_num [highSlope,slopeRatioLower,x,xQ,xi,xiQ,kappa,kappaQ,etaQ] <;> ring

theorem source_canonical_increment_lower (i : Row) {z₁ z₂ : ℝ}
    (h₁ : z₁∈Icc (1/2) (sourceZhi i)) (h₂ : z₂∈Icc (1/2) (sourceZhi i))
    (hz : z₁≤z₂) :
    cutoff i*(slopeRatioLower i/500)*(z₂-z₁) ≤ canonicalRate i z₁-canonicalRate i z₂ := by
  have hi : sourceZhi i≤x i := by cases i <;> norm_num [sourceZhi,x,xQ]
  have hz₁ : z₁∈Icc (1/2) (x i) := ⟨h₁.1,h₁.2.trans hi⟩
  have hz₂ : z₂∈Icc (1/2) (x i) := ⟨h₂.1,h₂.2.trans hi⟩
  obtain ⟨theta,htheta,hroot,hrate,_hstrict,_hunique⟩ := exists_unique_source_tilt_on_crossover i h₂
  have ht0 : 0≤theta := by linarith [htheta.1]
  have hg := laplace_increment_lower i hz₁ hz₂ hz ⟨ht0,htheta.2.le⟩
  have hl := log_increment_lower (laplace_pos i hz₁)
    (source_laplace_monotone i hz₁ hz₂ hz ht0) (laplace_le_one i hz₂ ht0)
  have htheta' : cutoff i*(1/50)*Real.exp (-(7/5:ℝ))*(1-x i)*highSlope i*(z₂-z₁) ≤
      cutoff i*theta*Real.exp (-(7/5:ℝ))*(1-x i)*highSlope i*(z₂-z₁) := by
    have hx : 0≤1-x i := by cases i <;> norm_num [x,xQ]
    have hp : 0≤cutoff i*Real.exp (-(7/5:ℝ))*(1-x i)*highSlope i*(z₂-z₁) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (cutoff_pos i).le
        (Real.exp_pos _).le) hx) (highSlope_pos i).le) (sub_nonneg.mpr hz)
    have hm := mul_le_mul_of_nonneg_left htheta.1.le hp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hm
  have hh := htheta'.trans (hg.trans hl)
  have hb := test_below_canonical_rate i hz₁ ht0
  rw [hrate]
  unfold objective at hb ⊢
  rw [←source_lower_slope_identity i]
  nlinarith

theorem source_pure_increment_upper (i : Row) {z₁ z₂ : ℝ}
    (h₁ : z₁∈Icc (1/2) (x i)) (h₂ : z₂∈Icc (1/2) (x i)) (hz : z₁≤z₂) :
    pureRate i z₁-pureRate i z₂≤cutoff i/500*(z₂-z₁) := by
  have hc : ContinuousOn (pureRate i) (Icc (1/2) (x i)) := fun z hz =>
    (pure_rate_derivative i hz).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (pureRate i) (interior (Icc (1/2) (x i))) := fun z hz =>
    (pure_rate_derivative i (interior_subset hz)).differentiableAt.differentiableWithinAt
  have hb : ∀ z∈interior (Icc (1/2) (x i)), -cutoff i/500≤deriv (pureRate i) z := by
    intro z hz
    rw [(pure_rate_derivative i (interior_subset hz)).deriv]
    have hh := mul_le_mul_of_nonneg_left (pure_physical_slope_bounds i (interior_subset hz)).2
      (cutoff_pos i).le
    linarith
  have hh := (convex_Icc (1/2:ℝ) (x i)).mul_sub_le_image_sub_of_le_deriv hc hd hb z₁ h₁ z₂ h₂ hz
  linarith

theorem source_rate_difference_strictAnti (i : Row) :
    StrictAntiOn (fun z => canonicalRate i z-pureRate i z) (Icc (1/2) (sourceZhi i)) := by
  intro z₁ h₁ z₂ h₂ hz
  have hi : sourceZhi i≤x i := by cases i <;> norm_num [sourceZhi,x,xQ]
  have hc := source_canonical_increment_lower i h₁ h₂ hz.le
  have hp := source_pure_increment_upper i ⟨h₁.1,h₁.2.trans hi⟩ ⟨h₂.1,h₂.2.trans hi⟩ hz.le
  have hratio : 1<slopeRatioLower i := by
    cases i
    · linarith [physical_slope_numerics.1]
    · linarith [physical_slope_numerics.2]
  have hstrict : 0<cutoff i*(slopeRatioLower i/500-1/500)*(z₂-z₁) :=
    mul_pos (mul_pos (cutoff_pos i) (by linarith)) (sub_pos.mpr hz)
  have hcomp : cutoff i/500*(z₂-z₁)<cutoff i*(slopeRatioLower i/500)*(z₂-z₁) := by
    nlinarith
  linarith

theorem exists_unique_source_rate_crossover (i : Row) :
    ∃ z∈Ioo (sourceZlo i) (sourceZhi i), canonicalRate i z=pureRate i z ∧
      ∀ u∈Icc (1/2) (x i), canonicalRate i u=pureRate i u → u=z := by
  obtain ⟨z,hz,hroot⟩ := exists_source_rate_crossover i
  have hlo : (1/2:ℝ)<sourceZlo i := by cases i <;> norm_num [sourceZlo]
  have hzi : z∈Icc (1/2) (sourceZhi i) := ⟨(hlo.trans hz.1).le,hz.2.le⟩
  refine ⟨z,hz,hroot,?_⟩
  intro u hu huroot
  by_cases hui : u≤sourceZhi i
  · have hui' : u∈Icc (1/2) (sourceZhi i) := ⟨hu.1,hui⟩
    rcases lt_trichotomy u z with hlt|heq|hgt
    · have hh := source_rate_difference_strictAnti i hui' hzi hlt
      dsimp only at hh
      rw [hroot,huroot] at hh
      linarith
    · exact heq
    · have hh := source_rate_difference_strictAnti i hzi hui' hgt
      dsimp only at hh
      rw [hroot,huroot] at hh
      linarith
  · have hh := no_source_crossover_above_zhi i ⟨(lt_of_not_ge hui).le,hu.2⟩
    rw [huroot] at hh
    exact (lt_irrefl _ hh).elim
end FCAppendix.Affine.Uniform07
