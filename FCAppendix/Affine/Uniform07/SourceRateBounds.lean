import FCAppendix.Affine.Uniform07.ParameterCertificate
import FCAppendix.Affine.Uniform07.RateDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace FCAppendix.Affine.Uniform07
open MeasureTheory Set

noncomputable def purePhysicalSlope (i : Row) (z : ℝ) : ℝ :=
  (pureParameter i z-rho)/(pureParameter i z*(1-pureParameter i z))

theorem cutoff_small (i : Row) : cutoff i<1/800 := by
  apply Box.upper_real (cutoffBox_ok i)
  cases i <;> norm_num [cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,
    LogCertificate.box,Box.div,Box.inv,Box.point,Box.mul,Box.scale,Box.sub,Box.add,Box.neg,xiQ,etaQ,xQ]

theorem pure_parameter_range (i : Row) {z : ℝ} (hz : z∈Icc (1/2) (x i)) :
    pureParameter i z∈Ioc rho (1/2) := by
  have ht := cutoff_pos i
  have hsmall := cutoff_small i
  have hx : x i≤3/4 := by cases i <;> norm_num [x,xQ]
  have hz' : z≤3/4 := hz.2.trans hx
  have hlow := mul_le_mul_of_nonneg_right hz' ht.le
  have hhigh := mul_le_mul_of_nonneg_right hz.1 ht.le
  unfold pureParameter rho
  constructor <;> nlinarith

theorem pure_physical_slope_bounds (i : Row) {z : ℝ} (hz : z∈Icc (1/2) (x i)) :
    0<purePhysicalSlope i z ∧ purePhysicalSlope i z≤1/500 := by
  have hp := pure_parameter_range i hz
  have hP : 0<pureParameter i z := by norm_num [rho] at hp; linarith [hp.1]
  have hP1 : 0<1-pureParameter i z := by linarith [hp.2]
  have hden := mul_pos hP hP1
  constructor
  · exact div_pos (sub_pos.mpr hp.1) hden
  · unfold purePhysicalSlope
    apply (div_le_iff₀ hden).2
    have hprod := mul_nonpos_of_nonpos_of_nonneg
      (show pureParameter i z-1/2≤0 by linarith [hp.2])
      (show 0≤pureParameter i z/500+999/1000 by positivity)
    dsimp [rho]
    nlinarith

theorem pure_rate_derivative (i : Row) {z : ℝ} (hz : z∈Icc (1/2) (x i)) :
    HasDerivAt (pureRate i) (-cutoff i*purePhysicalSlope i z) z := by
  have hp := pure_parameter_range i hz
  have hP : 0<pureParameter i z := by norm_num [rho] at hp; linarith [hp.1]
  have hP1 : 0<1-pureParameter i z := by linarith [hp.2]
  have hr : 0<rho := by norm_num [rho]
  have hr1 : 0<1-rho := by norm_num [rho]
  have hD : HasDerivAt (pureParameter i) (-cutoff i) z := by
    convert (hasDerivAt_const z ((1+cutoff i)/2)).sub
      ((hasDerivAt_id z).mul_const (cutoff i)) using 1 <;>
      first | rfl | ext a b | simp
  have h1 := (((hasDerivAt_const z rho).div hD hP.ne').log (div_pos hr hP).ne').const_mul rho
  have h2 := (((hasDerivAt_const z (1-rho)).div
    ((hasDerivAt_const z (1:ℝ)).sub hD) hP1.ne').log (div_pos hr1 hP1).ne').const_mul (1-rho)
  have hs := h1.add h2
  change HasDerivAt (pureRate i) _ z at hs
  apply hs.congr_deriv
  dsimp
  unfold purePhysicalSlope
  field_simp
  ring

theorem laplace_lower_prefix (i : Row) {z theta : ℝ} (hz : z∈Icc (1/2) (x i)) :
    cutoff i*z≤laplace i theta z := by
  have ht := cutoff_pos i
  have ht1 := cutoff_lt_one i
  have hx : x i≤1 := by cases i <;> norm_num [x,xQ]
  have h1 : 0≤pieceZ (1/xi i) (z/xi i) theta z (x i) :=
    intervalIntegral.integral_nonneg hz.2 (fun _ _ => (Real.exp_pos _).le)
  have h2 : 0≤pieceZ ((1-z*kappa i/x i)/xi i) z theta (x i) 1 :=
    intervalIntegral.integral_nonneg hx (fun _ _ => (Real.exp_pos _).le)
  have he : 0≤(1-cutoff i)*Real.exp (-theta/2) := by positivity
  have hh := mul_nonneg ht.le (add_nonneg h1 h2)
  unfold laplace
  nlinarith

theorem laplace_pos (i : Row) {z theta : ℝ} (hz : z∈Icc (1/2) (x i)) :
    0<laplace i theta z :=
  (mul_pos (cutoff_pos i) (by linarith [hz.1])).trans_le (laplace_lower_prefix i hz)

theorem canonical_rate_bddAbove (i : Row) {z : ℝ} (hz : z∈Icc (1/2) (x i)) :
    BddAbove ((fun theta => objective i theta z) '' Ici 0) := by
  refine ⟨-Real.log (cutoff i*z),?_⟩
  rintro y ⟨theta,htheta,rfl⟩
  have htz : 0<cutoff i*z := mul_pos (cutoff_pos i) (by linarith [hz.1])
  have hlog := Real.log_le_log htz (laplace_lower_prefix i (theta := theta) hz)
  have hn : 0≤theta*rho := mul_nonneg htheta (by norm_num [rho])
  unfold objective
  linarith

theorem test_below_canonical_rate (i : Row) {z theta : ℝ}
    (hz : z∈Icc (1/2) (x i)) (htheta : 0≤theta) :
    objective i theta z≤canonicalRate i z :=
  le_csSup (canonical_rate_bddAbove i hz) ⟨theta,htheta,rfl⟩

end FCAppendix.Affine.Uniform07
