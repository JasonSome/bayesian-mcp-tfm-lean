import FCAppendix.PayOnce.GaussianStrictVariance

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryGaussian
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.PayOnce.GaussianResponse
local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

def inverseMills (x : ℝ) : ℝ := φ x / Φ x

lemma inverseMills_pos (x : ℝ) : 0 < inverseMills x :=
  div_pos (gaussianPDFReal_pos 0 1 x (by norm_num))
    (FCAppendix.CorrelatedLoads.gaussian_cdf_pos x)

lemma x_add_inverseMills_pos (x : ℝ) : 0 < x+inverseMills x := by
  have hp := FCAppendix.CorrelatedLoads.gaussian_cdf_pos x
  have ht := successPrimitive_pos x
  rw [FCAppendix.Bayes.gaussianSuccessPrimitive] at ht
  have he : x+inverseMills x = (x*Φ x+φ x)/Φ x := by
    unfold inverseMills
    field_simp [hp.ne']
  rw [he]
  exact div_pos ht hp

lemma hasDerivAt_inverseMills (x : ℝ) :
    HasDerivAt inverseMills (-(inverseMills x)*(x+inverseMills x)) x := by
  have hp := FCAppendix.CorrelatedLoads.gaussian_cdf_pos x
  have hh := (FCAppendix.Bayes.hasDerivAt_standardGaussianPDF x).div
    (hasDerivAt_normalCDF x) hp.ne'
  apply hh.congr_deriv
  unfold inverseMills
  field_simp [hp.ne']
  ring

lemma inverseMills_strictAnti : StrictAnti inverseMills := by
  apply strictAnti_of_hasDerivAt_neg hasDerivAt_inverseMills
  intro x
  have h := mul_pos (inverseMills_pos x) (x_add_inverseMills_pos x)
  nlinarith

lemma hasDerivAt_log_normalCDF (x : ℝ) :
    HasDerivAt (fun y => Real.log (Φ y)) (inverseMills x) x :=
  (hasDerivAt_normalCDF x).log
    (FCAppendix.CorrelatedLoads.gaussian_cdf_pos x).ne'

theorem concaveOn_log_normalCDF :
    ConcaveOn ℝ Set.univ (fun x : ℝ => Real.log (Φ x)) := by
  have hanti : AntitoneOn (deriv (fun x : ℝ => Real.log (Φ x)))
      (interior (Set.univ : Set ℝ)) := by
    intro x _ y _ hxy
    rw [(hasDerivAt_log_normalCDF x).deriv,(hasDerivAt_log_normalCDF y).deriv]
    exact inverseMills_strictAnti.antitone hxy
  exact hanti.concaveOn_of_deriv (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    ((continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_log_normalCDF x).continuousAt).continuousOn)
    (fun x _ => (hasDerivAt_log_normalCDF x).differentiableAt.differentiableWithinAt)

def foldedKernel (omega c x : ℝ) : ℝ :=
  2/omega * φ (x/omega) * Φ (c*x)

lemma foldedKernel_pos {omega c : ℝ} (homega : 0 < omega) (x : ℝ) :
    0 < foldedKernel omega c x := by
  unfold foldedKernel
  exact mul_pos (mul_pos (by positivity)
    (gaussianPDFReal_pos 0 1 (x/omega) (by norm_num)))
    (FCAppendix.CorrelatedLoads.gaussian_cdf_pos (c*x))

lemma log_foldedKernel {omega c : ℝ} (homega : 0 < omega) (x : ℝ) :
    Real.log (foldedKernel omega c x) =
      Real.log (2/omega) + Real.log (φ (x/omega)) + Real.log (Φ (c*x)) := by
  have hp : 0 < φ (x/omega) := gaussianPDFReal_pos 0 1 (x/omega) (by norm_num)
  have hF : 0 < Φ (c*x) := FCAppendix.CorrelatedLoads.gaussian_cdf_pos _
  unfold foldedKernel
  rw [Real.log_mul (mul_ne_zero (by positivity) hp.ne') hF.ne',
    Real.log_mul (by positivity) hp.ne']

lemma hasDerivAt_log_foldedKernel {omega c : ℝ} (homega : 0 < omega) (x : ℝ) :
    HasDerivAt (fun y => Real.log (foldedKernel omega c y))
      (-x/omega^2 + c*inverseMills (c*x)) x := by
  have hp : 0 < φ (x/omega) := gaussianPDFReal_pos 0 1 (x/omega) (by norm_num)
  have hPDF0 : HasDerivAt (fun y => φ (y/omega))
      (-(x/omega)*φ (x/omega)*(1/omega)) x := by
    convert! (FCAppendix.Bayes.hasDerivAt_standardGaussianPDF (x/omega)).comp x
      ((hasDerivAt_id x).div_const omega) using 1
  have hPDF := hPDF0.log hp.ne'
  have hCDF := (hasDerivAt_log_normalCDF (c*x)).comp x
    ((hasDerivAt_id x).const_mul c)
  have hconst := hasDerivAt_const x (Real.log (2/omega))
  have hh := (hconst.add hPDF).add hCDF
  have he : (fun y => Real.log (foldedKernel omega c y)) =
      (fun y => Real.log (2/omega)+Real.log (φ (y/omega))+Real.log (Φ (c*y))) :=
    funext (log_foldedKernel homega)
  rw [he]
  apply hh.congr_deriv
  field_simp [homega.ne',hp.ne']
  ring

theorem concaveOn_log_foldedKernel {omega c : ℝ}
    (homega : 0 < omega) (hc : 0 ≤ c) :
    ConcaveOn ℝ Set.univ (fun x => Real.log (foldedKernel omega c x)) := by
  have hanti : AntitoneOn (deriv (fun x => Real.log (foldedKernel omega c x)))
      (interior (Set.univ : Set ℝ)) := by
    intro x _ y _ hxy
    rw [(hasDerivAt_log_foldedKernel homega x).deriv,
      (hasDerivAt_log_foldedKernel homega y).deriv]
    have hlinear : -y/omega^2 ≤ -x/omega^2 :=
      div_le_div_of_nonneg_right (neg_le_neg hxy) (sq_nonneg omega)
    have hratio := inverseMills_strictAnti.antitone (mul_le_mul_of_nonneg_left hxy hc)
    exact add_le_add hlinear (mul_le_mul_of_nonneg_left hratio hc)
  exact hanti.concaveOn_of_deriv (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    ((continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_log_foldedKernel homega x).continuousAt).continuousOn)
    (fun x _ => (hasDerivAt_log_foldedKernel homega x).differentiableAt.differentiableWithinAt)

end FCAppendix.Affine.Uniform06.EntryGaussian
