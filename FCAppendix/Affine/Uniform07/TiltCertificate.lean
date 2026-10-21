import FCAppendix.Affine.Uniform07.TiltSigns
import FCAppendix.Affine.Uniform07.SourceLaw
import FCAppendix.Affine.Uniform07.TiltOptimizerBound

namespace FCAppendix.Affine.Uniform07
open MeasureTheory ProbabilityTheory Set

theorem source_tilt_mean (i : Row) {z theta : ℝ} (hz : z ∈ Icc (1/2) (x i))
    (hroot : tiltScore i theta z=0) :
    (∫ y : ℝ, y ∂(sourceLaw i z).tilted (fun y => -theta*y))=rho := by
  have hp := mgf_pos (sourceLaw_exp_integrable i hz (-theta))
  have hm := sourceLaw_score_moment i hz theta
  rw [hroot] at hm
  have he : (∫ y, y*Real.exp (-theta*y) ∂sourceLaw i z)=
      rho*mgf (fun y : ℝ => y) (sourceLaw i z) (-theta) := by linarith
  calc
    _ = ∫ y, (y*Real.exp (-theta*y))/
        mgf (fun y : ℝ => y) (sourceLaw i z) (-theta) ∂sourceLaw i z := by
      rw [integral_tilted_mul_eq_mgf]
      congr 1
      funext y
      simp only [smul_eq_mul]
      ring
    _ = (∫ y, y*Real.exp (-theta*y) ∂sourceLaw i z)/
        mgf (fun y : ℝ => y) (sourceLaw i z) (-theta) := integral_div _ _
    _ = rho := by rw [he]; exact mul_div_cancel_right₀ _ hp.ne'

theorem source_objective_eq_cgf (i : Row) {z : ℝ} (hz : z ∈ Icc (1/2) (x i))
    (theta : ℝ) :
    objective i theta z = -theta*rho-cgf (fun y : ℝ => y) (sourceLaw i z) (-theta) := by
  rw [cgf,sourceLaw_mgf i hz theta]
  rfl

theorem source_tilt_global_max (i : Row) {z theta : ℝ} (hz : z ∈ Icc (1/2) (x i))
    (hroot : tiltScore i theta z=0) (s : ℝ) : objective i s z ≤ objective i theta z := by
  rw [source_objective_eq_cgf i hz s,source_objective_eq_cgf i hz theta]
  exact root_tilt_global_max (sourceLaw i z) (fun y : ℝ => y)
    measurable_id.aemeasurable (sourceLaw_bounds i hz) (source_tilt_mean i hz hroot) s

theorem source_tilt_rate (i : Row) {z theta : ℝ} (hz : z ∈ Icc (1/2) (x i))
    (htheta : 0 ≤ theta) (hroot : tiltScore i theta z=0) :
    canonicalRate i z=objective i theta z := by
  have hupper : BddAbove ((fun s => objective i s z) '' Ici 0) := by
    refine ⟨objective i theta z,?_⟩
    rintro _ ⟨s,_hs,rfl⟩
    exact source_tilt_global_max i hz hroot s
  apply le_antisymm
  · apply csSup_le
    · exact ⟨objective i 0 z,0,by simp,rfl⟩
    · rintro _ ⟨s,_hs,rfl⟩
      exact source_tilt_global_max i hz hroot s
  · exact le_csSup hupper ⟨theta,htheta,rfl⟩

theorem source_tilt_allowance (i : Row) {z theta lo hi : ℝ}
    (hz : z ∈ Icc (1/2) (x i)) (hlo : lo ≤ theta) (hhi : theta ≤ hi)
    (hroot : tiltScore i theta z=0) :
    objective i theta z ≤ objective i ((lo+hi)/2) z+((hi-lo)/2)^2/8 := by
  rw [source_objective_eq_cgf i hz theta,source_objective_eq_cgf i hz ((lo+hi)/2)]
  exact tilt_bracket_allowance (sourceLaw i z) (fun y : ℝ => y)
    measurable_id.aemeasurable (sourceLaw_bounds i hz) hlo hhi (source_tilt_mean i hz hroot)

theorem exists_source_tilt (i : Row) {z lo hi : ℝ}
    (hz : z ∈ Icc (1/2) (x i)) (hlohi : lo ≤ hi)
    (hleft : 0 < tiltScore i lo z) (hright : tiltScore i hi z < 0) :
    ∃ theta ∈ Ioo lo hi, tiltScore i theta z=0 := by
  obtain ⟨theta,htheta,hroot⟩ := intermediate_value_Icc' hlohi
    (continuous_tiltScore i hz).continuousOn ⟨hright.le,hleft.le⟩
  refine ⟨theta,⟨?_,?_⟩,hroot⟩
  · by_contra hn
    have he : theta=lo := le_antisymm (le_of_not_gt hn) htheta.1
    rw [he] at hroot
    linarith
  · by_contra hn
    have he : theta=hi := le_antisymm htheta.2 (le_of_not_gt hn)
    rw [he] at hroot
    linarith

theorem first_optimized_bracket :
    ∃ theta ∈ Ioo (323/12500:ℝ) (517/20000),
      tiltScore .first theta (371/500)=0 ∧
      canonicalRate .first (371/500)=objective .first theta (371/500) ∧
      canonicalRate .first (371/500) ≤
        objective .first (5169/200000) (371/500)+3125/10^15 := by
  have hz : (371/500:ℝ) ∈ Icc (1/2) (x .first) := by norm_num [x,xQ]
  obtain ⟨theta,htheta,hroot⟩ := exists_source_tilt .first hz (by norm_num)
    first_bracket_low first_bracket_high
  have hrate := source_tilt_rate .first hz (by linarith [htheta.1]) hroot
  have hbound := source_tilt_allowance .first hz htheta.1.le htheta.2.le hroot
  norm_num at hbound
  exact ⟨theta,htheta,hroot,hrate,by rw [hrate]; linarith [hbound]⟩

theorem second_optimized_bracket :
    ∃ theta ∈ Ioo (1421/50000:ℝ) (711/25000),
      tiltScore .second theta (347/500)=0 ∧
      canonicalRate .second (347/500)=objective .second theta (347/500) ∧
      canonicalRate .second (347/500) ≤
        objective .second (2843/100000) (347/500)+125/10^13 := by
  have hz : (347/500:ℝ) ∈ Icc (1/2) (x .second) := by norm_num [x,xQ]
  obtain ⟨theta,htheta,hroot⟩ := exists_source_tilt .second hz (by norm_num)
    second_bracket_low second_bracket_high
  have hrate := source_tilt_rate .second hz (by linarith [htheta.1]) hroot
  have hbound := source_tilt_allowance .second hz htheta.1.le htheta.2.le hroot
  norm_num at hbound
  exact ⟨theta,htheta,hroot,hrate,by rw [hrate]; linarith [hbound]⟩

end FCAppendix.Affine.Uniform07
