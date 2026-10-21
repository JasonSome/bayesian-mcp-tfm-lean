import FCAppendix.Affine.Uniform07.EndpointCertificate
import FCAppendix.Affine.Uniform07.TiltFamily

namespace FCAppendix.Affine.Uniform07
open MeasureTheory ProbabilityTheory Set

theorem source_acceptance_antitone (i : Row) {z₁ z₂ y : ℝ}
    (h₁ : z₁∈Icc (1/2) (x i)) (h₂ : z₂∈Icc (1/2) (x i)) (hz : z₁≤z₂)
    (hy : y∈Ioc 0 1) : normalizedAcceptance i z₂ y≤normalizedAcceptance i z₁ y := by
  have hx : 0<x i := by cases i <;> norm_num [x,xQ]
  have hk : 0<kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hB : 0<normalizedBid i y := by
    unfold normalizedBid
    split_ifs
    · exact hy.1
    · exact div_pos (mul_pos hx hy.1)
        (add_pos (mul_pos hk hy.1) (mul_pos (xi_pos i) hx))
  rw [normalizedAcceptance_eq_source i h₁ hy,normalizedAcceptance_eq_source i h₂ hy]
  exact max_le_max le_rfl (div_le_div_of_nonneg_right
    (sub_le_sub_left (div_le_div_of_nonneg_right hz hB.le) 1) (xi_pos i).le)

theorem source_laplace_uniform_integral (i : Row) {z : ℝ}
    (hz : z∈Icc (1/2) (x i)) (theta : ℝ) :
    laplace i theta z=(1-cutoff i)*Real.exp (-theta/2)+cutoff i*
      ∫ y, Real.exp (-theta*normalizedAcceptance i z y) ∂uniformLaw := by
  have hf : Continuous (fun u : ℝ => Real.exp (-theta*u)) := by fun_prop
  rw [←sourceLaw_mgf i hz theta]
  unfold mgf
  have h := sourceLaw_integral i hz hf
  rw [←lowerSourceLaw_integral i z hf,lowerSourceLaw,
    integral_map (measurable_normalizedAcceptance i z).aemeasurable
      hf.measurable.aestronglyMeasurable] at h
  convert h using 1
  ring

theorem source_laplace_monotone (i : Row) {z₁ z₂ theta : ℝ}
    (h₁ : z₁∈Icc (1/2) (x i)) (h₂ : z₂∈Icc (1/2) (x i))
    (hz : z₁≤z₂) (htheta : 0≤theta) : laplace i theta z₁≤laplace i theta z₂ := by
  rw [source_laplace_uniform_integral i h₁ theta,source_laplace_uniform_integral i h₂ theta]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (cutoff_pos i).le
  have hf : Continuous (fun u : ℝ => Real.exp (-theta*u)) := by fun_prop
  have hi (z : ℝ) (hz : z∈Icc (1/2) (x i)) :
      Integrable (fun y => Real.exp (-theta*normalizedAcceptance i z y)) uniformLaw :=
    (lowerSourceLaw_integrable i hz hf).comp_aemeasurable
      (measurable_normalizedAcceptance i z).aemeasurable
  apply integral_mono_ae (hi z₁ h₁) (hi z₂ h₂)
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc] with y hy
  apply Real.exp_le_exp.mpr
  by_cases hy0 : y=0
  · subst y
    have hz₁ : 0≤z₁ := by linarith [h₁.1]
    have hz₂ : 0≤z₂ := by linarith [h₂.1]
    simp [normalizedAcceptance,hz₁,hz₂]
  · exact mul_le_mul_of_nonpos_left
      (source_acceptance_antitone i h₁ h₂ hz ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0),hy.2⟩)
      (neg_nonpos.mpr htheta)

theorem source_rate_antitone (i : Row) : AntitoneOn (canonicalRate i) (Icc (1/2) (x i)) := by
  intro z₁ h₁ z₂ h₂ hz
  apply csSup_le
  · exact ⟨objective i 0 z₂,0,by simp,rfl⟩
  · rintro _ ⟨theta,htheta,rfl⟩
    have hlog := Real.log_le_log (laplace_pos i h₁)
      (source_laplace_monotone i h₁ h₂ hz htheta)
    have hobj : objective i theta z₂≤objective i theta z₁ := by
      unfold objective
      linarith
    exact hobj.trans (test_below_canonical_rate i h₁ htheta)

theorem source_pure_rate_antitone (i : Row) : AntitoneOn (pureRate i) (Icc (1/2) (x i)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro z hz
    exact (pure_rate_derivative i hz).continuousAt.continuousWithinAt
  · intro z hz
    exact (pure_rate_derivative i (interior_subset hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [(pure_rate_derivative i (interior_subset hz)).deriv]
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg (cutoff_pos i).le
      (pure_physical_slope_bounds i (interior_subset hz)).1.le)

theorem no_source_crossover_above_zhi (i : Row) {z : ℝ}
    (hz : z∈Icc (sourceZhi i) (x i)) : canonicalRate i z<pureRate i z := by
  have hihi : sourceZhi i≤x i := by cases i <;> norm_num [sourceZhi,x,xQ]
  have hi : sourceZhi i∈Icc (1/2) (x i) :=
    ⟨by cases i <;> norm_num [sourceZhi],hihi⟩
  have hx : x i∈Icc (1/2) (x i) :=
    ⟨by cases i <;> norm_num [x,xQ],le_rfl⟩
  have hz' : z∈Icc (1/2) (x i) := ⟨hi.1.trans hz.1,hz.2⟩
  have he : canonicalRate i (sourceZhi i)<pureRate i (x i) := by
    cases i
    · exact canonical_upper_endpoint_gap.1
    · exact canonical_upper_endpoint_gap.2
  exact (source_rate_antitone i hi hz' hz.1).trans_lt
    (he.trans_le (source_pure_rate_antitone i hz' hx hz.2))
end FCAppendix.Affine.Uniform07
