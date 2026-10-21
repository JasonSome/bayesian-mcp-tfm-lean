import FCAppendix.Affine.Uniform07.RateMonotonicity
import Mathlib.Topology.Order.Compact

noncomputable section
namespace FCAppendix.Affine.Uniform07
open MeasureTheory ProbabilityTheory Set

abbrev SourceZ (i : Row) := Icc (1/2:ℝ) (sourceZhi i)
abbrev SourceTheta := Icc (1/50:ℝ) (7/5)

private theorem sourceZ_mem (i : Row) (z : SourceZ i) : (z:ℝ)∈Icc (1/2) (x i) :=
  ⟨z.2.1,z.2.2.trans (by cases i <;> norm_num [sourceZhi,x,xQ])⟩

private theorem laplace_uniform (i : Row) {z : ℝ}
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

private theorem acceptance_continuous (i : Row) {y : ℝ} (hy : y∈Icc (0:ℝ) 1) :
    Continuous (fun q : SourceZ i × SourceTheta => normalizedAcceptance i q.1 y) := by
  by_cases hy0 : y=0
  · subst y
    have he : (fun q : SourceZ i × SourceTheta => normalizedAcceptance i q.1 0)=fun _ => 0 := by
      funext q
      have hq : (0:ℝ)≤q.1 := by linarith [q.1.2.1]
      simp [normalizedAcceptance,hq]
    rw [he]
    exact continuous_const
  · have he : (fun q : SourceZ i × SourceTheta => normalizedAcceptance i q.1 y)=
        fun q => max 0 ((1-(q.1:ℝ)/normalizedBid i y)/xi i) := by
      funext q
      exact normalizedAcceptance_eq_source i (sourceZ_mem i q.1)
        ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0),hy.2⟩
    rw [he]
    fun_prop

private theorem laplace_joint_continuous (i : Row) :
    Continuous (fun q : SourceZ i × SourceTheta => laplace i q.2 q.1) := by
  have hI : Continuous (fun q : SourceZ i × SourceTheta =>
      ∫ y, Real.exp (-(q.2:ℝ)*normalizedAcceptance i q.1 y) ∂uniformLaw) := by
    apply continuous_of_dominated (bound:=fun _ => (1:ℝ))
    · intro q
      exact ((measurable_normalizedAcceptance i q.1).const_mul (-(q.2:ℝ))).exp.aestronglyMeasurable
    · intro q
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc] with y hy
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [q.2.2.1])
        (normalizedAcceptance_bounds i (sourceZ_mem i q.1) hy).1
    · exact integrable_const 1
    · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc] with y hy
      have htheta : Continuous (fun q : SourceZ i × SourceTheta => -(q.2:ℝ)) := by fun_prop
      exact Real.continuous_exp.comp (htheta.mul (acceptance_continuous i hy))
  have hsum : Continuous (fun q : SourceZ i × SourceTheta =>
      (1-cutoff i)*Real.exp (-(q.2:ℝ)/2)+cutoff i*
        ∫ y, Real.exp (-(q.2:ℝ)*normalizedAcceptance i q.1 y) ∂uniformLaw) := by
    have htheta : Continuous (fun q : SourceZ i × SourceTheta => -(q.2:ℝ)/2) := by fun_prop
    exact (continuous_const.mul (Real.continuous_exp.comp htheta)).add (continuous_const.mul hI)
  exact hsum.congr (fun q => (laplace_uniform i (sourceZ_mem i q.1) q.2).symm)

private theorem objective_joint_continuous (i : Row) :
    Continuous (fun q : SourceZ i × SourceTheta => objective i q.2 q.1) := by
  unfold objective
  exact (((continuous_subtype_val.comp continuous_snd).neg).mul continuous_const).sub
    ((laplace_joint_continuous i).log (fun q => (laplace_pos i (sourceZ_mem i q.1)).ne'))

theorem continuous_source_rate (i : Row) :
    ContinuousOn (canonicalRate i) (Icc (1/2) (sourceZhi i)) := by
  letI : CompactSpace SourceTheta := isCompact_iff_compactSpace.mp isCompact_Icc
  have hc : Continuous (fun z : SourceZ i =>
      sSup ((fun theta : SourceTheta => objective i theta z) '' (univ:Set SourceTheta))) :=
    (isCompact_univ : IsCompact (univ:Set SourceTheta)).continuous_sSup
      (objective_joint_continuous i)
  rw [continuousOn_iff_continuous_restrict]
  apply hc.congr
  intro z
  obtain ⟨theta,htheta,hroot,hrate,_hstrict,_hunique⟩ :=
    exists_unique_source_tilt_on_crossover i z.2
  change sSup ((fun theta : SourceTheta => objective i theta z) '' (univ:Set SourceTheta)) =
    canonicalRate i (z:ℝ)
  rw [hrate]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨objective i (1/50) z,⟨1/50,by norm_num⟩,mem_univ _,rfl⟩
    · rintro _ ⟨s,_hs,rfl⟩
      exact source_tilt_global_max i (sourceZ_mem i z) hroot s
  · apply le_csSup
    · refine ⟨objective i theta z,?_⟩
      rintro _ ⟨s,_hs,rfl⟩
      exact source_tilt_global_max i (sourceZ_mem i z) hroot s
    · exact ⟨⟨theta,htheta.1.le,htheta.2.le⟩,mem_univ _,rfl⟩
end FCAppendix.Affine.Uniform07
