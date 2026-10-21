import FCAppendix.Affine.Uniform07.TiltCertificate

namespace FCAppendix.Affine.Uniform07
open MeasureTheory ProbabilityTheory Set

private theorem centered_cgf_pos (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hb : ∀ᵐ y ∂nu, y ∈ Icc (0:ℝ) 1) {r s : ℝ}
    (hmean : (∫ y, y ∂nu)=r) (hn : ¬∀ᵐ y ∂nu, y=r) (hs : s≠0) :
    0 < cgf (fun y => y-r) nu s := by
  have hiX : Integrable (fun y : ℝ => y) nu :=
    Integrable.of_mem_Icc 0 1 measurable_id.aemeasurable hb
  have hiY : Integrable (fun y : ℝ => y-r) nu := hiX.sub (integrable_const r)
  have hY : ∀ᵐ y ∂nu, y-r ∈ Icc (-r) (1-r) := by
    filter_upwards [hb] with y hy
    constructor <;> linarith [hy.1,hy.2]
  have hiE : Integrable (fun y : ℝ => Real.exp (s*(y-r))) nu :=
    integrable_exp_mul_of_mem_Icc (measurable_id.aemeasurable.sub_const r) hY
  have hiL : Integrable (fun y : ℝ => (1:ℝ)+s*(y-r)) nu :=
    (integrable_const 1).add (hiY.const_mul s)
  let f := fun y : ℝ => Real.exp (s*(y-r))-(1+s*(y-r))
  have hf : Integrable f nu := hiE.sub hiL
  have hf0 : 0 ≤ f := fun y => sub_nonneg.mpr (by
    simpa only [add_comm] using Real.add_one_le_exp (s*(y-r)))
  have hsub : {y : ℝ | y≠r} ⊆ Function.support f := by
    intro y hy
    change f y≠0
    have he := Real.add_one_lt_exp (mul_ne_zero hs (sub_ne_zero.mpr hy))
    dsimp [f]
    linarith
  have hn' : nu {y : ℝ | y≠r} ≠0 := by
    simpa only [ae_iff] using hn
  have hp : 0 < ∫ y, f y ∂nu :=
    (integral_pos_iff_support_of_nonneg hf0 hf).2
      ((pos_iff_ne_zero.mpr hn').trans_le (measure_mono hsub))
  have hmean0 : (∫ y, y-r ∂nu)=0 := by
    rw [integral_sub hiX (integrable_const r),hmean]
    simp
  have hone : (∫ y : ℝ, (1:ℝ)+s*(y-r) ∂nu)=1 := by
    rw [integral_add (integrable_const 1) (hiY.const_mul s),integral_const_mul,hmean0]
    simp
  rw [show (∫ y, f y ∂nu)=(∫ y, Real.exp (s*(y-r)) ∂nu)-1 by
    change (∫ y, Real.exp (s*(y-r))-(1+s*(y-r)) ∂nu) = _
    rw [integral_sub hiE hiL,hone]] at hp
  exact Real.log_pos (by linarith : 1 < ∫ y, Real.exp (s*(y-r)) ∂nu)

private theorem sourceLaw_not_constant (i : Row) (z : ℝ) :
    ¬∀ᵐ y ∂sourceLaw i z, y=rho := by
  intro h
  rw [sourceLaw,ae_add_measure_iff] at h
  have hc : ENNReal.ofReal (1-cutoff i)≠0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (cutoff_lt_one i)))
  have hd : ∀ᵐ y ∂Measure.dirac (1/2:ℝ), y=rho := by
    simpa [ae_iff,Measure.smul_apply,smul_eq_mul,hc] using h.1
  have he := (ae_dirac_iff (by measurability)).mp hd
  norm_num [rho] at he

theorem source_tilt_strict_global_max (i : Row) {z theta s : ℝ}
    (hz : z ∈ Icc (1/2) (x i)) (hroot : tiltScore i theta z=0)
    (hne : s≠theta) : objective i s z < objective i theta z := by
  let mu := sourceLaw i z
  let nu := mu.tilted (fun y : ℝ => -theta*y)
  have hint : Integrable (fun y : ℝ => Real.exp (-theta*y)) mu :=
    sourceLaw_exp_integrable i hz (-theta)
  letI : IsProbabilityMeasure nu := isProbabilityMeasure_tilted hint
  have hac := tilted_absolutelyContinuous mu (fun y : ℝ => -theta*y)
  have hback := absolutelyContinuous_tilted hint
  have hn : ¬∀ᵐ y ∂nu, y=rho := by
    intro h
    exact sourceLaw_not_constant i z (hback.ae_le h)
  have hp := centered_cgf_pos nu (hac.ae_le (sourceLaw_bounds i hz))
    (source_tilt_mean i hz hroot) hn (sub_ne_zero.mpr (Ne.symm hne))
  rw [← objective_difference_as_cgf mu (fun y : ℝ => y) measurable_id.aemeasurable
    (sourceLaw_bounds i hz) theta s rho] at hp
  rw [source_objective_eq_cgf i hz s,source_objective_eq_cgf i hz theta]
  linarith

theorem source_tilt_unique (i : Row) {z theta s : ℝ}
    (hz : z ∈ Icc (1/2) (x i))
    (htheta : tiltScore i theta z=0) (hs : tiltScore i s z=0) : theta=s := by
  by_contra hne
  have hstrict := source_tilt_strict_global_max i hz htheta (Ne.symm hne)
  have hweak := source_tilt_global_max i hz hs theta
  linarith
end FCAppendix.Affine.Uniform07
