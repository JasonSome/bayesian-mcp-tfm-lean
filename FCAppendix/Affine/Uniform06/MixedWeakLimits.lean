import FCAppendix.Affine.Uniform06.MixedLaw
import FCAppendix.Affine.Uniform06.FiniteGuards
import FCAppendix.PayOnce.KernelLawConvergence
import FCAppendix.Probability.BoundedLawConvergence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.MixedWeakLimits

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07
open FCAppendix.ExponentialTilt

def unitClip : C(ℝ,Icc (0:ℝ) 1) :=
  ⟨fun x => ⟨FiniteGuards.clip01 x,FiniteGuards.clip01_bounds x⟩,
    FiniteGuards.continuous_clip01.subtype_mk _⟩

def unitTest (u : ℝ) (F : ℝ → ℝ) (hF : Continuous F) :
    BoundedContinuousFunction ℝ ℝ :=
  (BoundedContinuousFunction.mkOfCompact
    (⟨fun x : Icc (0:ℝ) 1 => Real.exp (u*x)*F x,by fun_prop⟩ :
      C(Icc (0:ℝ) 1,ℝ))).compContinuous unitClip

theorem unitTest_eq (u : ℝ) (F : ℝ → ℝ) (hF : Continuous F)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    unitTest u F hF x=Real.exp (u*x)*F x := by
  change Real.exp (u*FiniteGuards.clip01 x)*F (FiniteGuards.clip01 x)=_
  rw [FiniteGuards.clip01_self hx]

theorem exp_difference_upper {x y M : ℝ} (hx : x ≤ M) (hy : y ≤ M) :
    |Real.exp x-Real.exp y| ≤ Real.exp M*|x-y| := by
  have ordered {a b : ℝ} (hab : a ≤ b) (hbM : b ≤ M) :
      Real.exp b-Real.exp a ≤ Real.exp M*(b-a) := by
    apply (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
      Real.continuous_exp.continuousOn
      (fun z _ => (Real.hasDerivAt_exp z).differentiableAt.differentiableWithinAt)
      (fun z hz => by
        rw [Real.deriv_exp]
        exact Real.exp_le_exp.mpr ((interior_subset hz).2.trans hbM))
      a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonpos (sub_nonpos.mpr h),neg_sub,neg_sub]
    exact ordered h hy
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered h hx

theorem unitTest_uniform_tendsto (u : ℕ → ℝ) {u0 : ℝ}
    (hu : Tendsto u atTop (𝓝 u0)) (F : ℝ → ℝ) (hF : Continuous F) :
    TendstoUniformly (fun n => unitTest (u n) F hF) (unitTest u0 F hF) atTop := by
  let C := Real.exp (|u0|+1)*‖unitTest 0 F hF‖
  have hsmall : Tendsto (fun n => C*|u n-u0|) atTop (𝓝 0) := by
    simpa using ((hu.sub_const u0).abs).const_mul C
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have habs : Tendsto (fun n => |u n-u0|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (hu.sub_const u0).abs
  filter_upwards [habs.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    hsmall.eventually_lt_const hε] with n hn hsmalln x
  let y : ℝ := FiniteGuards.clip01 x
  have hy := FiniteGuards.clip01_bounds x
  have hux : u n*y ≤ |u0|+1 := by
    have hub : u n ≤ |u0|+1 := by linarith [le_abs_self u0,(abs_le.mp hn.le).2]
    have hmax : u n*y ≤ max (u n) 0 := by
      by_cases hpos : 0 ≤ u n
      · rw [max_eq_left hpos]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2 hpos
      · rw [max_eq_right (le_of_not_ge hpos)]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hpos) hy.1
    exact hmax.trans (max_le hub (by positivity))
  have hu0x : u0*y ≤ |u0|+1 := by
    have h := mul_le_mul_of_nonneg_right (le_abs_self u0) hy.1
    have h' := mul_le_mul_of_nonneg_left hy.2 (abs_nonneg u0)
    linarith
  have hexp := exp_difference_upper hux hu0x
  have harg : |u n*y-u0*y| ≤ |u n-u0| := by
    rw [← sub_mul,abs_mul,abs_of_nonneg hy.1]
    exact mul_le_of_le_one_right (abs_nonneg _) hy.2
  have hFbound : |F y| ≤ ‖unitTest 0 F hF‖ := by
    have hh := (unitTest 0 F hF).norm_coe_le_norm x
    simpa [unitTest,unitClip,Real.norm_eq_abs,y] using hh
  have hd : |unitTest (u n) F hF x-unitTest u0 F hF x| ≤ C*|u n-u0| := by
    change |Real.exp (u n*y)*F y-Real.exp (u0*y)*F y| ≤ _
    rw [← sub_mul,abs_mul]
    have he := hexp.trans (mul_le_mul_of_nonneg_left harg (Real.exp_pos _).le)
    have hh := mul_le_mul he hFbound (abs_nonneg _) (by positivity)
    convert! hh using 1
    dsimp only [C]
    ring
  simpa only [Real.dist_eq,abs_sub_comm] using hd.trans_lt hsmalln

theorem weighted_lower_integral_tendsto
    (ν : ℕ → ProbabilityMeasure ℝ) (ν0 : ProbabilityMeasure ℝ)
    (hν : ∀ n, ∀ᵐ x ∂(ν n:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hν0 : ∀ᵐ x ∂(ν0:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hweak : Tendsto ν atTop (𝓝 ν0))
    (u : ℕ → ℝ) {u0 : ℝ} (hu : Tendsto u atTop (𝓝 u0))
    (F : ℝ → ℝ) (hF : Continuous F) :
    Tendsto (fun n => ∫ x, Real.exp (u n*x)*F x ∂(ν n:Measure ℝ)) atTop
      (𝓝 (∫ x, Real.exp (u0*x)*F x ∂(ν0:Measure ℝ))) := by
  have ht := FCAppendix.PayOnce.KernelLawConvergence.tendsto_integral_varying_test hweak
    (fun n => unitTest (u n) F hF) (unitTest u0 F hF)
    (unitTest_uniform_tendsto u hu F hF)
  have he (n : ℕ) : (∫ x, unitTest (u n) F hF x ∂(ν n:Measure ℝ))=
      ∫ x, Real.exp (u n*x)*F x ∂(ν n:Measure ℝ) :=
    integral_congr_ae ((hν n).mono fun x hx => unitTest_eq _ _ _ hx)
  have he0 : (∫ x, unitTest u0 F hF x ∂(ν0:Measure ℝ))=
      ∫ x, Real.exp (u0*x)*F x ∂(ν0:Measure ℝ) :=
    integral_congr_ae (hν0.mono fun x hx => unitTest_eq _ _ _ hx)
  simpa only [he,he0] using ht

def normalizer (i : Row) (ν : Measure ℝ) (u : ℝ) : ℝ :=
  (1-cutoff i)*Real.exp (u/2)+cutoff i*(∫ x, Real.exp (u*x) ∂ν)

theorem normalizer_eq_mgf (i : Row) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    normalizer i ν u=mgf Prod.fst (MixedLaw.law i ν) u := by
  rw [mgf,MixedLaw.integral_law i ν hν (by fun_prop)]
  simp only [smul_eq_mul]
  unfold normalizer
  rw [show u*(1/2:ℝ)=u/2 by ring]
  ring

theorem normalizer_pos (i : Row) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    0 < normalizer i ν u := by
  rw [normalizer_eq_mgf i ν hν u]
  exact mgf_pos (integrable_exp_mul_of_bounded (MixedLaw.law i ν)
    measurable_fst.aemeasurable (MixedLaw.demand_bounds i ν hν) u)

theorem tilted_integral_ratio (i : Row) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (0:ℝ) 1) (u : ℝ)
    (F : (ℝ × ℝ) → ℝ) (hF : Continuous F) :
    (∫ p, F p ∂MixedLaw.tiltedLaw i ν u)=
      ((1-cutoff i)*Real.exp (u/2)*(F (1/2,1)+F (1/2,-1))/2+
        cutoff i*(∫ x, Real.exp (u*x)*F (x,0) ∂ν))/normalizer i ν u := by
  rw [MixedLaw.tilted_integral i ν hν u hF]
  have hZ := normalizer_pos i ν hν u
  have he : Real.exp (-cgf Prod.fst (MixedLaw.law i ν) u)=(normalizer i ν u)⁻¹ := by
    rw [cgf,← normalizer_eq_mgf i ν hν u,Real.exp_neg,Real.exp_log hZ]
  have he1 : Real.exp (u/2-cgf Prod.fst (MixedLaw.law i ν) u)=
      Real.exp (u/2)*(normalizer i ν u)⁻¹ := by
    rw [sub_eq_add_neg,Real.exp_add,he]
  have hlow : (∫ x, Real.exp (u*x-cgf Prod.fst (MixedLaw.law i ν) u)*F (x,0) ∂ν)=
      (normalizer i ν u)⁻¹*(∫ x, Real.exp (u*x)*F (x,0) ∂ν) := by
    simp_rw [sub_eq_add_neg,Real.exp_add,he,
      show ∀ x, Real.exp (u*x)*(normalizer i ν u)⁻¹*F (x,0)=
        (normalizer i ν u)⁻¹*(Real.exp (u*x)*F (x,0)) by intro x; ring]
    exact integral_const_mul _ _
  rw [he1,hlow,div_eq_mul_inv]
  ring

theorem normalizer_tendsto (i : Row)
    (ν : ℕ → ProbabilityMeasure ℝ) (ν0 : ProbabilityMeasure ℝ)
    (hν : ∀ n, ∀ᵐ x ∂(ν n:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hν0 : ∀ᵐ x ∂(ν0:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hweak : Tendsto ν atTop (𝓝 ν0))
    (u : ℕ → ℝ) {u0 : ℝ} (hu : Tendsto u atTop (𝓝 u0)) :
    Tendsto (fun n => normalizer i (ν n:Measure ℝ) (u n)) atTop
      (𝓝 (normalizer i (ν0:Measure ℝ) u0)) := by
  have hlow := weighted_lower_integral_tendsto ν ν0 hν hν0 hweak u hu
    (fun _ => (1:ℝ)) continuous_const
  simp only [mul_one] at hlow
  convert! (((Real.continuous_exp.tendsto (u0/2)).comp (hu.div_const 2)).const_mul
    (1-cutoff i)).add (hlow.const_mul (cutoff i)) using 1

theorem tilted_integral_tendsto (i : Row)
    (ν : ℕ → ProbabilityMeasure ℝ) (ν0 : ProbabilityMeasure ℝ)
    (hν : ∀ n, ∀ᵐ x ∂(ν n:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hν0 : ∀ᵐ x ∂(ν0:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hweak : Tendsto ν atTop (𝓝 ν0))
    (u : ℕ → ℝ) {u0 : ℝ} (hu : Tendsto u atTop (𝓝 u0))
    (F : (ℝ × ℝ) → ℝ) (hF : Continuous F) :
    Tendsto (fun n => ∫ p, F p ∂MixedLaw.tiltedLaw i (ν n:Measure ℝ) (u n)) atTop
      (𝓝 (∫ p, F p ∂MixedLaw.tiltedLaw i (ν0:Measure ℝ) u0)) := by
  simp_rw [tilted_integral_ratio i _ (hν _) _ F hF,
    tilted_integral_ratio i _ hν0 _ F hF]
  have hlow := weighted_lower_integral_tendsto ν ν0 hν hν0 hweak u hu
    (fun x => F (x,0)) (hF.comp (by fun_prop))
  have hupp := ((((Real.continuous_exp.tendsto (u0/2)).comp (hu.div_const 2)).const_mul (1-cutoff i)).mul_const
    (F (1/2,1)+F (1/2,-1))).div_const 2
  convert! (hupp.add (hlow.const_mul (cutoff i))).div
    (normalizer_tendsto i ν ν0 hν hν0 hweak u hu)
    (normalizer_pos i (ν0:Measure ℝ) hν0 u0).ne' using 1

def tiltedProbability (i : Row) (ν : ProbabilityMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν:Measure ℝ), x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    ProbabilityMeasure (ℝ × ℝ) :=
  ⟨MixedLaw.tiltedLaw i (ν:Measure ℝ) u,MixedLaw.tiltedLaw_probability i _ hν u⟩

theorem tiltedProbability_tendsto (i : Row)
    (ν : ℕ → ProbabilityMeasure ℝ) (ν0 : ProbabilityMeasure ℝ)
    (hν : ∀ n, ∀ᵐ x ∂(ν n:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hν0 : ∀ᵐ x ∂(ν0:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hweak : Tendsto ν atTop (𝓝 ν0))
    (u : ℕ → ℝ) {u0 : ℝ} (hu : Tendsto u atTop (𝓝 u0)) :
    Tendsto (fun n => tiltedProbability i (ν n) (hν n) (u n)) atTop
      (𝓝 (tiltedProbability i ν0 hν0 u0)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  exact tilted_integral_tendsto i ν ν0 hν hν0 hweak u hu F F.continuous

end FCAppendix.Affine.Uniform06.MixedWeakLimits
