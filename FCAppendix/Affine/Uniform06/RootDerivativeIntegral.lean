import FCAppendix.Affine.Uniform06.ActualRootDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.Uniform06.RootDerivativeIntegral

open MeasureTheory Set Filter Topology
open ActualRootDerivative EqualCanonicalRegularity
open scoped BigOperators

attribute [local irreducible] FCAppendix.Affine.EqualCapacity.positiveMarginal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def nonnegativeVector (B : ι → ℝ) : ι → ℝ := fun k => max 0 (B k)

def extension (ξ : ℝ) (c : ℕ) (j : ι) (a : ℝ) (B : ι → ℝ) (b : ℝ) : ℝ :=
  marginal ξ c (nonnegativeVector B) j (max a b)

theorem continuous_extension {ξ a : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (j : ι) (ha : 0 < a) : Continuous (Function.uncurry (extension ξ c j a)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let v := Function.update (nonnegativeVector p.1) j (max a p.2)
  have hv : ∀ k, 0 ≤ v k := by
    intro k
    by_cases hk : k=j
    · simp only [v,hk,Function.update_self]
      exact ha.le.trans (le_max_left _ _)
    · simp only [v,Function.update_of_ne hk,nonnegativeVector]
      exact le_max_left _ _
  have hj : 0 < v j := by
    simp only [v,Function.update_self]
    exact ha.trans_le (le_max_left _ _)
  change ContinuousAt (fun q : (ι → ℝ) × ℝ =>
    FCAppendix.Affine.EqualCapacity.positiveMarginal ξ c
      (Function.update (nonnegativeVector q.1) j (max a q.2)) j) p
  exact (FCAppendix.Affine.EqualCapacity.continuousAt_positiveMarginal_focal hξ hξ1 c v hv j hj).comp
    (show ContinuousAt (fun q : (ι → ℝ) × ℝ =>
      Function.update (nonnegativeVector q.1) j (max a q.2)) p from by
        unfold nonnegativeVector
        fun_prop)

theorem measurable_derivative (ξ : ℝ) (c : ℕ) (j : ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    Measurable (fun p : (ι → ℝ) × ℝ => derivative ξ c p.1 j p.2) := by
  have hp : Measurable (fun p : (ι → ℝ) × ℝ => marginal ξ c p.1 j p.2) :=
    ((measurable_pi_apply j).comp
      (FCAppendix.Affine.EqualCapacity.measurable_positiveMarginal ξ c hξ hξ1)).comp
        (by fun_prop)
  have hz : Measurable (fun p : (ι → ℝ) × ℝ => receipt ξ c p.1 j p.2) :=
    measurable_snd.mul (measurable_const.sub (hp.const_mul ξ))
  have hK : Measurable (fun p : (ι → ℝ) × ℝ => reciprocal ξ p.1 j (receipt ξ c p.1 j p.2)) := by
    unfold reciprocal
    apply Finset.measurable_sum
    intro k _
    have hm : Measurable (fun p : (ι → ℝ) × ℝ => p.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have hcond : MeasurableSet {p : (ι → ℝ) × ℝ |
        k ≠ j ∧ (1-ξ)*p.1 k < receipt ξ c p.1 j p.2 ∧ receipt ξ c p.1 j p.2 < p.1 k} := by
      by_cases hkj : k=j
      · simp [hkj]
      · have he : {p : (ι → ℝ) × ℝ |
            k ≠ j ∧ (1-ξ)*p.1 k < receipt ξ c p.1 j p.2 ∧ receipt ξ c p.1 j p.2 < p.1 k}=
            {p | (1-ξ)*p.1 k < receipt ξ c p.1 j p.2} ∩ {p | receipt ξ c p.1 j p.2 < p.1 k} := by
          ext p
          exact and_iff_right hkj
        rw [he]
        exact (measurableSet_lt (hm.const_mul (1-ξ)) hz).inter (measurableSet_lt hz hm)
    exact Measurable.ite hcond hm.inv measurable_const
  unfold derivative
  exact Measurable.ite ((measurableSet_lt measurable_const hp).inter
    (measurableSet_lt hp measurable_const))
    (((measurable_const.sub (hp.const_mul ξ)).mul hK).div
      ((measurable_const.add (measurable_snd.mul hK)).const_mul ξ)) measurable_const

theorem extension_eq_near {a b : ℝ} (hab : a < b)
    (ξ : ℝ) (c : ℕ) (j : ι) (B : ι → ℝ) :
    extension ξ c j a B=ᶠ[𝓝 b] marginal ξ c (nonnegativeVector B) j := by
  filter_upwards [eventually_gt_nhds hab] with z hz
  simp only [extension,max_eq_right hz.le]

theorem extension_fixed_price_ae {ξ a : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (j : ι) (ha : 0 < a) (μ : Measure (ι → ℝ)) [SFinite μ] :
    ∀ᵐ b ∂volume, a < b → ∀ᵐ B ∂μ,
      HasDerivAt (marginal ξ c (nonnegativeVector B) j)
        (derivative ξ c (nonnegativeVector B) j b) b := by
  let f := extension ξ c j a
  have hfc := continuous_extension hξ hξ1 c j ha
  let A : Set ((ι → ℝ) × ℝ) := {p | a < p.2 →
    DifferentiableAt ℝ (f p.1) p.2 ∧
      deriv (f p.1) p.2=derivative ξ c (nonnegativeVector p.1) j p.2}
  have hA : MeasurableSet A := by
    have hdf := measurableSet_of_differentiableAt_with_param ℝ hfc
    have hd := measurable_deriv_with_param hfc
    have hD := (measurable_derivative ξ c j hξ hξ1).comp
      (show Measurable (fun p : (ι → ℝ) × ℝ => (nonnegativeVector p.1,p.2)) by
        unfold nonnegativeVector; fun_prop)
    have he : A={p : (ι → ℝ) × ℝ | p.2 ≤ a} ∪
        ({p | DifferentiableAt ℝ (f p.1) p.2} ∩
          {p | deriv (f p.1) p.2=derivative ξ c (nonnegativeVector p.1) j p.2}) := by
      ext p
      simp [A,imp_iff_not_or]
    rw [he]
    exact (measurableSet_le measurable_snd measurable_const).union
      (hdf.inter (measurableSet_eq_fun hd hD))
  have hrow : ∀ᵐ B ∂μ, ∀ᵐ b ∂volume, (B,b) ∈ A := by
    apply Filter.Eventually.of_forall
    intro B
    filter_upwards [actual_derivative_ae hξ hξ1 c (nonnegativeVector B) j
      (fun k _ => le_max_left _ _)] with b hb hab
    have hh := (hb (ha.trans hab)).congr_of_eventuallyEq (extension_eq_near hab ξ c j B)
    exact ⟨hh.differentiableAt,hh.deriv⟩
  have hswap := (Measure.ae_ae_comm hA).mp hrow
  filter_upwards [hswap] with b hb hab
  filter_upwards [hb] with B hB
  have hh := (hB hab).1.hasDerivAt
  rw [(hB hab).2] at hh
  exact hh.congr_of_eventuallyEq (extension_eq_near hab ξ c j B).symm

theorem actual_fixed_price_derivative_ae {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (j : ι) (μ : Measure (ι → ℝ)) [SFinite μ]
    (hμ : ∀ᵐ B ∂μ, ∀ k, 0 ≤ B k) :
    ∀ᵐ b ∂volume, 0 < b → ∀ᵐ B ∂μ,
      HasDerivAt (marginal ξ c B j) (derivative ξ c B j b) b := by
  have hall : ∀ᵐ b ∂volume, ∀ n : ℕ, 1/((n:ℝ)+1) < b → ∀ᵐ B ∂μ,
      HasDerivAt (marginal ξ c (nonnegativeVector B) j)
        (derivative ξ c (nonnegativeVector B) j b) b :=
    ae_all_iff.mpr fun n => extension_fixed_price_ae hξ hξ1 c j (by positivity) μ
  filter_upwards [hall] with b hb hb0
  obtain ⟨n,hn⟩ := exists_nat_gt (1/b)
  have hn0 : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hnb : 1/((n:ℝ)+1) < b := by
    apply (div_lt_iff₀ hn0).mpr
    have hh := (div_lt_iff₀ hb0).mp hn
    nlinarith
  filter_upwards [hb n hnb,hμ] with B hB hnon
  have he : nonnegativeVector B=B := funext fun k => max_eq_right (hnon k)
  simpa only [he] using hB

theorem actual_lipschitz_on {ξ a : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hB : ∀ k, k ≠ j → 0 ≤ B k) (ha : 0 < a) :
    LipschitzOnWith (Real.nnabs (1/(ξ*a))) (marginal ξ c B j) (Ici a) := by
  apply LipschitzOnWith.of_le_add_mul
  intro x hx y hy
  have haξ : 0 < ξ*a := mul_pos hξ ha
  simp only [Real.coe_nnabs,abs_of_nonneg (one_div_pos.mpr haξ).le]
  rcases le_total x y with hxy | hyx
  · have hm := (actual_marginal_increment hξ hξ1 c B j hB (ha.trans_le hx) hxy).1
    change 0 ≤ marginal ξ c B j y-marginal ξ c B j x at hm
    have hn : 0 ≤ 1/(ξ*a)*dist x y := by positivity
    linarith
  · have hh := (actual_marginal_increment hξ hξ1 c B j hB (ha.trans_le hy) hyx).2
    have hcoef : (x-y)/(ξ*y) ≤ (x-y)/(ξ*a) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) haξ
        (mul_le_mul_of_nonneg_left hy hξ.le)
    have hd : dist x y=x-y := by rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [hd]
    change marginal ξ c B j x-marginal ξ c B j y ≤ _ at hh
    have hh' : marginal ξ c B j x-marginal ξ c B j y ≤ 1/(ξ*a)*(x-y) := by
      convert! hh.trans hcoef using 1
      ring
    linarith only [hh']

theorem actual_duplicate_lipschitz_on {ξ a : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hB : ∀ k, k ≠ j → 0 ≤ B k) (ha : 0 < a) :
    LipschitzOnWith (Real.nnabs (2/(ξ*a))) (fun b => (marginal ξ c B j b)^2) (Ici a) := by
  apply LipschitzOnWith.of_le_add_mul
  intro x hx y hy
  have hxP := marginal_bounds hξ hξ1 c B j x
  have hyP := marginal_bounds hξ hξ1 c B j y
  have hl := (actual_lipschitz_on hξ hξ1 c B j hB ha).dist_le_mul x hx y hy
  rw [Real.dist_eq,Real.coe_nnabs,abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(ξ*a))] at hl
  have hdiff : |(marginal ξ c B j x)^2-(marginal ξ c B j y)^2| ≤
      2*|marginal ξ c B j x-marginal ξ c B j y| := by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg hxP.1 hyP.1)]
    nlinarith [mul_nonneg (abs_nonneg (marginal ξ c B j x-marginal ξ c B j y))
      (show 0 ≤ 2-(marginal ξ c B j x+marginal ξ c B j y) by linarith [hxP.2,hyP.2])]
  simp only [Real.coe_nnabs,abs_of_nonneg (by positivity : (0:ℝ) ≤ 2/(ξ*a))]
  have hraw := le_abs_self ((marginal ξ c B j x)^2-(marginal ξ c B j y)^2)
  have hh := (hraw.trans hdiff).trans (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ) ≤ 2))
  have he : 2*(1/(ξ*a)*dist x y)=2/(ξ*a)*dist x y := by ring
  rw [he] at hh
  linarith only [hh]

attribute [local irreducible] derivative

theorem actual_integral_derivatives_ae {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (j : ι) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ B ∂μ, ∀ k, 0 ≤ B k) :
    ∀ᵐ b ∂volume, 0 < b →
      HasDerivAt (fun a => ∫ B, marginal ξ c B j a ∂μ)
        (∫ B, derivative ξ c B j b ∂μ) b ∧
      HasDerivAt (fun a => ∫ B, (marginal ξ c B j a)^2 ∂μ)
        (∫ B, 2*marginal ξ c B j b*derivative ξ c B j b ∂μ) b := by
  have hm (a : ℝ) : Measurable (fun B : ι → ℝ => marginal ξ c B j a) :=
    ((measurable_pi_apply j).comp
      (FCAppendix.Affine.EqualCapacity.measurable_positiveMarginal ξ c hξ hξ1)).comp (by fun_prop)
  filter_upwards [actual_fixed_price_derivative_ae hξ hξ1 c j μ hμ] with b hb hb0
  have hd : Measurable (fun B : ι → ℝ => derivative ξ c B j b) :=
    (measurable_derivative ξ c j hξ hξ1).comp (measurable_id.prodMk measurable_const)
  have hI : Integrable (fun B => marginal ξ c B j b) μ :=
    Integrable.of_mem_Icc 0 1 (hm b).aemeasurable
      (ae_of_all _ fun B => marginal_bounds hξ hξ1 c B j b)
  have hI2 : Integrable (fun B => (marginal ξ c B j b)^2) μ :=
    Integrable.of_mem_Icc 0 1 ((hm b).pow_const 2).aemeasurable (ae_of_all _ fun B => by
      have hh := marginal_bounds hξ hξ1 c B j b
      constructor <;> nlinarith [hh.1,hh.2])
  have hs : Ici (b/2) ∈ 𝓝 b := Ici_mem_nhds (by linarith)
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_lip hs
    (Filter.Eventually.of_forall fun a => (hm a).aestronglyMeasurable) hI hd.aestronglyMeasurable
    (hμ.mono fun B hB => actual_lipschitz_on hξ hξ1 c B j (fun k _ => hB k) (by positivity))
    (integrable_const (1/(ξ*(b/2)))) (hb hb0)
  have hsecond := hasDerivAt_integral_of_dominated_loc_of_lip hs
    (Filter.Eventually.of_forall fun a => ((hm a).pow_const 2).aestronglyMeasurable) hI2
    (((hm b).const_mul 2).mul hd).aestronglyMeasurable
    (hμ.mono fun B hB => actual_duplicate_lipschitz_on hξ hξ1 c B j
      (fun k _ => hB k) (by positivity))
    (integrable_const (2/(ξ*(b/2))))
    ((hb hb0).mono fun B hB => by simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,Pi.pow_apply,Pi.mul_apply] using! hB.pow 2)
  exact ⟨hfirst.2,hsecond.2⟩

end FCAppendix.Affine.Uniform06.RootDerivativeIntegral
