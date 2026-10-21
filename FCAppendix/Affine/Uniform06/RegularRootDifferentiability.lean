import FCAppendix.Affine.Uniform06.ActualRootDerivative
import FCAppendix.Affine.Uniform06.CanonicalCoarse

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RegularRootDifferentiability

open Set Filter Topology MeasureTheory
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual
open ActualRootDerivative EntryOwnImpact CanonicalInterior CanonicalCoarse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exposure_eventually_affine {ξ z B : ℝ}
    (hξ : 0 < ξ) (_hξ1 : ξ < 1) (hz : 0 < z)
    (hB : z ≠ B) (hκB : z ≠ (1-ξ)*B) :
    ∀ᶠ a in 𝓝 z, exposure ξ a B=exposure ξ z B-
      (if (1-ξ)*B < z ∧ z < B then B⁻¹ else 0)*(a-z)/ξ := by
  by_cases hhi : B < z
  · filter_upwards [eventually_gt_nhds hhi] with a ha
    have hn : ¬ ((1-ξ)*B < z ∧ z < B) := fun h => (lt_asymm hhi h.2).elim
    rw [exposure_zero ha.le,exposure_zero hhi.le,if_neg hn]
    ring
  · have hzB : z < B := lt_of_le_of_ne (le_of_not_gt hhi) hB
    have hB0 := hz.trans hzB
    by_cases hlo : z < (1-ξ)*B
    · have hp (a : ℝ) (ha : 0 < a) (haκ : a < (1-ξ)*B) : exposure ξ a B=1 := by
        have haB : a < B := by nlinarith [mul_pos hξ hB0]
        have hr : 1 ≤ (B-a)/(ξ*B) :=
          (le_div_iff₀ (mul_pos hξ hB0)).mpr (by nlinarith)
        rw [exposure,max_eq_left haB.le,max_eq_right (sub_nonneg.mpr haB.le),min_eq_left hr]
      filter_upwards [eventually_gt_nhds hz,eventually_lt_nhds hlo] with a ha haκ
      have hn : ¬ ((1-ξ)*B < z ∧ z < B) := fun h => (lt_asymm hlo h.1).elim
      rw [hp a ha haκ,hp z hz hlo,if_neg hn]
      ring
    · have hκ : (1-ξ)*B < z := lt_of_le_of_ne (le_of_not_gt hlo) (Ne.symm hκB)
      filter_upwards [eventually_gt_nhds hz,eventually_gt_nhds hκ,
        eventually_lt_nhds hzB] with a ha haκ haB
      rw [exposure_of_between hξ ha haB haκ.le,
        exposure_of_between hξ hz hzB hκ.le,if_pos ⟨hκ,hzB⟩]
      field_simp [hξ.ne',hB0.ne']
      ring

theorem remaining_eventually_affine {ξ z : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (B : ι → ℝ) (j : ι) (hz : 0 < z)
    (hfaces : ∀ k,k ≠ j → z ≠ B k ∧ z ≠ (1-ξ)*B k) :
    ∀ᶠ a in 𝓝 z, remainingDemand ξ B {j} a=
      remainingDemand ξ B {j} z-reciprocal ξ B j z*(a-z)/ξ := by
  have hcoord : ∀ᶠ a in 𝓝 z,∀ k,k ≠ j →
      exposure ξ a (B k)=exposure ξ z (B k)-
        (if (1-ξ)*B k < z ∧ z < B k then (B k)⁻¹ else 0)*(a-z)/ξ := by
    apply eventually_all.mpr
    intro k
    by_cases hk : k=j
    · exact Eventually.of_forall fun _ h => (h hk).elim
    · exact (exposure_eventually_affine hξ hξ1 hz (hfaces k hk).1 (hfaces k hk).2).mono
        fun _ h _ => h
  filter_upwards [hcoord] with a ha
  unfold remainingDemand reciprocal
  rw [Finset.sum_mul,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=j
  · simp [hk]
  · simpa only [Finset.mem_singleton,hk,if_false,ne_eq,not_false_eq_true,true_and] using ha k hk

theorem actual_interior_differentiable {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hB : ∀ k,k ≠ j → 0 ≤ B k) (hb : 0 < b)
    (hp : marginal ξ c B j b ∈ Ioo (0:ℝ) 1)
    (hfaces : ∀ k,k ≠ j → receipt ξ c B j b ≠ B k ∧
      receipt ξ c B j b ≠ (1-ξ)*B k) :
    DifferentiableAt ℝ (marginal ξ c B j) b := by
  let p := marginal ξ c B j
  let z := receipt ξ c B j b
  let K := reciprocal ξ B j z
  have hz : 0 < z := receipt_pos hξ hξ1 c B j hb
  have hK : 0 ≤ K := reciprocal_nonneg B j hz
  have hpc := continuousAt_marginal hξ hξ1 c B j hB hb
  have hzc : ContinuousAt (receipt ξ c B j) b :=
    continuousAt_id.mul (continuousAt_const.sub (hpc.const_mul ξ))
  have he := remaining_eventually_affine hξ hξ1 B j hz hfaces
  have hcompose := hzc.tendsto.eventually he
  let f : ℝ → ℝ := fun a => (p b*(1+b*K)+(a-b)*K/ξ)/(1+a*K)
  have hf : DifferentiableAt ℝ f b := by
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · positivity
  have heq : p=ᶠ[𝓝 b] f := by
    filter_upwards [hcompose,eventually_gt_nhds hb,
      hpc.preimage_mem_nhds (Ioo_mem_nhds hp.1 hp.2)] with a hHa ha hpa
    have hca := actual_interior_equation hξ hξ1 c B j ha hpa
    have hcb := actual_interior_equation hξ hξ1 c B j hb hp
    have hden : 0 < 1+a*K := by positivity
    dsimp only [f]
    apply (eq_div_iff hden.ne').mpr
    change remainingDemand ξ B {j} (receipt ξ c B j a)=
      remainingDemand ξ B {j} z-K*(receipt ξ c B j a-z)/ξ at hHa
    dsimp only [z,receipt,p] at hHa hca hcb ⊢
    have hHa' := congrArg (fun r : ℝ => ξ*r) hHa
    field_simp [hξ.ne'] at hHa' ⊢
    nlinarith
  exact (hf.hasDerivAt.congr_of_eventuallyEq heq).differentiableAt

theorem actual_interior_hasDerivAt {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hB : ∀ k,k ≠ j → 0 ≤ B k) (hb : 0 < b)
    (hp : marginal ξ c B j b ∈ Ioo (0:ℝ) 1)
    (hfaces : ∀ k,k ≠ j → receipt ξ c B j b ≠ B k ∧
      receipt ξ c B j b ≠ (1-ξ)*B k) :
    HasDerivAt (marginal ξ c B j)
      ((1-ξ*marginal ξ c B j b)*reciprocal ξ B j (receipt ξ c B j b)/
        (ξ*(1+b*reciprocal ξ B j (receipt ξ c B j b)))) b :=
  actual_interior_derivative hξ hξ1 c B j hB hb hp
    (actual_interior_differentiable hξ hξ1 c B j hB hb hp hfaces) hfaces

theorem remaining_update_focal (ξ : ℝ) (B : ι → ℝ) (j : ι) (a z : ℝ) :
    remainingDemand ξ (Function.update B j a) {j} z=remainingDemand ξ B {j} z := by
  unfold remainingDemand
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=j
  · subst k
    simp
  · simp [hk]

theorem continuousAt_exposure_price {ξ b : ℝ} (hξ : 0 < ξ) (hb : 0 < b) (B : ℝ) :
    ContinuousAt (fun a => exposure ξ a B) b := by
  unfold exposure
  apply continuousAt_const.min
  exact (continuousAt_const.max (continuousAt_const.sub continuousAt_id)).div
    (continuousAt_const.mul (continuousAt_const.max continuousAt_id))
    (ne_of_gt (mul_pos hξ (hb.trans_le (le_max_right _ _))))

theorem zero_face_hasDerivAt {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < b) (hstrict : (c:ℝ) < remainingDemand ξ B {j} b) :
    HasDerivAt (marginal ξ c B j) 0 b := by
  have hH : ContinuousAt (remainingDemand ξ B {j}) b := by
    unfold remainingDemand
    apply tendsto_finsetSum Finset.univ
    intro k _
    by_cases hk : k ∈ ({j}:Finset ι)
    · simp only [if_pos hk]
      exact continuousAt_const
    · simp only [if_neg hk]
      exact continuousAt_exposure_price hξ hb (B k)
  have he : marginal ξ c B j=ᶠ[𝓝 b] fun _ => (0:ℝ) := by
    filter_upwards [eventually_gt_nhds hb,hH.preimage_mem_nhds (Ioi_mem_nhds hstrict)] with a ha hHa
    apply le_antisymm _ (marginal_bounds hξ hξ1 c B j a).1
    by_contra hn
    have hh := actual_positive_implies_deficit_positive hξ hξ1 c (Function.update B j a) j
      (by simpa using ha) (lt_of_not_ge hn)
    rw [Function.update_self,remaining_update_focal] at hh
    change (c:ℝ) < remainingDemand ξ B {j} a at hHa
    linarith
  exact (hasDerivAt_const b 0).congr_of_eventuallyEq he

end FCAppendix.Affine.Uniform06.RegularRootDifferentiability
