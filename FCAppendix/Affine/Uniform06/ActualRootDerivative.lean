import FCAppendix.Affine.Uniform06.CanonicalInterior
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.ActualRootDerivative

open Set Filter Topology MeasureTheory
open FCAppendix.Affine.ClippedResidual
open EqualCanonicalRegularity CanonicalInterior EntryOwnImpact
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def marginal (ξ : ℝ) (c : ℕ) (B : ι → ℝ) (j : ι) (b : ℝ) : ℝ :=
  EqualCapacity.positiveMarginal ξ c (Function.update B j b) j

def receipt (ξ : ℝ) (c : ℕ) (B : ι → ℝ) (j : ι) (b : ℝ) : ℝ :=
  b*(1-ξ*marginal ξ c B j b)

def reciprocal (ξ : ℝ) (B : ι → ℝ) (j : ι) (z : ℝ) : ℝ :=
  ∑ k, if k ≠ j ∧ (1-ξ)*B k < z ∧ z < B k then (B k)⁻¹ else 0

theorem marginal_bounds {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (b : ℝ) :
    marginal ξ c B j b ∈ Icc (0:ℝ) 1 := by
  have hh := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update B j b)
  exact ⟨hh.1 j,hh.2.1 j⟩

theorem receipt_pos {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hb : 0 < b) : 0 < receipt ξ c B j b := by
  have hp := marginal_bounds hξ hξ1 c B j b
  have hf : 0 < 1-ξ*marginal ξ c B j b := by
    nlinarith [mul_le_mul_of_nonneg_left hp.2 hξ.le]
  exact mul_pos hb hf

theorem reciprocal_nonneg {ξ z : ℝ} (B : ι → ℝ) (j : ι) (hz : 0 < z) :
    0 ≤ reciprocal ξ B j z := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs with hk
  · exact inv_nonneg.mpr (hz.trans hk.2.2).le
  · rfl

theorem continuousAt_marginal {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι)
    (hB : ∀ k, k ≠ j → 0 ≤ B k) (hb : 0 < b) :
    ContinuousAt (marginal ξ c B j) b := by
  have hnon : ∀ k, 0 ≤ Function.update B j b k := by
    intro k
    by_cases hk : k=j
    · simpa [hk] using hb.le
    · simpa only [Function.update_of_ne hk] using hB k hk
  exact (EqualCapacity.continuousAt_positiveMarginal_focal hξ hξ1 c
    (Function.update B j b) hnon j (by simpa using hb)).comp
    (by fun_prop : ContinuousAt (fun a : ℝ => Function.update B j a) b)

theorem actual_interior_equation {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hb : 0 < b)
    (hp : marginal ξ c B j b ∈ Ioo (0:ℝ) 1) :
    remainingDemand ξ B {j} (receipt ξ c B j b)+marginal ξ c B j b=(c:ℝ) := by
  let B' := Function.update B j b
  let p := EqualCapacity.positiveMarginal ξ c B'
  have hpb := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 B'
  obtain ⟨Λ,hΛ0,hT,hslack⟩ := EqualCapacity.positiveMarginal_threshold hξ hξ1 c B'
  have heΛ : Λ=receipt ξ c B j b := by
    simpa only [B',Function.update_self,receipt,marginal,p] using (hT.2.2 j hp.1 hp.2).symm
  have hΛ : 0 < Λ := by rw [heΛ]; exact receipt_pos hξ hξ1 c B j hb
  have hsum : (∑ k, p k)=(c:ℝ) := by
    have hz := (mul_eq_zero.mp hslack).resolve_left hΛ.ne'
    linarith
  have hcoord (k : ι) (hk : k ≠ j) : p k=exposure ξ Λ (B k) := by
    have hh := scalar_threshold_eq_exposure hξ hξ1 hΛ (hpb.1 k) (hpb.2.1 k)
      (hT.1 k) (hT.2.1 k) (hT.2.2 k)
    simpa only [B',Function.update_of_ne hk] using hh
  have he : remainingDemand ξ B {j} Λ=(∑ k, if k=j then 0 else p k) := by
    unfold remainingDemand
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k=j
    · simp [hk]
    · simp only [Finset.mem_singleton,hk,if_false,hcoord k hk]
  rw [← heΛ,he]
  change (∑ k, if k=j then 0 else p k)+p j=(c:ℝ)
  rw [sum_remove_focal]
  exact hsum

theorem exposure_price_derivative {ξ z B : ℝ}
    (hξ : 0 < ξ) (_hξ1 : ξ < 1) (hz : 0 < z)
    (hB : z ≠ B) (hκB : z ≠ (1-ξ)*B) :
    HasDerivAt (fun a => exposure ξ a B)
      (if (1-ξ)*B < z ∧ z < B then -(B⁻¹)/ξ else 0) z := by
  by_cases hhi : B < z
  · have he : (fun a => exposure ξ a B)=ᶠ[𝓝 z] fun _ => (0:ℝ) := by
      filter_upwards [eventually_gt_nhds hhi] with a ha
      exact exposure_zero ha.le
    have hn : ¬ ((1-ξ)*B < z ∧ z < B) := fun h => (lt_asymm hhi h.2).elim
    rw [if_neg hn]
    exact (hasDerivAt_const z (0:ℝ)).congr_of_eventuallyEq he
  · have hzb : z < B := lt_of_le_of_ne (le_of_not_gt hhi) hB
    have hB0 := hz.trans hzb
    by_cases hlo : z < (1-ξ)*B
    · have he : (fun a => exposure ξ a B)=ᶠ[𝓝 z] fun _ => (1:ℝ) := by
        filter_upwards [eventually_gt_nhds hz,eventually_lt_nhds hlo] with a ha haκ
        have haB : a < B := by nlinarith [mul_pos hξ hB0]
        have hr : 1 ≤ (B-a)/(ξ*B) :=
          (le_div_iff₀ (mul_pos hξ hB0)).mpr (by nlinarith)
        rw [exposure,max_eq_left haB.le,max_eq_right (sub_nonneg.mpr haB.le),min_eq_left hr]
      have hn : ¬ ((1-ξ)*B < z ∧ z < B) := fun h => (lt_asymm hlo h.1).elim
      rw [if_neg hn]
      exact (hasDerivAt_const z (1:ℝ)).congr_of_eventuallyEq he
    · have hzκ : (1-ξ)*B < z := lt_of_le_of_ne (le_of_not_gt hlo) (Ne.symm hκB)
      have he : (fun a => exposure ξ a B)=ᶠ[𝓝 z] fun a => (1-a/B)/ξ := by
        filter_upwards [eventually_gt_nhds hz,eventually_gt_nhds hzκ,
          eventually_lt_nhds hzb] with a ha haκ haB
        exact exposure_of_between hξ ha haB haκ.le
      rw [if_pos ⟨hzκ,hzb⟩]
      have hh := (((hasDerivAt_id z).div_const B).const_sub 1).div_const ξ
      convert! hh.congr_of_eventuallyEq he using 1
      simp [one_div]

theorem remaining_price_derivative {ξ z : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : ι → ℝ) (j : ι) (hz : 0 < z)
    (hfaces : ∀ k, k ≠ j → z ≠ B k ∧ z ≠ (1-ξ)*B k) :
    HasDerivAt (remainingDemand ξ B {j}) (-(reciprocal ξ B j z)/ξ) z := by
  have hd (k : ι) : HasDerivAt
      (fun a => if k ∈ ({j}:Finset ι) then 0 else exposure ξ a (B k))
      (if k ≠ j ∧ (1-ξ)*B k < z ∧ z < B k then -(B k)⁻¹/ξ else 0) z := by
    by_cases hk : k=j
    · simp only [hk,Finset.mem_singleton,if_true,ne_eq,not_true_eq_false,false_and,if_false]
      exact hasDerivAt_const _ _
    · simpa only [Finset.mem_singleton,hk,if_false,ne_eq,not_false_eq_true,true_and] using
        exposure_price_derivative hξ hξ1 hz (hfaces k hk).1 (hfaces k hk).2
  have hh := HasDerivAt.sum fun k (_ : k ∈ (Finset.univ:Finset ι)) => hd k
  convert! hh using 1
  · funext a
    simp only [remainingDemand,Finset.sum_apply]
  · unfold reciprocal
    rw [neg_div,Finset.sum_div,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring

theorem actual_interior_derivative {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι)
    (hB : ∀ k, k ≠ j → 0 ≤ B k) (hb : 0 < b)
    (hp : marginal ξ c B j b ∈ Ioo (0:ℝ) 1)
    (hd : DifferentiableAt ℝ (marginal ξ c B j) b)
    (hfaces : ∀ k, k ≠ j → receipt ξ c B j b ≠ B k ∧
      receipt ξ c B j b ≠ (1-ξ)*B k) :
    HasDerivAt (marginal ξ c B j)
      ((1-ξ*marginal ξ c B j b)*reciprocal ξ B j (receipt ξ c B j b)/
        (ξ*(1+b*reciprocal ξ B j (receipt ξ c B j b)))) b := by
  let p := marginal ξ c B j
  let k := reciprocal ξ B j (receipt ξ c B j b)
  have hz := receipt_pos hξ hξ1 c B j hb
  have hk : 0 ≤ k := reciprocal_nonneg (ξ := ξ) B j hz
  have hp' := hd.hasDerivAt
  have hlam := (hasDerivAt_id b).mul ((hp'.const_mul ξ).const_sub 1)
  have hH := (remaining_price_derivative hξ hξ1 B j hz hfaces).comp b hlam
  have htotal := hH.add hp'
  have heq : (fun a => remainingDemand ξ B {j} (receipt ξ c B j a)+p a)=ᶠ[𝓝 b]
      fun _ => (c:ℝ) := by
    have hpc := continuousAt_marginal hξ hξ1 c B j hB hb
    filter_upwards [eventually_gt_nhds hb,hpc.preimage_mem_nhds (Ioo_mem_nhds hp.1 hp.2)]
      with a ha hpa
    exact actual_interior_equation hξ hξ1 c B j ha hpa
  have hzder := htotal.unique ((hasDerivAt_const b (c:ℝ)).congr_of_eventuallyEq heq)
  have hden : 0 < ξ*(1+b*k) := by positivity
  have hsolve : deriv p b=(1-ξ*p b)*k/(ξ*(1+b*k)) := by
    apply (eq_div_iff hden.ne').mpr
    simp only [one_mul,id_eq] at hzder
    change (-k/ξ)*((1-ξ*p b)+b*(-(ξ*deriv p b)))+deriv p b=0 at hzder
    have hm := congrArg (fun z : ℝ => ξ*z) hzder
    field_simp [hξ.ne'] at hm
    nlinarith
  rw [← hsolve]
  exact hp'

def priceFromCorner (ξ : ℝ) (c : ℕ) (B : ι → ℝ) (j : ι) (z : ℝ) : ℝ :=
  z/(1-ξ*((c:ℝ)-remainingDemand ξ B {j} z))

def exceptionalPrices (ξ : ℝ) (c : ℕ) (B : ι → ℝ) (j : ι) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun k => priceFromCorner ξ c B j (B k)) ∪
    Finset.univ.image (fun k => priceFromCorner ξ c B j ((1-ξ)*B k))

theorem actual_corner_price {ξ b z : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hb : 0 < b)
    (hp : marginal ξ c B j b ∈ Ioo (0:ℝ) 1)
    (hz : receipt ξ c B j b=z) : b=priceFromCorner ξ c B j z := by
  have he := actual_interior_equation hξ hξ1 c B j hb hp
  rw [hz] at he
  have hpEq : (c:ℝ)-remainingDemand ξ B {j} z=marginal ξ c B j b := by linarith
  have hden : 0 < 1-ξ*marginal ξ c B j b := by
    nlinarith [mul_le_mul_of_nonneg_left hp.2.le hξ.le]
  unfold priceFromCorner
  rw [hpEq]
  apply (eq_div_iff hden.ne').mpr
  exact hz

theorem actual_regular_away_finite {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hb : 0 < b)
    (hp : marginal ξ c B j b ∈ Ioo (0:ℝ) 1)
    (hex : b ∉ exceptionalPrices ξ c B j) :
    ∀ k, k ≠ j → receipt ξ c B j b ≠ B k ∧ receipt ξ c B j b ≠ (1-ξ)*B k := by
  classical
  intro k _
  constructor
  · intro hk
    have he := actual_corner_price hξ hξ1 c B j hb hp hk
    apply hex
    unfold exceptionalPrices
    rw [he]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
  · intro hk
    have he := actual_corner_price hξ hξ1 c B j hb hp hk
    apply hex
    unfold exceptionalPrices
    rw [he]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)

theorem nonnegative_extension_monotone {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hB : ∀ k, k ≠ j → 0 ≤ B k) :
    Monotone (fun b => marginal ξ c B j (max 0 b)) := by
  intro b a hba
  exact LowBody.positiveMarginal_update_mono hξ hξ1 c B j hB (le_max_left _ _)
    (max_le_max_left _ hba)

theorem actual_ae_differentiable {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hB : ∀ k, k ≠ j → 0 ≤ B k) :
    ∀ᵐ b ∂volume, 0 < b → DifferentiableAt ℝ (marginal ξ c B j) b := by
  filter_upwards [(nonnegative_extension_monotone hξ hξ1 c B j hB).ae_differentiableAt]
    with b hb hb0
  have he : marginal ξ c B j=ᶠ[𝓝 b] fun a => marginal ξ c B j (max 0 a) := by
    filter_upwards [eventually_gt_nhds hb0] with a ha
    rw [max_eq_right ha.le]
  exact (hb.hasDerivAt.congr_of_eventuallyEq he).differentiableAt

def derivative (ξ : ℝ) (c : ℕ) (B : ι → ℝ) (j : ι) (b : ℝ) : ℝ :=
  if 0 < marginal ξ c B j b ∧ marginal ξ c B j b < 1 then
    (1-ξ*marginal ξ c B j b)*reciprocal ξ B j (receipt ξ c B j b)/
      (ξ*(1+b*reciprocal ξ B j (receipt ξ c B j b)))
  else 0

theorem actual_derivative_of_regular {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hB : ∀ k, k ≠ j → 0 ≤ B k) (hb : 0 < b)
    (hd : DifferentiableAt ℝ (marginal ξ c B j) b)
    (hex : b ∉ exceptionalPrices ξ c B j) :
    HasDerivAt (marginal ξ c B j) (derivative ξ c B j b) b := by
  by_cases hp : marginal ξ c B j b ∈ Ioo (0:ℝ) 1
  · change 0 < marginal ξ c B j b ∧ marginal ξ c B j b < 1 at hp
    rw [derivative,if_pos hp]
    exact actual_interior_derivative hξ hξ1 c B j hB hb hp hd
      (actual_regular_away_finite hξ hξ1 c B j hb hp hex)
  · change ¬(0 < marginal ξ c B j b ∧ marginal ξ c B j b < 1) at hp
    have hbound := marginal_bounds hξ hξ1 c B j b
    have hface : marginal ξ c B j b=0 ∨ marginal ξ c B j b=1 := by
      by_cases hz : marginal ξ c B j b=0
      · exact Or.inl hz
      · right
        have hpos : 0 < marginal ξ c B j b := lt_of_le_of_ne hbound.1 (Ne.symm hz)
        exact le_antisymm hbound.2 (le_of_not_gt (fun h => hp ⟨hpos,h⟩))
    have hz : deriv (marginal ξ c B j) b=0 := by
      rcases hface with hz | ho
      · have hm : IsLocalMin (marginal ξ c B j) b := by
          apply Filter.Eventually.of_forall
          intro a
          change marginal ξ c B j b ≤ marginal ξ c B j a
          rw [hz]
          exact (marginal_bounds hξ hξ1 c B j a).1
        exact hm.deriv_eq_zero
      · have hm : IsLocalMax (marginal ξ c B j) b := by
          apply Filter.Eventually.of_forall
          intro a
          change marginal ξ c B j a ≤ marginal ξ c B j b
          rw [ho]
          exact (marginal_bounds hξ hξ1 c B j a).2
        exact hm.deriv_eq_zero
    rw [derivative,if_neg hp,← hz]
    exact hd.hasDerivAt

theorem actual_derivative_ae {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hB : ∀ k, k ≠ j → 0 ≤ B k) :
    ∀ᵐ b ∂volume, 0 < b →
      HasDerivAt (marginal ξ c B j) (derivative ξ c B j b) b := by
  have hex := (exceptionalPrices ξ c B j).finite_toSet.countable.ae_notMem volume
  filter_upwards [actual_ae_differentiable hξ hξ1 c B j hB,hex] with b hb hex hb0
  exact actual_derivative_of_regular hξ hξ1 c B j hB hb0 (hb hb0) hex

theorem actual_derivative_bounds {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hb : 0 < b) :
    derivative ξ c B j b ∈ Icc (0:ℝ) (1/(ξ*b)) := by
  by_cases hp : marginal ξ c B j b ∈ Ioo (0:ℝ) 1
  · change 0 < marginal ξ c B j b ∧ marginal ξ c B j b < 1 at hp
    rw [derivative,if_pos hp]
    have hk := reciprocal_nonneg (ξ := ξ) B j (receipt_pos hξ hξ1 c B j hb)
    have hf : 0 ≤ 1-ξ*marginal ξ c B j b := by
      nlinarith [mul_le_mul_of_nonneg_left hp.2.le hξ.le]
    have hden : 0 < ξ*(1+b*reciprocal ξ B j (receipt ξ c B j b)) := by positivity
    refine ⟨div_nonneg (mul_nonneg hf hk) hden.le,?_⟩
    apply (div_le_div_iff₀ hden (mul_pos hξ hb)).mpr
    have hp0 := mul_nonneg hξ.le hp.1.le
    have hprod := mul_nonneg (mul_nonneg hb.le hk) hp0
    nlinarith
  · change ¬(0 < marginal ξ c B j b ∧ marginal ξ c B j b < 1) at hp
    rw [derivative,if_neg hp]
    exact ⟨le_rfl,by positivity⟩

theorem actual_first_second_derivatives_ae {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hB : ∀ k, k ≠ j → 0 ≤ B k) :
    ∀ᵐ b ∂volume, 0 < b →
      HasDerivAt (marginal ξ c B j) (derivative ξ c B j b) b ∧
      HasDerivAt (fun a => (marginal ξ c B j a)^2)
        (2*marginal ξ c B j b*derivative ξ c B j b) b := by
  filter_upwards [actual_derivative_ae hξ hξ1 c B j hB] with b hb hb0
  refine ⟨hb hb0,?_⟩
  have hh := (hb hb0).pow 2
  convert! hh using 1
  norm_num

end FCAppendix.Affine.Uniform06.ActualRootDerivative
