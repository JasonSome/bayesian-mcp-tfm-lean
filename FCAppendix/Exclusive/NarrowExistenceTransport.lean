import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace FCAppendix.Exclusive.Existence

open Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def inverseLogBidSum (r : ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (-r*z i)

theorem inverseLogBidSum_pos [Nonempty ι] (r : ℝ) (z : ι → ℝ) :
    0 < inverseLogBidSum r z :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem inverseLogBidSum_le_mul_exp {r δ : ℝ} (hr : 0 ≤ r)
    (z w : ι → ℝ) (hzw : ∀ i, |z i-w i| ≤ δ) :
    inverseLogBidSum r z ≤ Real.exp (r*δ)*inverseLogBidSum r w := by
  unfold inverseLogBidSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hi := (abs_le.mp (hzw i)).1
  nlinarith

theorem abs_log_inverseLogBidSum_sub_le [Nonempty ι] {r δ : ℝ}
    (hr : 0 ≤ r) (z w : ι → ℝ) (hzw : ∀ i, |z i-w i| ≤ δ) :
    |Real.log (inverseLogBidSum r z)-Real.log (inverseLogBidSum r w)| ≤ r*δ := by
  have hz := inverseLogBidSum_pos r z
  have hw := inverseLogBidSum_pos r w
  have hup := inverseLogBidSum_le_mul_exp hr z w hzw
  have hlow := inverseLogBidSum_le_mul_exp hr w z (fun i => by
    simpa only [abs_sub_comm] using hzw i)
  have hu := Real.log_le_log hz hup
  have hl := Real.log_le_log hw hlow
  rw [Real.log_mul (Real.exp_pos _).ne' hw.ne', Real.log_exp] at hu
  rw [Real.log_mul (Real.exp_pos _).ne' hz.ne', Real.log_exp] at hl
  rw [abs_le]
  constructor <;> linarith

theorem rival_profile_score_bound [Nonempty ι] {r δ K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (z w : ι → ℝ)
    (hzw : ∀ i, |z i-w i| ≤ δ) (score : ℝ → ℝ)
    (hs : ∀ x y : ℝ,
      |score (Real.exp x)-score (Real.exp y)| ≤ (K/r)*|x-y|) :
    |score (inverseLogBidSum r z)-score (inverseLogBidSum r w)| ≤ K*δ := by
  have h := hs (Real.log (inverseLogBidSum r z)) (Real.log (inverseLogBidSum r w))
  rw [Real.exp_log (inverseLogBidSum_pos r z),
    Real.exp_log (inverseLogBidSum_pos r w)] at h
  calc
    _ ≤ (K/r)*|Real.log (inverseLogBidSum r z)-Real.log (inverseLogBidSum r w)| := h
    _ ≤ (K/r)*(r*δ) := mul_le_mul_of_nonneg_left
      (abs_log_inverseLogBidSum_sub_le hr.le z w hzw) (div_nonneg hK hr.le)
    _ = K*δ := by field_simp

end FCAppendix.Exclusive.Existence
