import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Filter Topology Set Real

def movingThreshold (m : ℕ) : ℝ := (m : ℝ) ^ (1 / 5 : ℝ)

def movingCap (B k : ℝ) (m : ℕ) : ℝ := B - k / movingThreshold m

theorem movingThreshold_pos (m : ℕ) (hm : 0 < m) : 0 < movingThreshold m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

theorem movingThreshold_pow_five (m : ℕ) : movingThreshold m ^ 5 = (m : ℝ) := by
  dsimp [movingThreshold]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
  norm_num

theorem movingThreshold_pow_ten (m : ℕ) : movingThreshold m ^ 10 = (m : ℝ) ^ 2 := by
  rw [show 10 = 5 * 2 by norm_num, pow_mul, movingThreshold_pow_five]

theorem movingThreshold_tendsto : Tendsto movingThreshold atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
    tendsto_natCast_atTop_atTop

theorem movingThreshold_ge_one (m : ℕ) (hm : 1 ≤ m) : 1 ≤ movingThreshold m := by
  dsimp [movingThreshold]
  exact Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)

theorem movingThreshold_le_population (m : ℕ) (hm : 1 ≤ m) :
    movingThreshold m ≤ (m : ℝ) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  simpa [movingThreshold] using
    Real.rpow_le_rpow_of_exponent_le hm' (by norm_num : (1 / 5 : ℝ) ≤ 1)

theorem utility_error_ratio_identity (x : ℝ) (hx : 0 < x) :
    (x ^ (1 / 5 : ℝ) / Real.sqrt x) / (1 / x ^ (1 / 5 : ℝ)) =
      x ^ (-1 / 10 : ℝ) := by
  have hp : 0 < x ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hx _
  have hs : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have he : (x ^ (1 / 5 : ℝ)) ^ 2 = x ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1; norm_num
  calc
    _ = (x ^ (1 / 5 : ℝ)) ^ 2 / x ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      field_simp
    _ = x ^ (2 / 5 : ℝ) / x ^ (1 / 2 : ℝ) := by rw [he]
    _ = x ^ (-1 / 10 : ℝ) := by
      rw [← Real.rpow_sub hx]
      congr 1; norm_num

theorem allocation_error_ratio_identity (x : ℝ) (hx : 0 < x) :
    (1 / Real.sqrt x) / (1 / (x ^ (1 / 5 : ℝ)) ^ 2) =
      x ^ (-1 / 10 : ℝ) := by
  rw [← utility_error_ratio_identity x hx]
  have hp : 0 < x ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hx _
  have hs := Real.sqrt_pos.2 hx
  field_simp

theorem utility_error_ratio_tendsto :
    Tendsto (fun m : ℕ => (movingThreshold m / Real.sqrt (m : ℝ)) /
      (1 / movingThreshold m)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  simpa only [movingThreshold,Function.comp_def,neg_div] using
    (utility_error_ratio_identity (m : ℝ) (by exact_mod_cast hm)).symm

theorem allocation_error_ratio_tendsto :
    Tendsto (fun m : ℕ => (1 / Real.sqrt (m : ℝ)) /
      (1 / movingThreshold m ^ 2)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  simpa only [movingThreshold,Function.comp_def,neg_div] using
    (allocation_error_ratio_identity (m : ℝ) (by exact_mod_cast hm)).symm

end FCAppendix.Affine.Hybrid.Tail03
