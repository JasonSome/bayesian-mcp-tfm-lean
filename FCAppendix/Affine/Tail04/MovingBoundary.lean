import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Tail04
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
    congr 1 ; norm_num
  calc
    _ = (x ^ (1 / 5 : ℝ)) ^ 2 / x ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      field_simp

    _ = x ^ (2 / 5 : ℝ) / x ^ (1 / 2 : ℝ) := by rw [he]
    _ = x ^ (-1 / 10 : ℝ) := by
      rw [← Real.rpow_sub hx]
      congr 1 ; norm_num

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
  simpa only [Function.comp_apply,movingThreshold,neg_div] using
    (utility_error_ratio_identity (m : ℝ) (by exact_mod_cast hm)).symm

theorem allocation_error_ratio_tendsto :
    Tendsto (fun m : ℕ => (1 / Real.sqrt (m : ℝ)) /
      (1 / movingThreshold m ^ 2)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  simpa only [Function.comp_apply,movingThreshold,neg_div] using
    (allocation_error_ratio_identity (m : ℝ) (by exact_mod_cast hm)).symm

theorem exists_boundary_k (Amin Amax : ℝ)
    (hmin : 0 < Amin) (horder : Amin ≤ Amax) (hwidth : Amax < 2 * Amin) :
    ∃ k : ℝ, 1 / (4 * Amin) < k ∧ k < 1 / (2 * Amax) := by
  have hmax : 0 < Amax := hmin.trans_le horder
  apply exists_between
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * Amin)
    (by positivity : (0 : ℝ) < 2 * Amax)).2
  nlinarith

def endpointCost (A B v b : ℝ) : ℝ := B - (B - b) + A * v * (B - b) ^ 2

theorem endpointCost_square (A B v b : ℝ) (hA : A ≠ 0) (hv : v ≠ 0) :
    endpointCost A B v b = B - 1 / (4 * A * v) +
      A * v * (B - b - 1 / (2 * A * v)) ^ 2 := by
  dsimp [endpointCost]
  field_simp
  ; ring

theorem endpointCost_minimum (A B v : ℝ) (hA : 0 < A) (hv : 0 < v) :
    (∀ b, B - 1 / (4 * A * v) ≤ endpointCost A B v b) ∧
    endpointCost A B v (B - 1 / (2 * A * v)) = B - 1 / (4 * A * v) := by
  constructor
  · intro b
    rw [endpointCost_square A B v b hA.ne' hv.ne']
    have : 0 ≤ A * v * (B - b - 1 / (2 * A * v)) ^ 2 := by positivity
    linarith
  · rw [endpointCost_square A B v _ hA.ne' hv.ne']
    simp

theorem quadratic_optimizer_lt_cap (A Amax B k t : ℝ)
    (hA : 0 < A) (hmax : A ≤ Amax) (ht : 0 < t)
    (hk : k < 1 / (2 * Amax)) :
    B - 1 / (2 * A * t) < B - k / t := by
  have hamax : 0 < Amax := hA.trans_le hmax
  have hbound : 1 / (2 * Amax) ≤ 1 / (2 * A) := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hkt : k / t < (1 / (2 * A)) / t :=
    div_lt_div_of_pos_right (hk.trans_le hbound) ht
  have he : (1 / (2 * A)) / t = 1 / (2 * A * t) := by field_simp
  rw [he] at hkt
  linarith

theorem quadratic_floor_gt_cap (A Amin B k t : ℝ)
    (hmin : 0 < Amin) (hA : Amin ≤ A) (ht : 0 < t)
    (hk : 1 / (4 * Amin) < k) :
    B - k / t < B - 1 / (4 * A * t) := by
  have ha : 0 < A := hmin.trans_le hA
  have hbound : 1 / (4 * A) ≤ 1 / (4 * Amin) := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hkt : (1 / (4 * A)) / t < k / t :=
    div_lt_div_of_pos_right (hbound.trans_lt hk) ht
  have he : (1 / (4 * A)) / t = 1 / (4 * A * t) := by field_simp
  rw [he] at hkt
  linarith

theorem matched_floor_gt_cap (B k t q V c eps : ℝ)
    (_ht : 0 < t) (hq : 0 < q) (_hc : c < k)
    (happrox : |(t - V) - (B - c / t)| ≤ eps)
    (hqerror : V * (1 / q - 1) + eps < (k - c) / t) :
    B - k / t < t - V / q := by
  have hlo : B - c / t - eps ≤ t - V := by
    have := (abs_le.mp happrox).1
    linarith
  have he : t - V / q = (t - V) - V * (1 / q - 1) := by
    field_simp
    ; ring
  rw [he]
  have hmargin : (k - c) / t = k / t - c / t := sub_div _ _ _
  rw [hmargin] at hqerror
  linarith

theorem mixed_flag_lower_at_cap (e0 Delta B k t b : ℝ)
    (he : 0 < e0) (hd : 0 < Delta) (hk : 0 < k) (ht : 0 < t)
    (hb : b ≤ B - k / t) :
    e0 * (k / Delta) ^ 2 / t ^ 2 ≤ e0 * ((B - b) / Delta) ^ 2 := by
  have hgap : k / t ≤ B - b := by linarith
  have hleft : 0 ≤ k / t := by positivity
  have hsq : (k / t) ^ 2 ≤ (B - b) ^ 2 := (sq_le_sq₀ hleft (by linarith)).2 hgap
  have hm := mul_le_mul_of_nonneg_left hsq he.le
  have hd2 : 0 < Delta ^ 2 := by positivity
  have hh := div_le_div_of_nonneg_right hm hd2.le
  convert! hh using 1 <;> field_simp

theorem two_mixed_flags_lower (pA pB pBoth cA cB t : ℝ)
    (ht : 0 < t) (hA : 0 ≤ cA) (hB : 0 ≤ cB)
    (hpA : cA / t ^ 2 ≤ pA) (hpB : cB / t ^ 2 ≤ pB)
    (hind : pBoth = pA * pB) : cA * cB / t ^ 4 ≤ pBoth := by
  rw [hind]
  have hpA0 : 0 ≤ pA := (by positivity : 0 ≤ cA / t ^ 2).trans hpA
  have h := mul_le_mul hpA hpB (by positivity) hpA0
  convert! h using 1 ; field_simp

theorem rare_jump_eventually_smaller (C B c gain : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hc : 0 < c) (hgain : 0 < gain) :
    ∀ᶠ m : ℕ in atTop,
      C * (movingThreshold m + 2 * B) * (m : ℝ) * Real.exp (-c * m) <
        gain / ((m : ℝ) ^ 2 * movingThreshold m ^ 4) := by
  have hlim : Tendsto (fun m : ℕ => C * (1 + 2 * B) *
      ((m : ℝ) ^ 8 * Real.exp (-c * m))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (8 : ℝ) c hc).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
    simpa [Real.rpow_natCast] using (tendsto_const_nhds.mul h)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlim.eventually (gt_mem_nhds hgain)] with m hm herr
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht0 := movingThreshold_pos m (by omega)
  have ht1 := movingThreshold_ge_one m hm
  have htm := movingThreshold_le_population m hm
  have htb : movingThreshold m + 2 * B ≤ (1 + 2 * B) * (m : ℝ) := by
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hm1)]
  have ht4 : movingThreshold m ^ 4 ≤ (m : ℝ) ^ 4 := pow_le_pow_left₀ ht0.le htm 4
  have hbnd : (C * (movingThreshold m + 2 * B) * (m : ℝ) * Real.exp (-c * m)) *
      ((m : ℝ) ^ 2 * movingThreshold m ^ 4) ≤
      C * (1 + 2 * B) * ((m : ℝ) ^ 8 * Real.exp (-c * m)) := by
    calc
      _ ≤ (C * ((1 + 2 * B) * (m : ℝ)) * (m : ℝ) * Real.exp (-c * m)) *
          ((m : ℝ) ^ 2 * (m : ℝ) ^ 4) := by gcongr
      _ = _ := by ring
  exact (lt_div_iff₀ (by positivity)).2 (hbnd.trans_lt herr)

end FCAppendix.Affine.Tail04
