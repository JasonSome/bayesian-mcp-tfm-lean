import FCAppendix.Finite.Envelope

namespace FCAppendix
namespace Ample

variable {n : ℕ}

noncomputable def deficit (P : Interim.Problem n) (w : ℝ) : ℝ :=
  w - P.envelope (w + P.g)

@[simp] theorem deficit_zero (P : Interim.Problem n) : deficit P 0 = 0 := by
  simp [deficit]

theorem deficit_nonneg (P : Interim.Problem n) (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ deficit P w := by
  have h := P.envelope_upper (w + P.g)
  have he : w + P.g - P.g = w := by ring
  rw [he, max_eq_left hw] at h
  unfold deficit
  linarith

theorem deficit_le_net (P : Interim.Problem n) (w : ℝ) : deficit P w ≤ w := by
  have h := P.envelope_nonneg (w + P.g)
  unfold deficit
  linarith

theorem deficit_monotone (P : Interim.Problem n) : Monotone (deficit P) := by
  intro w z hwz
  have h := P.envelope_increment_le (w + P.g) (z + P.g) (by linarith)
  unfold deficit
  linarith

theorem deficit_concave_combination (P : Interim.Problem n) (w z a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * deficit P w + b * deficit P z ≤ deficit P (a * w + b * z) := by
  have h := P.envelope_convex_combination (w + P.g) (z + P.g) a b ha hb hab
  have he : a * (w + P.g) + b * (z + P.g) = a * w + b * z + P.g := by
    rw [show b = 1 - a by linarith]
    ring
  rw [he] at h
  unfold deficit
  nlinarith

theorem deficit_concave (P : Interim.Problem n) : ConcaveOn ℝ Set.univ (deficit P) := by
  refine ⟨convex_univ, ?_⟩
  intro w _ z _ a b ha hb hab
  simpa only [smul_eq_mul] using deficit_concave_combination P w z a b ha hb hab

theorem deficit_secant (P : Interim.Problem n) (w z : ℝ)
    (hw : 0 ≤ w) (hz : 0 < z) (hwz : w ≤ z) :
    (w / z) * deficit P z ≤ deficit P w := by
  have hr0 : 0 ≤ w / z := div_nonneg hw (le_of_lt hz)
  have hr1 : w / z ≤ 1 := (div_le_one hz).mpr hwz
  have h := deficit_concave_combination P z 0 (w / z) (1 - w / z)
    hr0 (sub_nonneg.mpr hr1) (by ring)
  have he : w / z * z + (1 - w / z) * 0 = w := by
    rw [div_mul_cancel₀ _ (ne_of_gt hz)]
    ring
  rw [he, deficit_zero] at h
  simpa using h

theorem deficit_ratio_bounds (P : Interim.Problem n) (w z : ℝ)
    (hw : 0 < w) (hz : 0 < z) :
    min 1 (w / z) * deficit P z ≤ deficit P w ∧
      deficit P w ≤ max 1 (w / z) * deficit P z := by
  by_cases hwz : w ≤ z
  · have hr : w / z ≤ 1 := (div_le_one hz).mpr hwz
    rw [min_eq_right hr, max_eq_left hr, one_mul]
    exact ⟨deficit_secant P w z (le_of_lt hw) hz hwz, deficit_monotone P hwz⟩
  · have hzw : z ≤ w := le_of_not_ge hwz
    have hr : 1 ≤ w / z := (le_div_iff₀ hz).mpr (by simpa using hzw)
    rw [min_eq_left hr, max_eq_right hr, one_mul]
    refine ⟨deficit_monotone P hzw, ?_⟩
    have h := deficit_secant P z w (le_of_lt hz) hw hzw
    have hm := mul_le_mul_of_nonneg_left h (le_of_lt hw)
    have he : w * (z / w) = z := by field_simp [ne_of_gt hw]
    have hf : deficit P w * z ≤ w * deficit P z := by
      rw [← mul_assoc, he] at hm
      nlinarith
    have hd : deficit P w ≤ (w * deficit P z) / z := (le_div_iff₀ hz).mpr hf
    simpa only [div_mul_eq_mul_div] using hd

theorem deficit_identity (P : Interim.Problem n) (w : ℝ)
    (a : Game.JointAction n) (ha : P.BestResponse (w + P.g) a) :
    deficit P w = w * (1 - (P.outcome a).success) +
      a.bid * (P.outcome a).charge P.A +
      P.g * ((P.outcome a).charge P.G - (P.outcome a).success) := by
  unfold deficit
  rw [← (P.bestResponse_iff_attains (w + P.g) a).mp ha]
  change w - (P.outcome a).utility (w + P.g) a.bid P.g P.A P.G = _
  have h := (P.outcome a).service_deficit (w + P.g) a.bid P.g P.A P.G
  simpa using h

theorem deficit_controls (P : Interim.Problem n) (w : ℝ) (hw : 0 < w)
    (a : Game.JointAction n) (ha : P.BestResponse (w + P.g) a) :
    1 - (P.outcome a).success ≤ deficit P w / w ∧
      a.bid * (P.outcome a).charge P.A ≤ deficit P w := by
  have h := deficit_identity P w a ha
  have h1 : 0 ≤ w * (1 - (P.outcome a).success) :=
    mul_nonneg (le_of_lt hw) (sub_nonneg.mpr (P.outcome a).success_le_one)
  have h2 := mul_nonneg a.bid_nonneg ((P.outcome a).charge_nonneg P.A)
  have h3 := mul_nonneg P.g_nonneg
    (sub_nonneg.mpr ((P.outcome a).success_le_charge P.G))
  constructor
  · apply (le_div_iff₀ hw).mpr
    nlinarith
  · linarith

end Ample
end FCAppendix
