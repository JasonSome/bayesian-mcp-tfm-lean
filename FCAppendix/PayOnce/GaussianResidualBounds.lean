import FCAppendix.PayOnce.InactiveEntryHazard

namespace FCAppendix.PayOnce
open Real

theorem mul_exp_neg_sq_le_one (x : ℝ) : x*exp (-x^2) ≤ 1 := by
  have hx : x ≤ exp (x^2) := by
    nlinarith [add_one_le_exp (x^2),sq_nonneg (x-(1:ℝ)/2)]
  calc
    x*exp (-x^2) ≤ exp (x^2)*exp (-x^2) :=
      mul_le_mul_of_nonneg_right hx (exp_pos _).le
    _ = 1 := by rw [← exp_add]; simp

theorem distance_mul_gaussian_le {M c d : ℝ} (hM : 0 < M) (hc : 0 < c) :
    d*exp (-c*M*d^2) ≤ (1/sqrt c)*M^(-(1:ℝ)/2) := by
  have hs : 0 < sqrt c*sqrt M := mul_pos (sqrt_pos.mpr hc) (sqrt_pos.mpr hM)
  have he : (sqrt c*sqrt M*d)^2 = c*M*d^2 := by
    rw [mul_pow,mul_pow,sq_sqrt hc.le,sq_sqrt hM.le]
  have hh := mul_exp_neg_sq_le_one (sqrt c*sqrt M*d)
  rw [he] at hh
  have hb : d*exp (-c*M*d^2) ≤ 1/(sqrt c*sqrt M) := by
    apply (le_div_iff₀ hs).mpr
    simp only [neg_mul]
    nlinarith only [hh]
  apply hb.trans_eq
  rw [neg_div,rpow_neg hM.le,← sqrt_eq_rpow]
  field_simp

theorem surplus_mul_derivative_error_le {M c d S ε K A : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hdε : d ≤ ε)
    (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hδ : M^(-(1:ℝ)/2) ≤ 1)
    (hsur : S ≤ K*(d+M^(-(1:ℝ)/2))) :
    S*(A*M^(-(1:ℝ)/2)+A*exp (-c*M*d^2)) ≤
      K*A*(ε+2+1/sqrt c)*M^(-(1:ℝ)/2) := by
  let δ := M^(-(1:ℝ)/2)
  have hδpos : 0 ≤ δ := rpow_nonneg hM.le _
  have htail : exp (-c*M*d^2) ≤ 1 := exp_le_one_iff.mpr (by
    have hh : 0 ≤ c*M*d^2 := by positivity
    nlinarith only [hh])
  have hdist := distance_mul_gaussian_le (d := d) hM hc
  have hprod := mul_le_mul_of_nonneg_left hdist (mul_nonneg hK hA)
  have hbd := mul_le_mul_of_nonneg_left hdε (mul_nonneg (mul_nonneg hK hA) hδpos)
  have hsq := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδ hδpos)
    (mul_nonneg hK hA)
  have htailδ := mul_le_mul_of_nonneg_left htail (mul_nonneg (mul_nonneg hK hA) hδpos)
  calc
    S*(A*δ+A*exp (-c*M*d^2)) ≤ K*(d+δ)*(A*δ+A*exp (-c*M*d^2)) :=
      mul_le_mul_of_nonneg_right hsur (by positivity)
    _ ≤ K*A*(ε+2+1/sqrt c)*δ := by dsimp only [δ] at *; nlinarith

end FCAppendix.PayOnce
