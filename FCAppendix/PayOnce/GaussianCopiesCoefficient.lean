import FCAppendix.PayOnce.GaussianSecondPositivePart
import Mathlib.Data.Nat.Choose.Cast

namespace FCAppendix.PayOnce.GaussianResponse
open MeasureTheory ProbabilityTheory

theorem copies_coefficient {n : ℕ} (hn : 2 ≤ n) {t T R : ℝ} (ht : 0 < t) (hT : 0 < T) :
    ((Nat.choose n 2:ℝ)*(2/(((n:ℝ)-1)*t))^2*R)/
      ((n:ℝ)*(2/(((n:ℝ)-1)*t))*T) = (1/t)*R/T := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Nat.cast_choose_two]
  field_simp

end FCAppendix.PayOnce.GaussianResponse
