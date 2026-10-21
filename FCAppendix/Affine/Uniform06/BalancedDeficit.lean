import Mathlib.Tactic

namespace FCAppendix.Affine.Uniform06.BalancedDeficit

open scoped BigOperators

theorem max_eq_half_sum_add_abs (a b : ℝ) :
    max a b = (a + b + |a - b|) / 2 := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [max_eq_left hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

theorem exact_balanced_deficit {ι : Type*} (E : Finset ι)
    (p : ι → ℝ) (capacity upperLeft upperRight allDemand : ℝ)
    (hcard : (E.card : ℝ) = |upperLeft - upperRight|) :
    capacity - max upperLeft upperRight - (allDemand - ∑ i ∈ E, p i) =
      (capacity - (upperLeft + upperRight) / 2 - allDemand) -
        ∑ i ∈ E, ((1 : ℝ) / 2 - p i) := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hcard, max_eq_half_sum_add_abs]
  ring

theorem half_sign_cardinality (upperLeft upperRight : ℝ) :
    |upperLeft - upperRight| = 2 * |(upperLeft - upperRight) / 2| := by
  rw [abs_div]
  norm_num
  ring

theorem one_upper_not_half_sign :
    |(1 : ℝ) - 0| ≠ |((1 : ℝ) - 0) / 2| := by norm_num

theorem upper_tilted_sign_moment_zero (weight : ℝ) :
    weight / 2 * (1 : ℝ) + weight / 2 * (-1) = 0 := by ring

theorem upper_tilted_cross_moment_zero (weight : ℝ) :
    weight / 2 * ((1 : ℝ) / 2 * 1) +
      weight / 2 * ((1 : ℝ) / 2 * (-1)) = 0 := by ring

theorem upper_tilted_square_moment (weight : ℝ) :
    weight / 2 * (1 : ℝ) ^ 2 + weight / 2 * (-1) ^ 2 = weight := by ring

theorem upper_half_sign_square_moment (weight : ℝ) :
    weight / 2 * ((1 : ℝ) / 2) ^ 2 +
      weight / 2 * (-(1 : ℝ) / 2) ^ 2 = weight / 4 := by ring

theorem normalized_sign_variance (weight normalizer meanX : ℝ) :
    (weight / 2 * (1 : ℝ) ^ 2 + weight / 2 * (-1) ^ 2) / normalizer -
      ((weight / 2 * 1 + weight / 2 * (-1)) / normalizer) ^ 2 =
        weight / normalizer ∧
    (weight / 2 * ((1 : ℝ) / 2 * 1) +
        weight / 2 * ((1 : ℝ) / 2 * (-1))) / normalizer -
      meanX * ((weight / 2 * 1 + weight / 2 * (-1)) / normalizer) = 0 := by
  constructor
  · rw [upper_tilted_square_moment, upper_tilted_sign_moment_zero]
    simp
  · rw [upper_tilted_cross_moment_zero, upper_tilted_sign_moment_zero]
    simp

end FCAppendix.Affine.Uniform06.BalancedDeficit
