import FCAppendix.Model.Accounting
import FCAppendix.Probability.FiniteLaw

namespace FCAppendix

structure Schedule (n : ℕ) where
  charge : ℕ → ℝ
  zero : charge 0 = 0
  lower : ∀ r, 1 ≤ r → r ≤ n → 1 ≤ charge r
  upper : ∀ r, r ≤ n → charge r ≤ (r : ℝ)

namespace Schedule

variable {n : ℕ}

@[ext] theorem ext {A B : Schedule n} (h : ∀ r, A.charge r = B.charge r) : A = B := by
  cases A with
  | mk a ha la ua =>
    cases B with
    | mk b hb lb ub =>
      have : a = b := funext h
      subst b
      rfl

theorem nonneg (A : Schedule n) (r : ℕ) (hr : r ≤ n) : 0 ≤ A.charge r := by
  by_cases h : r = 0
  · simp [h, A.zero]
  · exact le_trans zero_le_one (A.lower r (by omega) hr)

theorem one (A : Schedule n) (hn : 1 ≤ n) : A.charge 1 = 1 := by
  have hl := A.lower 1 (by omega) hn
  have hu := A.upper 1 hn
  norm_num at hu
  exact le_antisymm hu hl

noncomputable def ppi (n : ℕ) : Schedule n where
  charge r := r
  zero := by norm_num
  lower r hr _ := by exact_mod_cast hr
  upper _ _ := le_rfl

noncomputable def once (n : ℕ) : Schedule n where
  charge := successIndicator
  zero := by simp [successIndicator]
  lower r hr _ := by simp [successIndicator, show r ≠ 0 by omega]
  upper r _ := by
    by_cases h : r = 0
    · simp [h, successIndicator]
    · simp only [successIndicator, if_neg h]
      exact_mod_cast (show 1 ≤ r by omega)

noncomputable def affine (n : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : Schedule n where
  charge r := successIndicator r + η * ((r : ℝ) - successIndicator r)
  zero := by simp [successIndicator]
  lower r hr _ := by
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    simp only [successIndicator, if_neg (show r ≠ 0 by omega)]
    nlinarith
  upper r _ := by
    by_cases hr : r = 0
    · simp [hr, successIndicator]
    · have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      simp only [successIndicator, if_neg hr]
      nlinarith

theorem affine_zero (n : ℕ) : affine n 0 (by norm_num) (by norm_num) = once n := by
  apply ext
  intro r
  simp [affine, once]

noncomputable def receiptRatio (A : Schedule n) (r : ℕ) : ℝ := A.charge r / r

theorem receiptRatio_le_one (A : Schedule n) (r : ℕ) (hr0 : 0 < r) (hrn : r ≤ n) :
    A.receiptRatio r ≤ 1 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  exact (div_le_one hr).mpr (A.upper r hrn)

theorem receiptRatio_pos (A : Schedule n) (r : ℕ) (hr0 : 0 < r) (hrn : r ≤ n) :
    0 < A.receiptRatio r := by
  apply div_pos
  · exact lt_of_lt_of_le zero_lt_one (A.lower r hr0 hrn)
  · exact_mod_cast hr0

theorem affine_ratio_lower (n r : ℕ) (hn : 0 < n) (hr : 0 < r) (hrn : r ≤ n)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (1 + ((n : ℝ) - 1) * η) / n ≤ (affine n η hη0 hη1).receiptRatio r := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrnR : (r : ℝ) ≤ n := by exact_mod_cast hrn
  unfold receiptRatio affine
  simp only [successIndicator, if_neg (Nat.ne_of_gt hr)]
  apply (div_le_div_iff₀ hnR hrR).mpr
  nlinarith

theorem affine_ratio_at_n (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (affine n η hη0 hη1).receiptRatio n = (1 + ((n : ℝ) - 1) * η) / n := by
  simp only [receiptRatio, affine, successIndicator, if_neg (Nat.ne_of_gt hn)]
  congr 1
  ring

end Schedule

theorem successIndicator_le_count (r : ℕ) : successIndicator r ≤ (r : ℝ) := by
  by_cases h : r = 0
  · simp [h, successIndicator]
  · simp only [successIndicator, if_neg h]
    exact_mod_cast (show 1 ≤ r by omega)

theorem successIndicator_nonneg (r : ℕ) : 0 ≤ successIndicator r := by
  unfold successIndicator
  split <;> norm_num

theorem successIndicator_le_one (r : ℕ) : successIndicator r ≤ 1 := by
  unfold successIndicator
  split <;> norm_num

theorem count_le_mul_success (n r : ℕ) (hr : r ≤ n) :
    (r : ℝ) ≤ n * successIndicator r := by
  by_cases h : r = 0
  · simp [h, successIndicator]
  · simp only [successIndicator, if_neg h, mul_one]
    exact_mod_cast hr

theorem factorial_le_duplicate (n r : ℕ) (hr : r ≤ n) :
    (r : ℝ) * ((r : ℝ) - 1) ≤ n * ((r : ℝ) - successIndicator r) := by
  by_cases h : r = 0
  · simp [h, successIndicator]
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hrn : (r : ℝ) ≤ n := by exact_mod_cast hr
    simp only [successIndicator, if_neg h]
    nlinarith

theorem duplicate_le_half_factorial (r : ℕ) :
    2 * ((r : ℝ) - successIndicator r) ≤ (r : ℝ) * ((r : ℝ) - 1) := by
  by_cases h0 : r = 0
  · simp [h0, successIndicator]
  by_cases h1 : r = 1
  · simp [h1, successIndicator]
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
  simp only [successIndicator, if_neg h0]
  nlinarith

theorem ppi_payoff_decomposition (v b g : ℝ) (G : ℕ → ℝ) (r : ℕ) :
    userPayoff v b g (fun j => (j : ℝ)) G r =
      (v - g - b) * successIndicator r - b * ((r : ℝ) - successIndicator r)
        - g * (G r - successIndicator r) := by
  unfold userPayoff
  ring

theorem affine_payoff_decomposition (v b g η θ : ℝ) (r : ℕ) :
    userPayoff v b g
      (fun j => successIndicator j + η * ((j : ℝ) - successIndicator j))
      (fun j => successIndicator j + θ * ((j : ℝ) - successIndicator j)) r =
      (v - b - g) * successIndicator r - (η * b + θ * g) *
        ((r : ℝ) - successIndicator r) := by
  unfold userPayoff
  ring

end FCAppendix
