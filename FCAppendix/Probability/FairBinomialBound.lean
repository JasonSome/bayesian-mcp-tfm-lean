import FCAppendix.Probability.PiBinomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
namespace FCAppendix.PiBinomial

def fairCentral (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

lemma fairCentral_nonneg (n : ℕ) : 0 ≤ fairCentral n := by
  unfold fairCentral
  positivity

lemma fairCentral_succ (n : ℕ) :
    fairCentral (n+1) = (((n:ℝ)+1/2)/((n:ℝ)+1))*fairCentral n := by
  have hc : ((n:ℝ)+1)*(Nat.centralBinom (n+1):ℝ) =
      2*(2*(n:ℝ)+1)*(Nat.centralBinom n:ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  unfold fairCentral
  rw [pow_succ]
  field_simp
  nlinarith only [hc]

theorem fairCentral_sq_mul_succ_le_one (n : ℕ) :
    fairCentral n ^ 2 * ((n:ℝ)+1) ≤ 1 := by
  induction n with
  | zero => norm_num [fairCentral]
  | succ n ih =>
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hfactor : ((((n:ℝ)+1/2)/((n:ℝ)+1))^2)*((n:ℝ)+2) ≤ (n:ℝ)+1 := by
      rw [div_pow, div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
      nlinarith [show (0:ℝ) ≤ n by positivity]
    rw [fairCentral_succ, mul_pow, Nat.cast_add_one]
    calc
      (((n:ℝ)+1/2)/((n:ℝ)+1))^2 * fairCentral n^2 * ((n:ℝ)+1+1) =
          fairCentral n^2 * (((((n:ℝ)+1/2)/((n:ℝ)+1))^2)*((n:ℝ)+2)) := by ring
      _ ≤ fairCentral n^2 * ((n:ℝ)+1) :=
        mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
      _ ≤ 1 := ih

lemma pmf_half_eq_choose_div (N k : ℕ) :
    pmf N (1/2) k = (N.choose k:ℝ) / 2^N := by
  by_cases hk : k ≤ N
  · unfold pmf
    norm_num only [show (1:ℝ)-1/2=1/2 by norm_num]
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk, div_pow]
    ring
  · rw [pmf, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma pmf_half_nonneg (N k : ℕ) : 0 ≤ pmf N (1/2) k := by
  rw [pmf_half_eq_choose_div]
  positivity

lemma pmf_even_le_fairCentral (n k : ℕ) : pmf (2*n) (1/2) k ≤ fairCentral n := by
  rw [pmf_half_eq_choose_div]
  unfold fairCentral
  have hp : (2:ℝ)^(2*n)=4^n := by rw [pow_mul]; norm_num
  rw [hp]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_centralBinom k n)
    (by positivity)

lemma pmf_odd_le_fairCentral (n k : ℕ) : pmf (2*n+1) (1/2) k ≤ fairCentral n := by
  cases k with
  | zero =>
    rw [pmf_half_eq_choose_div, Nat.choose_zero_right]
    have hp : (2:ℝ)^(2*n+1)=2*4^n := by rw [pow_succ, pow_mul]; norm_num; ring
    rw [hp]
    unfold fairCentral
    have hc : (1:ℝ) ≤ Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
    have hpow : (0:ℝ) < 4^n := by positivity
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*4^n) hpow).mpr
    norm_num only [Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_right hc hpow.le]
  | succ k =>
    rw [pmf_half_eq_choose_div, Nat.choose_succ_succ', Nat.cast_add]
    have hp : (2:ℝ)^(2*n+1)=2*4^n := by rw [pow_succ, pow_mul]; norm_num; ring
    rw [hp]
    unfold fairCentral
    have h1 : ((2*n).choose k:ℝ) ≤ Nat.centralBinom n := by
      exact_mod_cast Nat.choose_le_centralBinom k n
    have h2 : ((2*n).choose (k+1):ℝ) ≤ Nat.centralBinom n := by
      exact_mod_cast Nat.choose_le_centralBinom (k+1) n
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*4^n) (by positivity)).mpr
    nlinarith [show (0:ℝ) < 4^n by positivity]

theorem pmf_half_sq_mul_succ_le_two (K k : ℕ) :
    pmf K (1/2) k ^ 2 * ((K:ℝ)+1) ≤ 2 := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' K
  · have hbound := pmf_even_le_fairCentral n k
    have hsq : pmf (2*n) (1/2) k^2 ≤ fairCentral n^2 :=
      sq_le_sq₀ (pmf_half_nonneg _ _) (fairCentral_nonneg _) |>.mpr hbound
    have hcentral := fairCentral_sq_mul_succ_le_one n
    have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ (n:ℝ)+1)
    push_cast
    nlinarith [sq_nonneg (pmf (2*n) (1/2) k)]
  · have hbound := pmf_odd_le_fairCentral n k
    have hsq : pmf (2*n+1) (1/2) k^2 ≤ fairCentral n^2 :=
      sq_le_sq₀ (pmf_half_nonneg _ _) (fairCentral_nonneg _) |>.mpr hbound
    have hcentral := fairCentral_sq_mul_succ_le_one n
    have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ (n:ℝ)+1)
    push_cast
    nlinarith

theorem pmf_half_le_sqrt (K k : ℕ) :
    pmf K (1/2) k ≤ Real.sqrt (2/((K:ℝ)+1)) := by
  apply (Real.le_sqrt (pmf_half_nonneg K k) (by positivity)).mpr
  exact (le_div_iff₀ (by positivity : (0:ℝ)<(K:ℝ)+1)).mpr
    (pmf_half_sq_mul_succ_le_two K k)

end FCAppendix.PiBinomial
