import FCAppendix.PayOnce.ManyProposers
import FCAppendix.PayOnce.FocalDerivative

namespace FCAppendix.PayOnce.ManyProposers
open Set

theorem continuous_binomialMass (n j : ℕ) : Continuous (fun p => binomialMass n p j) := by
  unfold binomialMass
  fun_prop

theorem binomialMass_bounds (n j : ℕ) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    binomialMass n p j ∈ Icc (0:ℝ) 1 := by
  rw [← binomial_prob_eq_binomialMass n p hp.1 hp.2 j]
  exact ⟨FiniteLaw.prob_nonneg _ _,FiniteLaw.prob_le_one _ _⟩

theorem binomialMass_abs_sub_le (n j : ℕ) {p q : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    |binomialMass n p j-binomialMass n q j| ≤
      (n.choose j : ℝ)*((j:ℝ)+(n-j:ℕ))*|p-q| := by
  have hpow (a : ℕ) {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
      |x^a-y^a| ≤ (a:ℝ)*|x-y| := by
    have hmax : max |x| |y| ≤ (1:ℝ) := by
      rw [abs_of_nonneg hx.1,abs_of_nonneg hy.1]
      exact max_le hx.2 hy.2
    have hbound := pow_le_one₀ (le_max_of_le_left (abs_nonneg x)) hmax (n := a-1)
    have hh := abs_pow_sub_pow_le x y a
    have hmul := mul_le_mul_of_nonneg_left hbound (mul_nonneg (abs_nonneg (x-y)) (Nat.cast_nonneg a))
    nlinarith
  have hp' : 1-p ∈ Icc (0:ℝ) 1 := ⟨by linarith [hp.2],by linarith [hp.1]⟩
  have hq' : 1-q ∈ Icc (0:ℝ) 1 := ⟨by linarith [hq.2],by linarith [hq.1]⟩
  have hA := hpow j hp hq
  have hB := hpow (n-j) hp' hq'
  have hd : |(1-p)-(1-q)| = |p-q| := by
    rw [show (1-p)-(1-q) = -(p-q) by ring,abs_neg]
  rw [hd] at hB
  have he : p^j*(1-p)^(n-j)-q^j*(1-q)^(n-j) =
      (p^j-q^j)*(1-p)^(n-j)+q^j*((1-p)^(n-j)-(1-q)^(n-j)) := by ring
  have hgap : |p^j*(1-p)^(n-j)-q^j*(1-q)^(n-j)| ≤
      ((j:ℝ)+(n-j:ℕ))*|p-q| := by
    rw [he]
    have hh := abs_add_le ((p^j-q^j)*(1-p)^(n-j)) (q^j*((1-p)^(n-j)-(1-q)^(n-j)))
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hp'.1 _),abs_of_nonneg (pow_nonneg hq.1 _)] at hh
    have h₁ := mul_le_mul_of_nonneg_left (pow_le_one₀ hp'.1 hp'.2 (n := n-j)) (abs_nonneg (p^j-q^j))
    have h₂ := mul_le_mul_of_nonneg_right (pow_le_one₀ hq.1 hq.2 (n := j)) (abs_nonneg ((1-p)^(n-j)-(1-q)^(n-j)))
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (n.choose j))
  unfold binomialMass
  rw [show (n.choose j:ℝ)*p^j*(1-p)^(n-j)-(n.choose j:ℝ)*q^j*(1-q)^(n-j) =
      (n.choose j:ℝ)*(p^j*(1-p)^(n-j)-q^j*(1-q)^(n-j)) by ring,
    abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose j))]
  simpa only [mul_assoc] using hh

end FCAppendix.PayOnce.ManyProposers
