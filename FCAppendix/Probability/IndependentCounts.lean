import FCAppendix.Probability.CountLaw

namespace FCAppendix
namespace IndependentCounts

open scoped BigOperators

noncomputable def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw Bool where
  mass b := if b then p else 1 - p
  nonneg b := by cases b <;> simp <;> linarith
  total := by
    have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [hu]
    simp

@[simp] theorem expect_bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    (bernoulli p hp0 hp1).expect f = (1 - p) * f false + p * f true := by
  have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
  unfold FiniteLaw.expect bernoulli
  rw [hu]
  simp

noncomputable def acceptance {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (accept : Ω → Bool) : ℝ := μ.prob (fun ω => accept ω = true)

theorem accept_law {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (accept : Ω → Bool) :
    μ.map accept = bernoulli (acceptance μ accept)
      (μ.prob_nonneg _) (μ.prob_le_one _) := by
  classical
  have ht : (μ.map accept).mass true = acceptance μ accept := by
    simp [FiniteLaw.map, acceptance, FiniteLaw.prob, FiniteLaw.expect, mul_ite]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : accept ω = true <;> simp [h]
  have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
  have htotal := (μ.map accept).total
  rw [hu] at htotal
  simp at htotal
  apply FiniteLaw.ext
  intro b
  cases b
  · change (μ.map accept).mass false = 1 - acceptance μ accept
    linarith
  · exact ht

def addCount (n : ℕ) (b : Bool) (r : Fin (n + 1)) : Fin (n + 2) :=
  ⟨(if b then 1 else 0) + r.val, by cases b <;> simp at * <;> omega⟩

noncomputable def independentCount {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (accept : Ω → Bool) : (n : ℕ) → CountLaw n
  | 0 => FiniteLaw.dirac 0
  | n + 1 => (μ.prod (independentCount μ accept n)).map
      (fun z => addCount n (accept z.1) z.2)

noncomputable def binomial (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : CountLaw n :=
  independentCount (bernoulli p hp0 hp1) id n

theorem independentCount_bernoulli {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (accept : Ω → Bool) (n : ℕ) :
    independentCount μ accept n = binomial n (acceptance μ accept)
      (μ.prob_nonneg _) (μ.prob_le_one _) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply FiniteLaw.ext_expect
    intro f
    change ((μ.prod (independentCount μ accept n)).map
      (fun z => addCount n (accept z.1) z.2)).expect f =
      (((bernoulli (acceptance μ accept) (μ.prob_nonneg _) (μ.prob_le_one _)).prod
      (binomial n (acceptance μ accept) (μ.prob_nonneg _) (μ.prob_le_one _))).map
      (fun z => addCount n z.1 z.2)).expect f
    rw [FiniteLaw.expect_map, FiniteLaw.expect_prod, ih]
    rw [FiniteLaw.expect_map, FiniteLaw.expect_prod]
    let g : Bool → ℝ := fun b =>
      (binomial n (acceptance μ accept) (μ.prob_nonneg _) (μ.prob_le_one _)).expect
        (fun r => f (addCount n b r))
    change μ.expect (fun ω => g (accept ω)) = _
    rw [← μ.expect_map accept g, accept_law]

theorem expect_binomial_succ (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Fin (n + 2) → ℝ) :
    (binomial (n + 1) p hp0 hp1).expect f =
      (1 - p) * (binomial n p hp0 hp1).expect (fun r => f (addCount n false r)) +
      p * (binomial n p hp0 hp1).expect (fun r => f (addCount n true r)) := by
  change (((bernoulli p hp0 hp1).prod (binomial n p hp0 hp1)).map
    (fun z => addCount n z.1 z.2)).expect f = _
  rw [FiniteLaw.expect_map, FiniteLaw.expect_prod, expect_bernoulli]

@[simp] theorem val_add_false (n : ℕ) (r : Fin (n + 1)) :
    (addCount n false r).val = r.val := by simp [addCount]

@[simp] theorem val_add_true (n : ℕ) (r : Fin (n + 1)) :
    (addCount n true r).val = 1 + r.val := by simp [addCount]

@[simp] theorem success_add_false (n : ℕ) (r : Fin (n + 1)) :
    successIndicator (addCount n false r).val = successIndicator r.val := by
  simp [addCount]

@[simp] theorem success_add_true (n : ℕ) (r : Fin (n + 1)) :
    successIndicator (addCount n true r).val = 1 := by
  simp [addCount, successIndicator]

theorem binomial_success (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).success = 1 - (1 - p) ^ n := by
  induction n with
  | zero => simp [binomial, independentCount, CountLaw.success, successIndicator]
  | succ n ih =>
    unfold CountLaw.success
    rw [expect_binomial_succ]
    simp only [success_add_false, success_add_true, FiniteLaw.expect_const]
    change (1 - p) * (binomial n p hp0 hp1).success + p * 1 = _
    rw [ih, pow_succ]
    ring

theorem binomial_load (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).load = n * p := by
  induction n with
  | zero => simp [binomial, independentCount, CountLaw.load]
  | succ n ih =>
    unfold CountLaw.load
    rw [expect_binomial_succ]
    simp only [val_add_false, val_add_true, Nat.cast_add, Nat.cast_one]
    rw [FiniteLaw.expect_add, FiniteLaw.expect_const]
    change (1 - p) * (binomial n p hp0 hp1).load +
      p * (1 + (binomial n p hp0 hp1).load) = _
    rw [ih]
    ring

theorem binomial_factorial (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).factorialMoment = (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 := by
  induction n with
  | zero => simp [binomial, independentCount, CountLaw.factorialMoment]
  | succ n ih =>
    have hplus : (binomial n p hp0 hp1).expect
        (fun r => ((addCount n true r).val : ℝ) * (((addCount n true r).val : ℝ) - 1)) =
        (binomial n p hp0 hp1).factorialMoment + 2 * (binomial n p hp0 hp1).load := by
      calc
        _ = (binomial n p hp0 hp1).expect
            (fun r => (r.val : ℝ) * ((r.val : ℝ) - 1) + 2 * (r.val : ℝ)) := by
          apply FiniteLaw.expect_congr
          intro r
          simp only [val_add_true, Nat.cast_add, Nat.cast_one]
          ring
        _ = _ := by rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul]; rfl
    unfold CountLaw.factorialMoment
    rw [expect_binomial_succ, hplus]
    simp only [val_add_false]
    change (1 - p) * (binomial n p hp0 hp1).factorialMoment +
      p * ((binomial n p hp0 hp1).factorialMoment + 2 * (binomial n p hp0 hp1).load) = _
    rw [ih, binomial_load, Nat.cast_add, Nat.cast_one]
    ring

theorem binomial_success_lt_one (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (binomial n p hp0 (le_of_lt hp1)).success < 1 := by
  rw [binomial_success]
  have h := pow_pos (sub_pos.mpr hp1) n
  linarith

end IndependentCounts
end FCAppendix
