import Mathlib

namespace FCAppendix

open scoped BigOperators

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def expect (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * f ω

noncomputable def prob (μ : FiniteLaw Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact μ.expect (fun ω => if E ω then 1 else 0)

@[ext] theorem ext {μ ν : FiniteLaw Ω} (h : ∀ ω, μ.mass ω = ν.mass ω) : μ = ν := by
  cases μ with
  | mk a ha sa =>
    cases ν with
    | mk b hb sb =>
      have : a = b := funext h
      subst b
      rfl

theorem expect_congr (μ : FiniteLaw Ω) {f g : Ω → ℝ}
    (h : ∀ ω, f ω = g ω) : μ.expect f = μ.expect g := by
  unfold expect
  apply Finset.sum_congr rfl
  intro ω _
  rw [h ω]

@[simp] theorem expect_const (μ : FiniteLaw Ω) (a : ℝ) :
    μ.expect (fun _ => a) = a := by
  unfold expect
  rw [← Finset.sum_mul, μ.total, one_mul]

@[simp] theorem expect_zero (μ : FiniteLaw Ω) : μ.expect (fun _ => 0) = 0 :=
  μ.expect_const 0

theorem expect_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (μ : FiniteLaw Ω) (f : Ω → ℝ) (a : ℝ) :
    μ.expect (fun ω => f ω * a) = μ.expect f * a := by
  simp only [expect, ← mul_assoc, Finset.sum_mul]

theorem expect_const_mul (μ : FiniteLaw Ω) (a : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => a * f ω) = a * μ.expect f := by
  simp only [mul_comm a, μ.expect_mul_const]

theorem expect_finset_sum (μ : FiniteLaw Ω) {ι : Type*}
    (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  classical
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω))

theorem expect_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : μ.expect f ≤ μ.expect g := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem expect_le_const (μ : FiniteLaw Ω) {f : Ω → ℝ} {a : ℝ}
    (h : ∀ ω, f ω ≤ a) : μ.expect f ≤ a := by
  simpa using μ.expect_mono h

theorem const_le_expect (μ : FiniteLaw Ω) {f : Ω → ℝ} {a : ℝ}
    (h : ∀ ω, a ≤ f ω) : a ≤ μ.expect f := by
  simpa using μ.expect_mono h

theorem prob_eq_expect (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    μ.prob E = μ.expect (fun ω => if E ω then 1 else 0) := by
  unfold prob expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases h : E ω <;> simp [h]

theorem prob_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop) : 0 ≤ μ.prob E := by
  classical
  exact μ.expect_nonneg (fun ω => by split <;> norm_num)

theorem prob_le_one (μ : FiniteLaw Ω) (E : Ω → Prop) : μ.prob E ≤ 1 := by
  classical
  exact μ.expect_le_const (fun ω => by split <;> norm_num)

theorem prob_mono (μ : FiniteLaw Ω) {E F : Ω → Prop}
    (h : ∀ ω, E ω → F ω) : μ.prob E ≤ μ.prob F := by
  classical
  apply μ.expect_mono
  intro ω
  by_cases he : E ω
  · simp [he, h ω he]
  · simp only [he, if_false]
    split <;> norm_num

@[simp] theorem prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ => True) = 1 := by
  classical
  simp [prob]

@[simp] theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  classical
  simp [prob]

theorem prob_compl (μ : FiniteLaw Ω) (E : Ω → Prop) :
    μ.prob (fun ω => ¬ E ω) = 1 - μ.prob E := by
  classical
  calc
    _ = μ.expect (fun ω => 1 - (if E ω then 1 else 0)) := by
      apply μ.expect_congr
      intro ω
      by_cases h : E ω <;> simp [h]
    _ = _ := by rw [μ.expect_sub, μ.expect_const]; rfl

theorem prob_union_add_inter (μ : FiniteLaw Ω) (E F : Ω → Prop) :
    μ.prob (fun ω => E ω ∨ F ω) + μ.prob (fun ω => E ω ∧ F ω) =
      μ.prob E + μ.prob F := by
  classical
  rw [prob, prob, prob, prob, ← μ.expect_add, ← μ.expect_add]
  apply μ.expect_congr
  intro ω
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF]

theorem prob_union_le (μ : FiniteLaw Ω) (E F : Ω → Prop) :
    μ.prob (fun ω => E ω ∨ F ω) ≤ μ.prob E + μ.prob F := by
  have h := μ.prob_union_add_inter E F
  have hn := μ.prob_nonneg (fun ω => E ω ∧ F ω)
  linarith

theorem prob_inter_lower (μ : FiniteLaw Ω) (E F : Ω → Prop) :
    μ.prob E + μ.prob F - 1 ≤ μ.prob (fun ω => E ω ∧ F ω) := by
  have h := μ.prob_union_add_inter E F
  have hu := μ.prob_le_one (fun ω => E ω ∨ F ω)
  linarith

theorem mean_sq_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    (μ.expect f) ^ 2 ≤ μ.expect (fun ω => (f ω) ^ 2) := by
  have h := μ.expect_nonneg (fun ω => sq_nonneg (f ω - μ.expect f))
  have he : μ.expect (fun ω => (f ω - μ.expect f) ^ 2) =
      μ.expect (fun ω => (f ω) ^ 2) - (μ.expect f) ^ 2 := by
    calc
      _ = μ.expect (fun ω => (f ω) ^ 2 - 2 * μ.expect f * f ω + (μ.expect f) ^ 2) := by
        apply μ.expect_congr
        intro ω
        ring
      _ = _ := by
        rw [μ.expect_add, μ.expect_sub, μ.expect_const_mul, μ.expect_const]
        ring
  rw [he] at h
  linarith

@[simp] theorem expect_singleton [DecidableEq Ω] (μ : FiniteLaw Ω) (x : Ω) :
    μ.expect (fun ω => if ω = x then 1 else 0) = μ.mass x := by
  simp [expect]

theorem ext_expect {μ ν : FiniteLaw Ω}
    (h : ∀ f : Ω → ℝ, μ.expect f = ν.expect f) : μ = ν := by
  classical
  apply ext
  intro x
  simpa using h (fun ω => if ω = x then 1 else 0)

noncomputable def dirac (x : Ω) : FiniteLaw Ω := by
  classical
  exact {
    mass := fun ω => if ω = x then 1 else 0
    nonneg := fun ω => by split <;> norm_num
    total := by simp }

@[simp] theorem expect_dirac (x : Ω) (f : Ω → ℝ) :
    (dirac x).expect f = f x := by
  classical
  simp [expect, dirac]

noncomputable def mixture (μ ν : FiniteLaw Ω) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : FiniteLaw Ω where
  mass ω := t * μ.mass ω + (1 - t) * ν.mass ω
  nonneg ω := add_nonneg (mul_nonneg ht0 (μ.nonneg ω))
    (mul_nonneg (sub_nonneg.mpr ht1) (ν.nonneg ω))
  total := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, μ.total, ν.total]
    ring

theorem expect_mixture (μ ν : FiniteLaw Ω) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (f : Ω → ℝ) :
    (mixture μ ν t ht0 ht1).expect f = t * μ.expect f + (1 - t) * ν.expect f := by
  simp only [expect, mixture, add_mul, mul_assoc, Finset.sum_add_distrib,
    ← Finset.mul_sum]

noncomputable def map (μ : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ := by
  classical
  exact {
    mass := fun ξ => ∑ ω, if f ω = ξ then μ.mass ω else 0
    nonneg := fun ξ => Finset.sum_nonneg (fun ω _ => by
      split
      · exact μ.nonneg ω
      · exact le_rfl)
    total := by
      rw [Finset.sum_comm]
      simpa using μ.total }

theorem expect_map (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (μ.map f).expect g = μ.expect (fun ω => g (f ω)) := by
  classical
  unfold expect map
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

noncomputable def prod (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) : FiniteLaw (Ω × Ξ) where
  mass z := μ.mass z.1 * ν.mass z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) (ν.nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ν.total, mul_one, μ.total]

theorem expect_prod (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω × Ξ → ℝ) :
    (μ.prod ν).expect f = μ.expect (fun ω => ν.expect (fun ξ => f (ω, ξ))) := by
  unfold expect prod
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_assoc]

theorem expect_prod_mul (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (f : Ω → ℝ) (g : Ξ → ℝ) :
    (μ.prod ν).expect (fun z => f z.1 * g z.2) = μ.expect f * ν.expect g := by
  rw [expect_prod]
  simp only [ν.expect_const_mul, μ.expect_mul_const]

theorem sum_equiv (e : Ω ≃ Ξ) (f : Ξ → ℝ) :
    (∑ ω, f (e ω)) = ∑ ξ, f ξ := by
  classical
  apply Finset.sum_bij (fun ω _ => e ω)
  · intro ω _
    exact Finset.mem_univ _
  · intro a _ b _ hab
    exact e.injective hab
  · intro ξ _
    exact ⟨e.symm ξ, Finset.mem_univ _, e.apply_symm_apply ξ⟩
  · intro ω _
    rfl

noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := 1 / (Fintype.card Ω : ℝ)
  nonneg _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  total := by
    have h : (Fintype.card Ω : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Ω))
    simp [h]

theorem uniform_expect_equiv [Nonempty Ω] (e : Ω ≃ Ω) (f : Ω → ℝ) :
    (uniform Ω).expect (fun ω => f (e ω)) = (uniform Ω).expect f := by
  unfold expect uniform
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_equiv e f]

end FiniteLaw
end FCAppendix
