import FCAppendix.Probability.FiniteLaw

noncomputable section
namespace FCAppendix.Ample.Shortage
open Finset
open scoped BigOperators

private theorem sum_prod_pow {N : ℕ} {α : Type*} [Fintype α]
    (f : α → ℝ) :
    (∑ x : Fin N → α, ∏ i, f (x i)) = (∑ a, f a) ^ N := by
  classical
  have h := Fintype.prod_sum (fun (_ : Fin N) (a : α) => f a)
  rw [← h]
  simp

def iidLaw {α : Type*} [Fintype α] (μ : FiniteLaw α) (N : ℕ) :
    FiniteLaw (Fin N → α) where
  mass x := ∏ i, μ.mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => μ.nonneg (x i))
  total := by rw [sum_prod_pow, μ.total, one_pow]

theorem iid_expect_prod {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (N : ℕ) (f : α → ℝ) :
    (iidLaw μ N).expect (fun x => ∏ i, f (x i)) = (μ.expect f) ^ N := by
  classical
  unfold FiniteLaw.expect iidLaw
  simp_rw [← Finset.prod_mul_distrib]
  exact sum_prod_pow (N := N) (fun a => μ.mass a * f a)

variable {n N : ℕ}

def hits (x : Fin N → Finset (Fin n)) (j : Fin n) : ℕ :=
  ∑ i, if j ∈ x i then 1 else 0

def allHits (x : Fin N → Finset (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ∑ i, if S ⊆ x i then 1 else 0

def misses (x : Fin N → Finset (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ∑ i, if S ⊆ x i then 0 else 1

def congested (c : ℕ) (S : Finset (Fin n))
    (x : Fin N → Finset (Fin n)) : Prop := ∀ j ∈ S, c ≤ hits x j

def allMass (μ : FiniteLaw (Finset (Fin n))) (S : Finset (Fin n)) : ℝ :=
  μ.prob (fun T => S ⊆ T)

def congestionProb (μ : FiniteLaw (Finset (Fin n))) (N c : ℕ)
    (S : Finset (Fin n)) : ℝ := (iidLaw μ N).prob (congested c S)

theorem allHits_add_misses (x : Fin N → Finset (Fin n)) (S : Finset (Fin n)) :
    allHits x S + misses x S = N := by
  classical
  unfold allHits misses
  rw [← Finset.sum_add_distrib]
  have he : ∀ i : Fin N, (if S ⊆ x i then 1 else 0) +
      (if S ⊆ x i then 0 else 1) = (1 : ℕ) := by
    intro i; split_ifs <;> omega
  simp [he]

private theorem one_missing_le (S T : Finset (Fin n)) :
    (if S ⊆ T then 0 else 1 : ℕ) ≤ ∑ j ∈ S, if j ∈ T then 0 else 1 := by
  classical
  by_cases h : S ⊆ T
  · simp only [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]
    have hex : ∃ j ∈ S, j ∉ T := by
      by_contra hh
      push Not at hh
      exact h hh
    obtain ⟨j, hj, hjT⟩ := hex
    have hh := Finset.single_le_sum (f := fun j => if j ∈ T then 0 else (1 : ℕ))
      (fun _ _ => Nat.zero_le _) hj
    simpa only [if_neg hjT] using hh

theorem misses_le_of_congested (x : Fin N → Finset (Fin n))
    (S : Finset (Fin n)) (c : ℕ) (hf : congested c S x) :
    misses x S ≤ S.card * (N - c) := by
  classical
  have hpartition (j : Fin n) : hits x j +
      (∑ i, if j ∈ x i then 0 else 1) = N := by
    unfold hits
    rw [← Finset.sum_add_distrib]
    have he : ∀ i : Fin N, (if j ∈ x i then 1 else 0) +
        (if j ∈ x i then 0 else 1) = (1 : ℕ) := by
      intro i; split_ifs <;> omega
    simp [he]
  calc
    misses x S ≤ ∑ i : Fin N, ∑ j ∈ S, if j ∈ x i then 0 else 1 :=
      Finset.sum_le_sum (fun i _ => one_missing_le S (x i))
    _ = ∑ j ∈ S, ∑ i : Fin N, if j ∈ x i then 0 else 1 := Finset.sum_comm
    _ ≤ ∑ _j ∈ S, (N - c) := by
      apply Finset.sum_le_sum
      intro j hj
      have hp := hpartition j
      have hh := hf j hj
      omega
    _ = _ := by simp

theorem allHits_ge_of_congested (x : Fin N → Finset (Fin n))
    (S : Finset (Fin n)) (c : ℕ) (hf : congested c S x) :
    N - S.card * (N - c) ≤ allHits x S := by
  have hh := misses_le_of_congested x S c hf
  have hp := allHits_add_misses x S
  omega

private theorem prod_indicator {α : Type*} [Fintype α] (E : α → Prop)
    [DecidablePred E] [Decidable (∀ i, E i)] :
    (∏ i, if E i then (1 : ℝ) else 0) = if ∀ i, E i then 1 else 0 := by
  classical
  by_cases h : ∀ i, E i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem iid_all_probability (μ : FiniteLaw (Finset (Fin n)))
    (N : ℕ) (S : Finset (Fin n)) :
    (iidLaw μ N).prob (fun x => ∀ i, S ⊆ x i) = allMass μ S ^ N := by
  classical
  rw [FiniteLaw.prob_eq_expect]
  simp_rw [← prod_indicator]
  simpa only [allMass, FiniteLaw.prob_eq_expect] using
    iid_expect_prod μ N (fun T => if S ⊆ T then 1 else 0)

theorem finite_sandwich (μ : FiniteLaw (Finset (Fin n)))
    (N c : ℕ) (hc : c ≤ N) (S : Finset (Fin n)) :
    allMass μ S ^ N ≤ congestionProb μ N c S ∧
    congestionProb μ N c S ≤
      (iidLaw μ N).prob (fun x => N - S.card * (N - c) ≤ allHits x S) := by
  classical
  constructor
  · rw [← iid_all_probability]
    apply (iidLaw μ N).prob_mono
    intro x hx j hj
    have hh : hits x j = N := by
      unfold hits
      have he : ∀ i : Fin N, j ∈ x i := fun i => hx i hj
      simp [he]
    rwa [hh]
  · exact (iidLaw μ N).prob_mono (fun x hx => allHits_ge_of_congested x S c hx)

private theorem one_factor_expect (μ : FiniteLaw (Finset (Fin n)))
    (S : Finset (Fin n)) (θ : ℝ) :
    μ.expect (fun T => if S ⊆ T then 1 else Real.exp (-θ)) =
      allMass μ S + (1 - allMass μ S) * Real.exp (-θ) := by
  classical
  calc
    _ = μ.expect (fun T => Real.exp (-θ) +
        (1 - Real.exp (-θ)) * (if S ⊆ T then 1 else 0)) := by
      apply μ.expect_congr
      intro T; split_ifs <;> ring
    _ = _ := by
      rw [μ.expect_add, μ.expect_const, μ.expect_const_mul]
      rw [← FiniteLaw.prob_eq_expect]
      change Real.exp (-θ) + (1 - Real.exp (-θ)) * allMass μ S = _
      ring

private theorem exp_misses_eq_prod (x : Fin N → Finset (Fin n))
    (S : Finset (Fin n)) (θ : ℝ) :
    Real.exp (-θ * (misses x S : ℝ)) =
      ∏ i, if S ⊆ x i then 1 else Real.exp (-θ) := by
  classical
  have he : (-θ * (misses x S : ℝ)) =
      ∑ i : Fin N, if S ⊆ x i then 0 else -θ := by
    unfold misses
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; split_ifs <;> ring
  rw [he, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _; split_ifs <;> simp

theorem chernoff_shortage (μ : FiniteLaw (Finset (Fin n)))
    (N c : ℕ) (S : Finset (Fin n)) {θ : ℝ} (hθ : 0 ≤ θ) :
    congestionProb μ N c S ≤
      Real.exp (θ * (S.card : ℝ) * (N - c : ℕ)) *
        (allMass μ S + (1 - allMass μ S) * Real.exp (-θ)) ^ N := by
  classical
  have hpoint (x : Fin N → Finset (Fin n)) :
      (if congested c S x then (1 : ℝ) else 0) ≤
        Real.exp (θ * (S.card : ℝ) * (N - c : ℕ)) *
          Real.exp (-θ * (misses x S : ℝ)) := by
    rw [← Real.exp_add]
    by_cases hf : congested c S x
    · rw [if_pos hf]
      apply Real.one_le_exp
      have hh : (misses x S : ℝ) ≤ (S.card : ℝ) * (N - c : ℕ) := by
        exact_mod_cast misses_le_of_congested x S c hf
      nlinarith [mul_nonneg hθ (sub_nonneg.mpr hh)]
    · rw [if_neg hf]
      exact (Real.exp_pos _).le
  calc
    congestionProb μ N c S ≤ (iidLaw μ N).expect (fun x =>
        Real.exp (θ * (S.card : ℝ) * (N - c : ℕ)) *
          Real.exp (-θ * (misses x S : ℝ))) :=
      (iidLaw μ N).expect_mono hpoint
    _ = _ := by
      rw [(iidLaw μ N).expect_const_mul]
      simp_rw [exp_misses_eq_prod]
      rw [iid_expect_prod μ N (fun T => if S ⊆ T then 1 else Real.exp (-θ)),
        one_factor_expect]

end FCAppendix.Ample.Shortage
