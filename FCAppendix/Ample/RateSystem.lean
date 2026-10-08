import FCAppendix.Ample.BoundaryMass
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

namespace FCAppendix
namespace Ample

open Finset
open scoped BigOperators

noncomputable def hyperNum (n k j : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ antidiagonal j, (k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) * z ^ p.1

noncomputable def hyperPGF (n k j : ℕ) (z : ℝ) : ℝ :=
  hyperNum n k j z / (n.choose j : ℝ)

theorem hyperNum_eq_paper (n k j : ℕ) (z : ℝ) :
    hyperNum n k j z = ∑ a ∈ range (k + 1),
      (k.choose a : ℝ) * (if a ≤ j then ((n - k).choose (j - a) : ℝ) else 0) * z ^ a := by
  unfold hyperNum
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h1 : (∑ a ∈ range (j + 1), (k.choose a : ℝ) * ((n - k).choose (j - a) : ℝ) * z ^ a) =
      ∑ a ∈ range (j + k + 1),
        (k.choose a : ℝ) * (if a ≤ j then ((n - k).choose (j - a) : ℝ) else 0) * z ^ a := by
    calc (∑ a ∈ range (j + 1), (k.choose a : ℝ) * ((n - k).choose (j - a) : ℝ) * z ^ a)
        = ∑ a ∈ range (j + 1),
            (k.choose a : ℝ) * (if a ≤ j then ((n - k).choose (j - a) : ℝ) else 0) * z ^ a := by
          apply Finset.sum_congr rfl
          intro a ha
          have : a ≤ j := by simp at ha; omega
          simp [this]
      _ = _ := by
          apply Finset.sum_subset (by intro a; simp; omega)
          intro a _ ha
          have : ¬ a ≤ j := by simp at ha; omega
          simp [this]
  have h2 : (∑ a ∈ range (k + 1),
        (k.choose a : ℝ) * (if a ≤ j then ((n - k).choose (j - a) : ℝ) else 0) * z ^ a) =
      ∑ a ∈ range (j + k + 1),
        (k.choose a : ℝ) * (if a ≤ j then ((n - k).choose (j - a) : ℝ) else 0) * z ^ a := by
    apply Finset.sum_subset (by intro a; simp; omega)
    intro a _ ha
    have : k < a := by simp at ha; omega
    simp [Nat.choose_eq_zero_of_lt this]
  simp only [Nat.succ_eq_add_one]
  rw [h1, h2]

theorem hyperNum_one (n k j : ℕ) (hk : k ≤ n) : hyperNum n k j 1 = (n.choose j : ℝ) := by
  unfold hyperNum
  have hv := Nat.add_choose_eq k (n - k) j
  rw [Nat.add_sub_cancel' hk] at hv
  simp only [one_pow, mul_one]
  rw [hv]
  push_cast
  rfl

theorem hyperPGF_one (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ n) : hyperPGF n k j 1 = 1 := by
  unfold hyperPGF
  rw [hyperNum_one n k j hk]
  exact div_self (by exact_mod_cast (Nat.choose_pos hj).ne')

theorem hyperPGF_zero_routes (n k : ℕ) (z : ℝ) : hyperPGF n k 0 z = 1 := by
  simp [hyperPGF, hyperNum]

theorem hyperPGF_self (n j : ℕ) (hj : j ≤ n) (z : ℝ) : hyperPGF n n j z = z ^ j := by
  unfold hyperPGF hyperNum
  rw [Nat.sub_self, Finset.sum_eq_single_of_mem (j, 0) (by simp)]
  · simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
    have : (n.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    field_simp
  · intro p hp hne
    have h2 : p.2 ≠ 0 := by
      intro h2
      apply hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      ext <;> simp_all
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero h2)]

theorem hyperNum_nonneg (n k j : ℕ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ hyperNum n k j z := by
  unfold hyperNum
  apply Finset.sum_nonneg
  intro p _
  positivity

theorem hyperPGF_nonneg (n k j : ℕ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ hyperPGF n k j z :=
  div_nonneg (hyperNum_nonneg n k j hz) (Nat.cast_nonneg _)

theorem pow_le_hyperNum_self (n k : ℕ) {z : ℝ} (hz : 0 ≤ z) : z ^ k ≤ hyperNum n k k z := by
  unfold hyperNum
  have hmem : (k, 0) ∈ antidiagonal k := by simp
  have h := Finset.single_le_sum (f := fun p : ℕ × ℕ =>
    (k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) * z ^ p.1)
    (fun p _ => by positivity) hmem
  simpa using h

noncomputable def hyperInc (n k j : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ antidiagonal j,
    (k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) * ((k - p.1 : ℕ) : ℝ) * z ^ p.1

theorem hyperInc_nonneg (n k j : ℕ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ hyperInc n k j z := by
  unfold hyperInc
  apply Finset.sum_nonneg
  intro p _
  positivity

theorem hyperInc_pos (n k j : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) (hj : j < n) {z : ℝ}
    (hz : 0 < z) : 0 < hyperInc n k j z := by
  unfold hyperInc
  apply Finset.sum_pos'
  · intro p _
    have := hz.le
    positivity
  · refine ⟨(min j (k - 1), j - min j (k - 1)), by simp, ?_⟩
    have h1 : 0 < k.choose (min j (k - 1)) := Nat.choose_pos (by omega)
    have h2 : 0 < (n - k).choose (j - min j (k - 1)) := Nat.choose_pos (by omega)
    have h3 : 0 < k - min j (k - 1) := by omega
    have h1' : (0 : ℝ) < (k.choose (min j (k - 1)) : ℝ) := by exact_mod_cast h1
    have h2' : (0 : ℝ) < ((n - k).choose (j - min j (k - 1)) : ℝ) := by exact_mod_cast h2
    have h3' : (0 : ℝ) < ((k - min j (k - 1) : ℕ) : ℝ) := by exact_mod_cast h3
    have h4 : 0 < z ^ (min j (k - 1)) := pow_pos hz _
    positivity

theorem hyperNum_succ (n k j : ℕ) (z : ℝ) :
    ((j : ℝ) + 1) * hyperNum n k (j + 1) z =
      ∑ p ∈ antidiagonal j, (k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) *
        (((k - p.1 : ℕ) : ℝ) * z ^ (p.1 + 1) + ((n - k - p.2 : ℕ) : ℝ) * z ^ p.1) := by
  unfold hyperNum
  rw [Finset.mul_sum]
  have h1 : ∀ p ∈ antidiagonal (j + 1),
      ((j : ℝ) + 1) * ((k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) * z ^ p.1) =
        (p.1 : ℝ) * ((k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) * z ^ p.1) +
          (p.2 : ℝ) * ((k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) * z ^ p.1) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have : (p.1 : ℝ) + p.2 = j + 1 := by exact_mod_cast hp
    rw [← add_mul, this]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_succ']
  simp only [Nat.cast_zero, zero_mul, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hk := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_succ_right_eq k p.1)
  have hm := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_succ_right_eq (n - k) p.2)
  push_cast at hk hm ⊢
  linear_combination (((n - k).choose p.2 : ℝ) * z ^ (p.1 + 1)) * hk +
    ((k.choose p.1 : ℝ) * z ^ p.1) * hm

theorem hyperNum_succ_sub (n k j : ℕ) (hk : k ≤ n) (z : ℝ) :
    ((j : ℝ) + 1) * hyperNum n k (j + 1) z - ((n - j : ℕ) : ℝ) * hyperNum n k j z =
      (z - 1) * hyperInc n k j z := by
  rw [hyperNum_succ, hyperNum, hyperInc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases ha : p.1 ≤ k
  · by_cases hb : p.2 ≤ n - k
    · have hc : ((k - p.1 : ℕ) : ℝ) + ((n - k - p.2 : ℕ) : ℝ) = ((n - j : ℕ) : ℝ) := by
        have : k - p.1 + (n - k - p.2) = n - j := by omega
        exact_mod_cast this
      rw [← hc]
      ring
    · simp [Nat.choose_eq_zero_of_lt (show n - k < p.2 by omega)]
  · simp [Nat.choose_eq_zero_of_lt (show k < p.1 by omega)]

theorem hyperPGF_succ_sub (n k j : ℕ) (hk : k ≤ n) (hj : j < n) (z : ℝ) :
    hyperPGF n k (j + 1) z - hyperPGF n k j z =
      (z - 1) * hyperInc n k j z / ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) := by
  have hc := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_succ_right_eq n j)
  push_cast at hc
  have hNj : (n.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj.le).ne'
  have hNj1 : (n.choose (j + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  have hnj : ((n - j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - j ≠ 0 by omega)
  have e1 : hyperPGF n k (j + 1) z = ((j : ℝ) + 1) * hyperNum n k (j + 1) z /
      ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) := by
    rw [hyperPGF, ← hc]
    field_simp
  have e2 : hyperPGF n k j z = ((n - j : ℕ) : ℝ) * hyperNum n k j z /
      ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) := by
    rw [hyperPGF]
    field_simp
  rw [e1, e2, ← sub_div, hyperNum_succ_sub n k j hk z]

theorem hyperPGF_step_le (n k j : ℕ) (hk : k ≤ n) (hj : j < n) {z : ℝ} (hz : 1 ≤ z) :
    hyperPGF n k j z ≤ hyperPGF n k (j + 1) z := by
  have h := hyperPGF_succ_sub n k j hk hj z
  have hpos : 0 ≤ (z - 1) * hyperInc n k j z / ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) :=
    div_nonneg (mul_nonneg (by linarith) (hyperInc_nonneg n k j (by linarith)))
      (by positivity)
  linarith

theorem hyperPGF_step_lt (n k j : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) (hj : j < n) {z : ℝ}
    (hz : 1 < z) : hyperPGF n k j z < hyperPGF n k (j + 1) z := by
  have h := hyperPGF_succ_sub n k j hk hj z
  have hNj : (0 : ℝ) < (n.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj.le
  have hnj : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - j by omega)
  have hpos : 0 < (z - 1) * hyperInc n k j z / ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) :=
    div_pos (mul_pos (by linarith) (hyperInc_pos n k j hk1 hk hj (by linarith)))
      (mul_pos hNj hnj)
  linarith

theorem hyperPGF_mono (n k : ℕ) (hk : k ≤ n) {z : ℝ} (hz : 1 ≤ z) {i j : ℕ} (hij : i ≤ j)
    (hjn : j ≤ n) : hyperPGF n k i z ≤ hyperPGF n k j z := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (hyperPGF_step_le n k j hk (by omega) hz)

theorem hyperPGF_strictMono (n k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) {z : ℝ} (hz : 1 < z)
    {i j : ℕ} (hij : i < j) (hjn : j ≤ n) : hyperPGF n k i z < hyperPGF n k j z := by
  induction j, hij using Nat.le_induction with
  | base => exact hyperPGF_step_lt n k i hk1 hk (by omega) hz
  | succ j _ ih => exact (ih (by omega)).trans (hyperPGF_step_lt n k j hk1 hk (by omega) hz)

theorem one_le_hyperPGF (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ n) {z : ℝ} (hz : 1 ≤ z) :
    1 ≤ hyperPGF n k j z := by
  have h := hyperPGF_mono n k hk hz (Nat.zero_le j) hj
  rwa [hyperPGF_zero_routes] at h

theorem one_lt_hyperPGF (n k j : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) (hj1 : 1 ≤ j) (hj : j ≤ n)
    {z : ℝ} (hz : 1 < z) : 1 < hyperPGF n k j z := by
  have h := hyperPGF_strictMono n k hk1 hk hz (show 0 < j by omega) hj
  rwa [hyperPGF_zero_routes] at h

noncomputable def contactGain (n k j : ℕ) (θ : ℝ) : ℝ :=
  hyperPGF n k j (Real.exp θ) - 1

theorem contactGain_nonneg (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ n) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ contactGain n k j θ := by
  have := one_le_hyperPGF n k j hk hj (Real.one_le_exp hθ)
  unfold contactGain
  linarith

theorem contactGain_pos (n k j : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) (hj1 : 1 ≤ j) (hj : j ≤ n)
    {θ : ℝ} (hθ : 0 < θ) : 0 < contactGain n k j θ := by
  have := one_lt_hyperPGF n k j hk1 hk hj1 hj (Real.one_lt_exp_iff.mpr hθ)
  unfold contactGain
  linarith

theorem contactGain_mono (n k : ℕ) (hk : k ≤ n) {θ : ℝ} (hθ : 0 ≤ θ) {i j : ℕ} (hij : i ≤ j)
    (hjn : j ≤ n) : contactGain n k i θ ≤ contactGain n k j θ := by
  have := hyperPGF_mono n k hk (Real.one_le_exp hθ) hij hjn
  unfold contactGain
  linarith

theorem contactGain_strictMono (n k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) {θ : ℝ} (hθ : 0 < θ)
    {i j : ℕ} (hij : i < j) (hjn : j ≤ n) : contactGain n k i θ < contactGain n k j θ := by
  have := hyperPGF_strictMono n k hk1 hk (Real.one_lt_exp_iff.mpr hθ) hij hjn
  unfold contactGain
  linarith

theorem contactGain_zero (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ n) : contactGain n k j 0 = 0 := by
  simp [contactGain, hyperPGF_one n k j hk hj]

noncomputable def prefixMGF (n k : ℕ) (π : ℕ → ℝ) (θ : ℝ) : ℝ :=
  1 + ∑ j ∈ Icc 1 k, π j * contactGain n k j θ

noncomputable def prefixObjective (n : ℕ) (ρ : ℝ) (k : ℕ) (π : ℕ → ℝ) (θ : ℝ) : ℝ :=
  (k : ℝ) * ρ * θ - Real.log (prefixMGF n k π θ)

noncomputable def prefixRate (n : ℕ) (ρ : ℝ) (k : ℕ) (π : ℕ → ℝ) : ℝ :=
  ⨆ θ : Set.Ici (0 : ℝ), prefixObjective n ρ k π θ

noncomputable def fullMGF (n : ℕ) (h : ℝ) (π : ℕ → ℝ) (θ : ℝ) : ℝ :=
  1 - h + ∑ j ∈ Icc 1 n, π j * Real.exp ((j : ℝ) * θ)

noncomputable def fullObjective (n : ℕ) (ρ h : ℝ) (π : ℕ → ℝ) (θ : ℝ) : ℝ :=
  (n : ℝ) * ρ * θ - Real.log (fullMGF n h π θ)

noncomputable def fullRate (n : ℕ) (ρ h : ℝ) (π : ℕ → ℝ) : ℝ :=
  ⨆ θ : Set.Ici (0 : ℝ), fullObjective n ρ h π θ

theorem one_le_prefixMGF {n k : ℕ} (hk : k ≤ n) {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j)
    {θ : ℝ} (hθ : 0 ≤ θ) : 1 ≤ prefixMGF n k π θ := by
  unfold prefixMGF
  have : 0 ≤ ∑ j ∈ Icc 1 k, π j * contactGain n k j θ := by
    apply Finset.sum_nonneg
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact mul_nonneg (hπ j hj) (contactGain_nonneg n k j hk (by omega) hθ)
  linarith

theorem prefixMGF_pos {n k : ℕ} (hk : k ≤ n) {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j)
    {θ : ℝ} (hθ : 0 ≤ θ) : 0 < prefixMGF n k π θ :=
  lt_of_lt_of_le one_pos (one_le_prefixMGF hk hπ hθ)

theorem prefixMGF_zero {n k : ℕ} (hk : k ≤ n) (π : ℕ → ℝ) : prefixMGF n k π 0 = 1 := by
  unfold prefixMGF
  rw [Finset.sum_eq_zero]
  · ring
  · intro j hj
    have := mem_Icc.mp hj
    rw [contactGain_zero n k j hk (by omega), mul_zero]

theorem prefixObjective_zero {n k : ℕ} (hk : k ≤ n) (ρ : ℝ) (π : ℕ → ℝ) :
    prefixObjective n ρ k π 0 = 0 := by
  simp [prefixObjective, prefixMGF_zero hk]

theorem continuous_prefixMGF (n k : ℕ) (π : ℕ → ℝ) : Continuous (prefixMGF n k π) := by
  unfold prefixMGF contactGain hyperPGF hyperNum
  fun_prop

theorem prefixMGF_ge_leading {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) {θ : ℝ} (hθ : 0 ≤ θ) :
    min 1 (π k) / (n.choose k : ℝ) * Real.exp ((k : ℝ) * θ) ≤ prefixMGF n k π θ := by
  have hkmem : k ∈ Icc 1 k := mem_Icc.mpr ⟨hk1, le_rfl⟩
  have hsum : π k * contactGain n k k θ ≤ ∑ j ∈ Icc 1 k, π j * contactGain n k j θ :=
    Finset.single_le_sum (f := fun j => π j * contactGain n k j θ)
      (fun j hj => mul_nonneg (hπ j hj)
        (contactGain_nonneg n k j hk (by have := mem_Icc.mp hj; omega) hθ)) hkmem
  have hT := contactGain_nonneg n k k hk hk hθ
  have hC : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hlead : Real.exp ((k : ℝ) * θ) / (n.choose k : ℝ) ≤ hyperPGF n k k (Real.exp θ) := by
    unfold hyperPGF
    rw [Real.exp_nat_mul]
    exact div_le_div_of_nonneg_right (pow_le_hyperNum_self n k (Real.exp_pos θ).le) hC.le
  have hπk := hπ k hkmem
  have hmin : min 1 (π k) * (1 + contactGain n k k θ) ≤ 1 + π k * contactGain n k k θ := by
    rcases le_total 1 (π k) with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      nlinarith
  have hmin0 : 0 ≤ min 1 (π k) := le_min zero_le_one hπk
  unfold prefixMGF
  calc min 1 (π k) / (n.choose k : ℝ) * Real.exp ((k : ℝ) * θ)
      = min 1 (π k) * (Real.exp ((k : ℝ) * θ) / (n.choose k : ℝ)) := by ring
    _ ≤ min 1 (π k) * (1 + contactGain n k k θ) := by
        apply mul_le_mul_of_nonneg_left _ hmin0
        unfold contactGain
        linarith
    _ ≤ 1 + π k * contactGain n k k θ := hmin
    _ ≤ 1 + ∑ j ∈ Icc 1 k, π j * contactGain n k j θ := by linarith

theorem prefixObjective_le_of_leading {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ}
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπk : 0 < π k) {θ : ℝ} (hθ : 0 ≤ θ) :
    prefixObjective n ρ k π θ ≤
      Real.log ((n.choose k : ℝ) / min 1 (π k)) - (k : ℝ) * (1 - ρ) * θ := by
  have hC : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hm : 0 < min 1 (π k) := lt_min one_pos hπk
  have hc : 0 < min 1 (π k) / (n.choose k : ℝ) := div_pos hm hC
  have hM := prefixMGF_ge_leading hk1 hk hπ hθ
  have hlog := Real.log_le_log (by positivity) hM
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hinv : Real.log ((n.choose k : ℝ) / min 1 (π k)) =
      - Real.log (min 1 (π k) / (n.choose k : ℝ)) := by
    rw [← Real.log_inv, inv_div]
  unfold prefixObjective
  rw [hinv]
  linarith

theorem prefixObjective_bddAbove {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπk : 0 < π k) :
    BddAbove (Set.range fun θ : Set.Ici (0 : ℝ) => prefixObjective n ρ k π θ) := by
  refine ⟨Real.log ((n.choose k : ℝ) / min 1 (π k)), ?_⟩
  rintro _ ⟨θ, rfl⟩
  have h := prefixObjective_le_of_leading hk1 hk (ρ := ρ) hπ hπk θ.2
  have h0 : 0 ≤ (k : ℝ) * (1 - ρ) * (θ : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) θ.2
  dsimp only
  linarith

theorem prefixObjective_le_prefixRate {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ}
    (hρ : ρ ≤ 1) {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπk : 0 < π k) {θ : ℝ}
    (hθ : 0 ≤ θ) : prefixObjective n ρ k π θ ≤ prefixRate n ρ k π :=
  le_ciSup (f := fun θ : Set.Ici (0 : ℝ) => prefixObjective n ρ k π θ)
    (prefixObjective_bddAbove hk1 hk hρ hπ hπk) ⟨θ, hθ⟩

theorem prefixRate_nonneg {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπk : 0 < π k) : 0 ≤ prefixRate n ρ k π := by
  have h := prefixObjective_le_prefixRate hk1 hk hρ hπ hπk (le_refl (0 : ℝ))
  rwa [prefixObjective_zero hk] at h

theorem prefixRate_attained {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ < 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπk : 0 < π k) :
    ∃ θ, 0 ≤ θ ∧ prefixObjective n ρ k π θ = prefixRate n ρ k π ∧
      ∀ θ', 0 ≤ θ' → prefixObjective n ρ k π θ' ≤ prefixObjective n ρ k π θ := by
  set L := Real.log ((n.choose k : ℝ) / min 1 (π k)) with hL
  have hkr : 0 < (k : ℝ) * (1 - ρ) :=
    mul_pos (by exact_mod_cast (show 0 < k by omega)) (by linarith)
  set R := max 0 (L / ((k : ℝ) * (1 - ρ))) with hR
  have hcont : ContinuousOn (prefixObjective n ρ k π) (Set.Icc 0 R) := by
    unfold prefixObjective
    apply ContinuousOn.sub (by fun_prop)
    apply ContinuousOn.log (continuous_prefixMGF n k π).continuousOn
    intro θ hθ
    exact (prefixMGF_pos hk hπ hθ.1).ne'
  obtain ⟨θ0, hθ0, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, Set.left_mem_Icc.mpr (le_max_left _ _)⟩ hcont
  rw [isMaxOn_iff] at hmax
  have hglobal : ∀ θ', 0 ≤ θ' → prefixObjective n ρ k π θ' ≤ prefixObjective n ρ k π θ0 := by
    intro θ' hθ'
    by_cases hθR : θ' ≤ R
    · exact hmax θ' ⟨hθ', hθR⟩
    · have h1 := prefixObjective_le_of_leading hk1 hk (ρ := ρ) hπ hπk hθ'
      have h2 : L ≤ (k : ℝ) * (1 - ρ) * θ' := by
        have : L / ((k : ℝ) * (1 - ρ)) < θ' := lt_of_le_of_lt (le_max_right _ _) (not_le.mp hθR)
        rw [div_lt_iff₀ hkr] at this
        linarith
      have h0 := hmax 0 ⟨le_rfl, le_max_left _ _⟩
      rw [prefixObjective_zero hk] at h0
      linarith
  refine ⟨θ0, hθ0.1, ?_, hglobal⟩
  apply le_antisymm
  · exact prefixObjective_le_prefixRate hk1 hk hρ.le hπ hπk hθ0.1
  · exact ciSup_le fun θ => hglobal θ θ.2

theorem prefixRate_positive_optimizer {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ}
    (hρ : ρ < 1) {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπk : 0 < π k)
    (hpos : 0 < prefixRate n ρ k π) :
    ∃ θ, 0 < θ ∧ prefixObjective n ρ k π θ = prefixRate n ρ k π ∧
      ∀ θ', 0 ≤ θ' → prefixObjective n ρ k π θ' ≤ prefixObjective n ρ k π θ := by
  obtain ⟨θ, hθ, hval, hmax⟩ := prefixRate_attained hk1 hk hρ hπ hπk
  refine ⟨θ, lt_of_le_of_ne hθ ?_, hval, hmax⟩
  rintro rfl
  rw [prefixObjective_zero hk] at hval
  linarith

theorem prefixRate_le_of_prefixMGF_le {n k : ℕ} {ρ : ℝ} {πA πB : ℕ → ℝ}
    (hbdd : BddAbove (Set.range fun θ : Set.Ici (0 : ℝ) => prefixObjective n ρ k πA θ))
    (hApos : ∀ θ, 0 ≤ θ → 0 < prefixMGF n k πA θ)
    (hle : ∀ θ, 0 ≤ θ → prefixMGF n k πA θ ≤ prefixMGF n k πB θ) :
    prefixRate n ρ k πB ≤ prefixRate n ρ k πA := by
  apply ciSup_le
  intro θ
  apply le_ciSup_of_le hbdd θ
  unfold prefixObjective
  have := Real.log_le_log (hApos θ θ.2) (hle θ θ.2)
  linarith

theorem prefixRate_lt_of_prefixMGF_lt {n k : ℕ} {ρ : ℝ} {πA πB : ℕ → ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hbdd : BddAbove (Set.range fun θ : Set.Ici (0 : ℝ) => prefixObjective n ρ k πA θ))
    (hApos : 0 < prefixMGF n k πA θ)
    (hopt : prefixObjective n ρ k πB θ = prefixRate n ρ k πB)
    (hlt : prefixMGF n k πA θ < prefixMGF n k πB θ) :
    prefixRate n ρ k πB < prefixRate n ρ k πA := by
  have h1 : prefixObjective n ρ k πA θ ≤ prefixRate n ρ k πA :=
    le_ciSup (f := fun θ : Set.Ici (0 : ℝ) => prefixObjective n ρ k πA θ) hbdd ⟨θ, hθ⟩
  have h2 := Real.log_lt_log hApos hlt
  rw [← hopt]
  unfold prefixObjective at h1 ⊢
  linarith

theorem sum_Icc_mul_eq_abel (d T : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Icc 1 k, d j * T j =
      (∑ j ∈ Icc 1 k, d j) * T k -
        ∑ j ∈ Ico 1 k, (∑ i ∈ Icc 1 j, d i) * (T (j + 1) - T j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Finset.sum_Ico_succ_top hk]
      ring

theorem prefixMGF_sub_summation_by_parts (n k : ℕ) (πA πB : ℕ → ℝ) (θ : ℝ) :
    prefixMGF n k πA θ - prefixMGF n k πB θ =
      (∑ j ∈ Icc 1 k, (πA j - πB j)) * contactGain n k k θ -
        ∑ j ∈ Ico 1 k, (∑ i ∈ Icc 1 j, (πA i - πB i)) *
          (contactGain n k (j + 1) θ - contactGain n k j θ) := by
  rw [← sum_Icc_mul_eq_abel (fun j => πA j - πB j) (fun j => contactGain n k j θ) k]
  unfold prefixMGF
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem prefixMGF_self_eq_fullMGF {n : ℕ} {h : ℝ} {π : ℕ → ℝ}
    (hmass : ∑ j ∈ Icc 1 n, π j = h) (θ : ℝ) : prefixMGF n n π θ = fullMGF n h π θ := by
  unfold prefixMGF fullMGF contactGain
  have : ∀ j ∈ Icc 1 n, π j * (hyperPGF n n j (Real.exp θ) - 1) =
      π j * Real.exp ((j : ℝ) * θ) - π j := by
    intro j hj
    rw [hyperPGF_self n j (mem_Icc.mp hj).2, ← Real.exp_nat_mul]
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hmass]
  ring

theorem prefixRate_self_eq_fullRate {n : ℕ} {ρ h : ℝ} {π : ℕ → ℝ}
    (hmass : ∑ j ∈ Icc 1 n, π j = h) : prefixRate n ρ n π = fullRate n ρ h π := by
  unfold prefixRate fullRate prefixObjective fullObjective
  simp only [prefixMGF_self_eq_fullMGF hmass]

theorem exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have hx := Real.exp_pos x
  have hm : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith

theorem prefixRate_self_pos {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Icc 1 n, 0 ≤ π j) (hπn : 0 < π n)
    (hmean : ∑ j ∈ Icc 1 n, (j : ℝ) * π j < (n : ℝ) * ρ) : 0 < prefixRate n ρ n π := by
  set m := ∑ j ∈ Icc 1 n, (j : ℝ) * π j with hm
  set β := (n : ℝ) * ρ with hβ
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun j hj => mul_nonneg (Nat.cast_nonneg _) (hπ j hj)
  have hβpos : 0 < β := lt_of_le_of_lt hm0 hmean
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set x := 1 + (β - m) / (2 * β) with hx
  have hx1 : 1 < x := by
    have : 0 < (β - m) / (2 * β) := div_pos (by linarith) (by linarith)
    linarith
  have hxm : m * x < β := by
    have h1 : m * ((β - m) / (2 * β)) ≤ (β - m) / 2 := by
      rw [mul_div_assoc']
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have : m * x = m + m * ((β - m) / (2 * β)) := by rw [hx]; ring
    linarith
  set θ := Real.log x / n with hθ
  have hθpos : 0 < θ := div_pos (Real.log_pos hx1) hnpos
  have hexpn : Real.exp ((n : ℝ) * θ) = x := by
    rw [hθ, mul_div_cancel₀ _ hnpos.ne', Real.exp_log (by linarith)]

  have hMle : prefixMGF n n π θ - 1 ≤ θ * x * m := by
    unfold prefixMGF
    rw [add_sub_cancel_left, hm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn := (mem_Icc.mp hj).2
    unfold contactGain
    rw [hyperPGF_self n j hjn, ← Real.exp_nat_mul]
    have h1 := exp_sub_one_le_mul_exp ((j : ℝ) * θ)
    have h2 : Real.exp ((j : ℝ) * θ) ≤ x := by
      rw [← hexpn]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjn) hθpos.le
    have hj0 : 0 ≤ (j : ℝ) * θ := mul_nonneg (Nat.cast_nonneg _) hθpos.le
    have h3 : Real.exp ((j : ℝ) * θ) - 1 ≤ (j : ℝ) * θ * x :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hj0)
    have := hπ j hj
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos (prefixMGF_pos (le_refl n) hπ hθpos.le)
  have hobj : 0 < prefixObjective n ρ n π θ := by
    unfold prefixObjective
    have : θ * x * m < β * θ := by nlinarith
    linarith
  exact lt_of_lt_of_le hobj (prefixObjective_le_prefixRate hn le_rfl hρ hπ hπn hθpos.le)

noncomputable def binaryKL (ρ q : ℝ) : ℝ :=
  ρ * Real.log (ρ / q) + (1 - ρ) * Real.log ((1 - ρ) / (1 - q))

theorem hyperPGF_one_one (n : ℕ) (hn : 1 ≤ n) (z : ℝ) : hyperPGF n 1 1 z = 1 + (z - 1) / n := by
  unfold hyperPGF hyperNum
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Nat.choose_one_right,
    Nat.choose_zero_right, Nat.choose_self, zero_add]
  have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_sub hn]
  field_simp
  ring

theorem prefixMGF_one (n : ℕ) (hn : 1 ≤ n) (π : ℕ → ℝ) (θ : ℝ) :
    prefixMGF n 1 π θ = 1 - π 1 / n + π 1 / n * Real.exp θ := by
  unfold prefixMGF contactGain
  simp only [Finset.Icc_self, Finset.sum_singleton]
  rw [hyperPGF_one_one n hn]
  ring

theorem binary_objective_le {ρ q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (θ : ℝ) : ρ * θ - Real.log (1 - q + q * Real.exp θ) ≤ binaryKL ρ q := by
  have hx : 0 < q * Real.exp θ / ρ := by positivity
  have h1q : 0 < 1 - q := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hy : 0 < (1 - q) / (1 - ρ) := div_pos h1q h1ρ
  have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy)
    hρ0.le h1ρ.le (by ring : ρ + (1 - ρ) = 1)
  simp only [smul_eq_mul] at hc
  have hsum : ρ * (q * Real.exp θ / ρ) + (1 - ρ) * ((1 - q) / (1 - ρ)) =
      1 - q + q * Real.exp θ := by
    field_simp
    ring
  rw [hsum, Real.log_div (by positivity) hρ0.ne', Real.log_mul hq0.ne' (Real.exp_pos θ).ne',
    Real.log_exp, Real.log_div h1q.ne' h1ρ.ne'] at hc
  unfold binaryKL
  rw [Real.log_div hρ0.ne' hq0.ne', Real.log_div h1ρ.ne' h1q.ne']
  linarith

noncomputable def binaryOptimizer (ρ q : ℝ) : ℝ := Real.log (ρ * (1 - q) / (q * (1 - ρ)))

theorem binary_objective_optimizer {ρ q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    ρ * binaryOptimizer ρ q - Real.log (1 - q + q * Real.exp (binaryOptimizer ρ q)) =
      binaryKL ρ q := by
  have h1q : 0 < 1 - q := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have ht : 0 < ρ * (1 - q) / (q * (1 - ρ)) := by positivity
  unfold binaryOptimizer
  rw [Real.exp_log ht]
  have hM : 1 - q + q * (ρ * (1 - q) / (q * (1 - ρ))) = (1 - q) / (1 - ρ) := by
    field_simp
    ring
  rw [hM, Real.log_div (by positivity) (by positivity), Real.log_mul hρ0.ne' h1q.ne',
    Real.log_mul hq0.ne' h1ρ.ne', Real.log_div h1q.ne' h1ρ.ne']
  unfold binaryKL
  rw [Real.log_div hρ0.ne' hq0.ne', Real.log_div h1ρ.ne' h1q.ne']
  ring

theorem binaryOptimizer_pos {ρ q : ℝ} (hq0 : 0 < q) (hqρ : q < ρ) (hρ1 : ρ < 1) :
    0 < binaryOptimizer ρ q := by
  unfold binaryOptimizer
  apply Real.log_pos
  rw [one_lt_div (mul_pos hq0 (by linarith))]
  nlinarith

theorem binaryKL_strictAntiOn {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    StrictAntiOn (binaryKL ρ) (Set.Ioo 0 ρ) := by
  intro q hq q' hq' hqq'
  have hq'1 : q' < 1 := by linarith [hq'.2]
  have hq1 : q < 1 := by linarith [hq.2]
  set θ := binaryOptimizer ρ q'
  have hθ : 0 < θ := binaryOptimizer_pos hq'.1 hq'.2 hρ1
  have hval := binary_objective_optimizer hq'.1 hq'1 hρ0 hρ1
  have hle := binary_objective_le hq.1 hq1 hρ0 hρ1 θ
  have he : 1 < Real.exp θ := Real.one_lt_exp_iff.mpr hθ
  have hMpos : 0 < 1 - q + q * Real.exp θ := by nlinarith [hq.1]
  have hMlt : 1 - q + q * Real.exp θ < 1 - q' + q' * Real.exp θ := by nlinarith
  have := Real.log_lt_log hMpos hMlt
  show binaryKL ρ q' < binaryKL ρ q
  linarith

theorem prefixRate_one_eq_binaryKL {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {π : ℕ → ℝ} (hπ1 : 0 < π 1) (hq : π 1 / n < ρ) :
    prefixRate n ρ 1 π = binaryKL ρ (π 1 / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq0 : 0 < π 1 / n := div_pos hπ1 hnpos
  have hq1 : π 1 / n < 1 := by linarith
  have hobj : ∀ θ, prefixObjective n ρ 1 π θ =
      ρ * θ - Real.log (1 - π 1 / n + π 1 / n * Real.exp θ) := by
    intro θ
    unfold prefixObjective
    rw [prefixMGF_one n hn]
    simp
  have hπ : ∀ j ∈ Icc 1 1, 0 ≤ π j := by
    intro j hj
    rw [Finset.Icc_self, Finset.mem_singleton] at hj
    rw [hj]
    exact hπ1.le
  apply le_antisymm
  · apply ciSup_le
    intro θ
    rw [hobj]
    exact binary_objective_le hq0 hq1 hρ0 hρ1 θ
  · have hθ := binaryOptimizer_pos hq0 hq hρ1
    have h := prefixObjective_le_prefixRate le_rfl hn hρ1.le hπ hπ1 hθ.le
    rw [hobj, binary_objective_optimizer hq0 hq1 hρ0 hρ1] at h
    exact h

theorem binaryKL_div_strictAntiOn {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    StrictAntiOn (fun x : ℝ => binaryKL ρ (x / n)) (Set.Ioo 0 ((n : ℝ) * ρ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  intro x hx y hy hxy
  have hmem : ∀ z ∈ Set.Ioo 0 ((n : ℝ) * ρ), z / n ∈ Set.Ioo 0 ρ := by
    intro z hz
    refine ⟨div_pos hz.1 hnpos, ?_⟩
    rw [div_lt_iff₀ hnpos]
    linarith [hz.2]
  exact binaryKL_strictAntiOn hρ0 hρ1 (hmem x hx) (hmem y hy)
    (div_lt_div_of_pos_right hxy hnpos)

structure IsRouteSolution (n : ℕ) (ρ h : ℝ) (π : ℕ → ℝ) : Prop where
  pos : ∀ j ∈ Icc 1 n, 0 < π j
  mass : ∑ j ∈ Icc 1 n, π j = h
  mean : ∑ j ∈ Icc 1 n, (j : ℝ) * π j < (n : ℝ) * ρ
  rate_eq : ∀ k ∈ Icc 1 n, prefixRate n ρ k π = fullRate n ρ h π

theorem isRouteSolution_iff {n : ℕ} {ρ h : ℝ} {π : ℕ → ℝ} :
    IsRouteSolution n ρ h π ↔
      (∀ j ∈ Icc 1 n, 0 < π j) ∧ ∑ j ∈ Icc 1 n, π j = h ∧
        ∑ j ∈ Icc 1 n, (j : ℝ) * π j < (n : ℝ) * ρ ∧
          ∀ k ∈ Icc 1 n, prefixRate n ρ k π = prefixRate n ρ n π := by
  constructor
  · intro hS
    refine ⟨hS.pos, hS.mass, hS.mean, fun k hk => ?_⟩
    rw [hS.rate_eq k hk, prefixRate_self_eq_fullRate hS.mass]
  · rintro ⟨hpos, hmass, hmean, hrate⟩
    refine ⟨hpos, hmass, hmean, fun k hk => ?_⟩
    rw [hrate k hk, prefixRate_self_eq_fullRate hmass]

namespace IsRouteSolution

variable {n : ℕ} {ρ h : ℝ} {π : ℕ → ℝ}

theorem one_le (hS : IsRouteSolution n ρ h π) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := hS.mean
    simp at this
  · exact hn

theorem nonneg_prefix (hS : IsRouteSolution n ρ h π) {k : ℕ} (hk : k ≤ n) :
    ∀ j ∈ Icc 1 k, 0 ≤ π j :=
  fun j hj => (hS.pos j (Finset.Icc_subset_Icc_right hk hj)).le

theorem rho_pos (hS : IsRouteSolution n ρ h π) : 0 < ρ := by
  have hn := hS.one_le
  have hm0 : 0 ≤ ∑ j ∈ Icc 1 n, (j : ℝ) * π j :=
    Finset.sum_nonneg fun j hj => mul_nonneg (Nat.cast_nonneg _) (hS.pos j hj).le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have := lt_of_le_of_lt hm0 hS.mean
  by_contra hρ
  push Not at hρ
  nlinarith

theorem fullRate_pos (hS : IsRouteSolution n ρ h π) (hρ : ρ ≤ 1) : 0 < fullRate n ρ h π := by
  have hn := hS.one_le
  rw [← prefixRate_self_eq_fullRate hS.mass]
  exact prefixRate_self_pos hn hρ (hS.nonneg_prefix le_rfl)
    (hS.pos n (mem_Icc.mpr ⟨hn, le_rfl⟩)) hS.mean

theorem positive_optimizer (hS : IsRouteSolution n ρ h π) (hρ : ρ < 1) {k : ℕ}
    (hk : k ∈ Icc 1 n) :
    ∃ θ, 0 < θ ∧ prefixObjective n ρ k π θ = prefixRate n ρ k π ∧
      ∀ θ', 0 ≤ θ' → prefixObjective n ρ k π θ' ≤ prefixObjective n ρ k π θ := by
  have hk' := mem_Icc.mp hk
  apply prefixRate_positive_optimizer hk'.1 hk'.2 hρ (hS.nonneg_prefix hk'.2) (hS.pos k hk)
  rw [hS.rate_eq k hk]
  exact hS.fullRate_pos hρ.le

theorem first_mass_lt (hS : IsRouteSolution n ρ h π) : π 1 / n < ρ := by
  have hn := hS.one_le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : (1 : ℝ) * π 1 ≤ ∑ j ∈ Icc 1 n, (j : ℝ) * π j := by
    have := Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) * π j)
      (fun j hj => mul_nonneg (Nat.cast_nonneg _) (hS.pos j hj).le)
      (mem_Icc.mpr ⟨le_rfl, hn⟩)
    simpa using this
  rw [div_lt_iff₀ hnpos]
  linarith [hS.mean]

theorem fullRate_eq_binaryKL (hS : IsRouteSolution n ρ h π) (hρ : ρ < 1) :
    fullRate n ρ h π = binaryKL ρ (π 1 / n) := by
  have hn := hS.one_le
  rw [← hS.rate_eq 1 (mem_Icc.mpr ⟨le_rfl, hn⟩)]
  exact prefixRate_one_eq_binaryKL hn hS.rho_pos hρ (hS.pos 1 (mem_Icc.mpr ⟨le_rfl, hn⟩))
    hS.first_mass_lt

theorem fullRate_le (hρ : ρ ≤ 1) {πA πB : ℕ → ℝ} (hA : IsRouteSolution n ρ h πA)
    (hB : IsRouteSolution n ρ h πB) : fullRate n ρ h πB ≤ fullRate n ρ h πA := by
  classical
  have hn := hA.one_le
  set D : ℕ → ℝ := fun k => ∑ j ∈ Icc 1 k, (πA j - πB j) with hD
  have hDn : D n = 0 := by
    simp only [hD, Finset.sum_sub_distrib, hA.mass, hB.mass, sub_self]
  have hex : ∃ k, 1 ≤ k ∧ D k ≤ 0 := ⟨n, hn, hDn.le⟩
  obtain ⟨k, ⟨hk1, hDk⟩, hmin⟩ : ∃ k, (1 ≤ k ∧ D k ≤ 0) ∧ ∀ j < k, ¬ (1 ≤ j ∧ D j ≤ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hkn : k ≤ n := by
    by_contra hkn
    exact hmin n (by omega) ⟨hn, hDn.le⟩
  have hkmem : k ∈ Icc 1 n := mem_Icc.mpr ⟨hk1, hkn⟩
  have hApos := hA.nonneg_prefix hkn
  have hle : ∀ θ, 0 ≤ θ → prefixMGF n k πA θ ≤ prefixMGF n k πB θ := by
    intro θ hθ
    have hsbp := prefixMGF_sub_summation_by_parts n k πA πB θ
    have hT := contactGain_nonneg n k k hkn hkn hθ
    have h1 : (∑ j ∈ Icc 1 k, (πA j - πB j)) * contactGain n k k θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hDk hT
    have h2 : 0 ≤ ∑ j ∈ Ico 1 k, (∑ i ∈ Icc 1 j, (πA i - πB i)) *
        (contactGain n k (j + 1) θ - contactGain n k j θ) := by
      apply Finset.sum_nonneg
      intro j hj
      have hj' := mem_Ico.mp hj
      have hDj : 0 < D j := by
        have := hmin j hj'.2
        push Not at this
        exact this hj'.1
      exact mul_nonneg hDj.le
        (sub_nonneg.mpr (contactGain_mono n k hkn hθ (Nat.le_succ j) (by omega)))
    linarith
  have hrate := prefixRate_le_of_prefixMGF_le
    (prefixObjective_bddAbove hk1 hkn hρ hApos (hA.pos k hkmem))
    (fun θ hθ => prefixMGF_pos hkn hApos hθ) hle
  rwa [hA.rate_eq k hkmem, hB.rate_eq k hkmem] at hrate

theorem fullRate_eq (hρ : ρ ≤ 1) {πA πB : ℕ → ℝ} (hA : IsRouteSolution n ρ h πA)
    (hB : IsRouteSolution n ρ h πB) : fullRate n ρ h πA = fullRate n ρ h πB :=
  le_antisymm (hB.fullRate_le hρ hA) (hA.fullRate_le hρ hB)

end IsRouteSolution

theorem prefixRate_lt_of_first_difference {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ}
    (hρ : ρ < 1) {πA πB : ℕ → ℝ} (hA : ∀ j ∈ Icc 1 k, 0 ≤ πA j)
    (hB : ∀ j ∈ Icc 1 k, 0 ≤ πB j) (hAk : 0 < πA k) (hBk : 0 < πB k)
    (hprefix : ∀ j ∈ Ico 1 k, πA j = πB j) (hlt : πA k < πB k)
    (hpos : 0 < prefixRate n ρ k πB) : prefixRate n ρ k πB < prefixRate n ρ k πA := by
  obtain ⟨θ, hθ, hval, -⟩ := prefixRate_positive_optimizer hk1 hk hρ hB hBk hpos
  apply prefixRate_lt_of_prefixMGF_lt hθ.le (prefixObjective_bddAbove hk1 hk hρ.le hA hAk)
    (prefixMGF_pos hk hA hθ.le) hval
  have hdiff : prefixMGF n k πA θ - prefixMGF n k πB θ =
      (πA k - πB k) * contactGain n k k θ := by
    unfold prefixMGF
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single_of_mem k (mem_Icc.mpr ⟨hk1, le_rfl⟩)]
    · ring
    · intro j hj hjk
      have hj' := mem_Icc.mp hj
      rw [hprefix j (mem_Ico.mpr ⟨hj'.1, lt_of_le_of_ne hj'.2 hjk⟩)]
      ring
  have hT := contactGain_pos n k k hk1 hk hk1 hk hθ
  nlinarith

theorem IsRouteSolution.unique {n : ℕ} {ρ h : ℝ} (hρ : ρ < 1) {πA πB : ℕ → ℝ}
    (hA : IsRouteSolution n ρ h πA) (hB : IsRouteSolution n ρ h πB) :
    ∀ j ∈ Icc 1 n, πA j = πB j := by
  classical
  have hJ := IsRouteSolution.fullRate_eq hρ.le hA hB
  by_contra hne
  push Not at hne
  obtain ⟨k, ⟨hkmem, hk⟩, hmin⟩ : ∃ k, (k ∈ Icc 1 n ∧ πA k ≠ πB k) ∧
      ∀ j < k, ¬ (j ∈ Icc 1 n ∧ πA j ≠ πB j) :=
    ⟨Nat.find hne, Nat.find_spec hne, fun j hj => Nat.find_min hne hj⟩
  have hk' := mem_Icc.mp hkmem
  have hprefix : ∀ j ∈ Ico 1 k, πA j = πB j := by
    intro j hj
    have hj' := mem_Ico.mp hj
    by_contra hne'
    exact hmin j hj'.2 ⟨mem_Icc.mpr ⟨hj'.1, by omega⟩, hne'⟩
  have hAn := hA.nonneg_prefix hk'.2
  have hBn := hB.nonneg_prefix hk'.2
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · have hpos : 0 < prefixRate n ρ k πB := by
      rw [hB.rate_eq k hkmem]
      exact hB.fullRate_pos hρ.le
    have := prefixRate_lt_of_first_difference hk'.1 hk'.2 hρ hAn hBn (hA.pos k hkmem)
      (hB.pos k hkmem) hprefix hlt hpos
    rw [hA.rate_eq k hkmem, hB.rate_eq k hkmem, hJ] at this
    exact lt_irrefl _ this
  · have hpos : 0 < prefixRate n ρ k πA := by
      rw [hA.rate_eq k hkmem]
      exact hA.fullRate_pos hρ.le
    have := prefixRate_lt_of_first_difference hk'.1 hk'.2 hρ hBn hAn (hB.pos k hkmem)
      (hA.pos k hkmem) (fun j hj => (hprefix j hj).symm) hgt hpos
    rw [hA.rate_eq k hkmem, hB.rate_eq k hkmem, hJ] at this
    exact lt_irrefl _ this

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Icc 1 n, f j = ∑ j ∈ range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem sum_Icc_choose (n : ℕ) : ∑ j ∈ Icc 1 n, (n.choose j : ℝ) = 2 ^ n - 1 := by
  rw [sum_Icc_one_eq_sum_range (fun j => (n.choose j : ℝ)), positive_choose_sum]

theorem upperBoundary_algebra {n : ℕ} (hn : 1 ≤ n) {h J : ℝ} (hh : 0 < h) {π : ℕ → ℝ}
    (hcoef : ∀ k ∈ Icc 1 n, π k / (n.choose k : ℝ) = Real.exp (-J))
    (hmass : ∑ k ∈ Icc 1 n, π k = h) :
    Real.exp (-J) = h / (2 ^ n - 1) ∧ J = Real.log ((2 ^ n - 1) / h) ∧
      (∀ k ∈ Icc 1 n, π k = boundaryMass n h k) ∧
      (∑ k ∈ Icc 1 n, (k : ℝ) * π k) / h = (n : ℝ) * 2 ^ (n - 1) / (2 ^ n - 1) := by
  have hden := boundary_denominator_pos n (by omega)
  have hπ : ∀ k ∈ Icc 1 n, π k = (n.choose k : ℝ) * Real.exp (-J) := by
    intro k hk
    have hC : (n.choose k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (mem_Icc.mp hk).2).ne'
    rw [← hcoef k hk]
    field_simp
  have hsum : h = (2 ^ n - 1) * Real.exp (-J) := by
    rw [← hmass, Finset.sum_congr rfl hπ, ← Finset.sum_mul, sum_Icc_choose]
  have he : Real.exp (-J) = h / (2 ^ n - 1) := by
    rw [hsum]
    field_simp
  have hmassk : ∀ k ∈ Icc 1 n, π k = boundaryMass n h k := by
    intro k hk
    rw [hπ k hk, he, boundaryMass]
    ring
  refine ⟨he, ?_, hmassk, ?_⟩
  · have := congrArg Real.log he
    rw [Real.log_exp] at this
    rw [← inv_div, Real.log_inv, ← this, neg_neg]
  · rw [Finset.sum_congr rfl (fun k hk => by rw [hmassk k hk]),
      sum_Icc_one_eq_sum_range (fun k => (k : ℝ) * boundaryMass n h k)]
    have := boundaryMass_load n h
    push_cast at this ⊢
    rw [this]
    field_simp

theorem binomial_half_toReal (n : ℕ) (k : Fin (n + 1)) :
    (ProbabilityTheory.binomial n ⟨1 / 2, by norm_num⟩).real {k.val} =
      (n.choose k : ℝ) / 2 ^ n := by
  rw [ProbabilityTheory.binomial_real_singleton]
  change (n.choose k : ℝ) * (1 / 2 : ℝ) ^ k.val * (1 - 1 / 2 : ℝ) ^ (n - k.val) = _
  have hk : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hk]
  simp only [div_eq_mul_inv, one_mul, inv_pow]

theorem boundaryMass_conditional_binomial {n : ℕ} (hn : 1 ≤ n) {h : ℝ} (hh : 0 < h) (k : ℕ)
    (hk : k ∈ Icc 1 n) :
    boundaryMass n h k / h =
      (ProbabilityTheory.binomial n ⟨1 / 2, by norm_num⟩).real {k} /
        (1 - (ProbabilityTheory.binomial n ⟨1 / 2, by norm_num⟩).real {0}) := by
  have hK : (ProbabilityTheory.binomial n ⟨1 / 2, by norm_num⟩).real {k} =
      (n.choose k : ℝ) / 2 ^ n :=
    binomial_half_toReal n ⟨k, Nat.lt_succ_of_le (mem_Icc.mp hk).2⟩
  have h0 : (ProbabilityTheory.binomial n ⟨1 / 2, by norm_num⟩).real {0} = 1 / 2 ^ n := by
    simpa using binomial_half_toReal n 0
  rw [hK, h0]
  have hden := boundary_denominator_pos n (by omega)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  unfold boundaryMass
  have : (1 : ℝ) - 1 / 2 ^ n = (2 ^ n - 1) / 2 ^ n := by field_simp
  rw [this]
  field_simp

noncomputable def vandNum (k m j : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ antidiagonal j, (k.choose p.1 : ℝ) * (m.choose p.2 : ℝ) * z ^ p.1

theorem hyperNum_eq_vandNum (n k j : ℕ) (z : ℝ) : hyperNum n k j z = vandNum k (n - k) j z :=
  rfl

theorem vandNum_zero (k m : ℕ) (z : ℝ) : vandNum k m 0 z = 1 := by
  simp [vandNum]

theorem vandNum_pascal (k m j : ℕ) (z : ℝ) :
    vandNum k (m + 1) (j + 1) z = vandNum k m (j + 1) z + vandNum k m j z := by
  unfold vandNum
  have h1 : (∑ p ∈ antidiagonal (j + 1), (k.choose p.1 : ℝ) * ((m + 1).choose p.2 : ℝ) *
      z ^ p.1) = (k.choose (j + 1) : ℝ) * z ^ (j + 1) +
        ∑ p ∈ antidiagonal j, (k.choose p.1 : ℝ) * ((m + 1).choose (p.2 + 1) : ℝ) * z ^ p.1 := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp
  have h2 : (∑ p ∈ antidiagonal (j + 1), (k.choose p.1 : ℝ) * (m.choose p.2 : ℝ) * z ^ p.1) =
      (k.choose (j + 1) : ℝ) * z ^ (j + 1) +
        ∑ p ∈ antidiagonal j, (k.choose p.1 : ℝ) * (m.choose (p.2 + 1) : ℝ) * z ^ p.1 := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp
  rw [h1, h2, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.choose_succ_succ']
  push_cast
  ring

theorem exp_mix_le {u v x y : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 < u + v) :
    (u + v) * Real.exp ((u * x + v * y) / (u + v)) ≤ u * Real.exp x + v * Real.exp y := by
  have h := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) (div_nonneg hu hs.le)
    (div_nonneg hv hs.le) (by field_simp)
  simp only [smul_eq_mul] at h
  have e : u / (u + v) * x + v / (u + v) * y = (u * x + v * y) / (u + v) := by
    field_simp
  rw [e] at h
  calc (u + v) * Real.exp ((u * x + v * y) / (u + v))
      ≤ (u + v) * (u / (u + v) * Real.exp x + v / (u + v) * Real.exp y) :=
        mul_le_mul_of_nonneg_left h hs.le
    _ = u * Real.exp x + v * Real.exp y := by field_simp

theorem exp_mix_lt {u v x y : ℝ} (hu : 0 < u) (hv : 0 < v) (hxy : x ≠ y) :
    (u + v) * Real.exp ((u * x + v * y) / (u + v)) < u * Real.exp x + v * Real.exp y := by
  have hs : 0 < u + v := by linarith
  have h := strictConvexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) hxy (div_pos hu hs)
    (div_pos hv hs) (by field_simp)
  simp only [smul_eq_mul] at h
  have e : u / (u + v) * x + v / (u + v) * y = (u * x + v * y) / (u + v) := by
    field_simp
  rw [e] at h
  calc (u + v) * Real.exp ((u * x + v * y) / (u + v))
      < (u + v) * (u / (u + v) * Real.exp x + v / (u + v) * Real.exp y) :=
        mul_lt_mul_of_pos_left h hs
    _ = u * Real.exp x + v * Real.exp y := by field_simp

theorem mix_exponent (k a : ℕ) (ha : a ≤ k) (θ : ℝ) :
    ((k.choose a : ℝ) * ((a : ℝ) * θ) + (k.choose (a + 1) : ℝ) * (((a : ℝ) + 1) * θ)) /
        ((k.choose a : ℝ) + (k.choose (a + 1) : ℝ)) = ((a : ℝ) + 1) * (θ * k / (k + 1)) := by
  have hu : (0 : ℝ) < (k.choose a : ℝ) := by exact_mod_cast Nat.choose_pos ha
  have hv : (0 : ℝ) ≤ (k.choose (a + 1) : ℝ) := Nat.cast_nonneg _
  have hr1 := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_succ_right_eq k a)
  push_cast [Nat.cast_sub ha] at hr1
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [div_eq_iff (by linarith)]
  field_simp
  linear_combination θ * hr1

theorem choose_exp_mix_le (k a : ℕ) (θ : ℝ) :
    ((k + 1).choose (a + 1) : ℝ) * Real.exp (θ * k / (k + 1)) ^ (a + 1) ≤
      (k.choose a : ℝ) * Real.exp θ ^ a + (k.choose (a + 1) : ℝ) * Real.exp θ ^ (a + 1) := by
  by_cases ha : a ≤ k
  · have hu : (0 : ℝ) < (k.choose a : ℝ) := by exact_mod_cast Nat.choose_pos ha
    have hv : (0 : ℝ) ≤ (k.choose (a + 1) : ℝ) := Nat.cast_nonneg _
    rw [Nat.choose_succ_succ', Nat.cast_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      ← Real.exp_nat_mul]
    push_cast
    rw [← mix_exponent k a ha θ]
    exact exp_mix_le hu.le hv (by linarith)
  · have h1 : k.choose a = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : k.choose (a + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h3 : (k + 1).choose (a + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2, h3]

theorem choose_exp_mix_lt (k a : ℕ) (ha : a < k) {θ : ℝ} (hθ : θ ≠ 0) :
    ((k + 1).choose (a + 1) : ℝ) * Real.exp (θ * k / (k + 1)) ^ (a + 1) <
      (k.choose a : ℝ) * Real.exp θ ^ a + (k.choose (a + 1) : ℝ) * Real.exp θ ^ (a + 1) := by
  have hu : (0 : ℝ) < (k.choose a : ℝ) := by exact_mod_cast Nat.choose_pos ha.le
  have hv : (0 : ℝ) < (k.choose (a + 1) : ℝ) := by exact_mod_cast Nat.choose_pos ha
  rw [Nat.choose_succ_succ', Nat.cast_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul]
  push_cast
  rw [← mix_exponent k a ha.le θ]
  apply exp_mix_lt hu hv
  intro h
  apply hθ
  nlinarith

theorem vandNum_mix_le (k m j : ℕ) (θ : ℝ) :
    vandNum (k + 1) m (j + 1) (Real.exp (θ * k / (k + 1))) ≤
      vandNum k m (j + 1) (Real.exp θ) + vandNum k m j (Real.exp θ) := by
  unfold vandNum
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul]
  rw [add_assoc, ← Finset.sum_add_distrib]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro p _
  have hc : (0 : ℝ) ≤ (m.choose p.2 : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left (choose_exp_mix_le k p.1 θ) hc
  linarith

theorem vandNum_mix_lt_one (k m : ℕ) (hk : 1 ≤ k) {θ : ℝ} (hθ : θ ≠ 0) :
    vandNum (k + 1) m 1 (Real.exp (θ * k / (k + 1))) <
      vandNum k m 1 (Real.exp θ) + vandNum k m 0 (Real.exp θ) := by
  unfold vandNum
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, zero_add]
  have h := choose_exp_mix_lt k 0 (by omega) hθ
  simp only [zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    one_mul] at h
  linarith

theorem hyperPGF_added_le (n k j : ℕ) (hk : k + 1 ≤ n) (θ : ℝ) :
    hyperPGF n (k + 1) j (Real.exp (θ * k / (k + 1))) ≤ hyperPGF n k j (Real.exp θ) := by
  unfold hyperPGF
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [hyperNum_eq_vandNum, hyperNum_eq_vandNum, show n - k = n - (k + 1) + 1 by omega]
  rcases j with _ | j
  · simp [vandNum_zero]
  · rw [vandNum_pascal]
    exact vandNum_mix_le k (n - (k + 1)) j θ

theorem hyperPGF_added_lt_one (n k : ℕ) (hk1 : 1 ≤ k) (hk : k + 1 ≤ n) {θ : ℝ} (hθ : θ ≠ 0) :
    hyperPGF n (k + 1) 1 (Real.exp (θ * k / (k + 1))) < hyperPGF n k 1 (Real.exp θ) := by
  unfold hyperPGF
  have hC : (0 : ℝ) < (n.choose 1 : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  apply div_lt_div_of_pos_right _ hC
  rw [hyperNum_eq_vandNum, hyperNum_eq_vandNum, show n - k = n - (k + 1) + 1 by omega,
    vandNum_pascal]
  exact vandNum_mix_lt_one k (n - (k + 1)) hk1 hθ

theorem prefixMGF_succ (n k : ℕ) (π : ℕ → ℝ) (θ : ℝ) :
    prefixMGF n (k + 1) π θ =
      1 + ∑ j ∈ Icc 1 k, π j * contactGain n (k + 1) j θ +
        π (k + 1) * contactGain n (k + 1) (k + 1) θ := by
  unfold prefixMGF
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

theorem prefixMGF_added_lt {n k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ n) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπ1 : 0 < π 1) {θ : ℝ} (hθ : 0 < θ) :
    prefixMGF n (k + 1) (Function.update π (k + 1) 0) (θ * k / (k + 1)) <
      prefixMGF n k π θ := by
  rw [prefixMGF_succ, Function.update_self, zero_mul, add_zero]
  unfold prefixMGF
  apply add_lt_add_of_le_of_lt le_rfl
  have hupd : ∀ j ∈ Icc 1 k, Function.update π (k + 1) 0 j = π j := by
    intro j hj
    rw [Function.update_of_ne (by have := (mem_Icc.mp hj).2; omega)]
  rw [Finset.sum_congr rfl (fun j hj => by rw [hupd j hj])]
  apply Finset.sum_lt_sum
  · intro j hj
    apply mul_le_mul_of_nonneg_left _ (hπ j hj)
    unfold contactGain
    linarith [hyperPGF_added_le n k j hk θ]
  · refine ⟨1, mem_Icc.mpr ⟨le_rfl, hk1⟩, ?_⟩
    apply mul_lt_mul_of_pos_left _ hπ1
    unfold contactGain
    linarith [hyperPGF_added_lt_one n k hk1 hk hθ.ne']

theorem added_constraint_objective_gt {n k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ n) {ρ : ℝ}
    (hρ : ρ < 1) {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπ1 : 0 < π 1) (hπk : 0 < π k)
    (hpos : 0 < prefixRate n ρ k π) :
    ∃ θ, 0 ≤ θ ∧
      prefixRate n ρ k π < prefixObjective n ρ (k + 1) (Function.update π (k + 1) 0) θ := by
  obtain ⟨θ, hθ, hval, -⟩ := prefixRate_positive_optimizer hk1 (by omega) hρ hπ hπk hpos
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine ⟨θ * k / (k + 1), div_nonneg (mul_nonneg hθ.le (Nat.cast_nonneg _)) hkpos.le, ?_⟩
  have hnon : ∀ j ∈ Icc 1 (k + 1), 0 ≤ Function.update π (k + 1) 0 j := by
    intro j hj
    by_cases hjk : j = k + 1
    · rw [hjk, Function.update_self]
    · rw [Function.update_of_ne hjk]
      exact hπ j (mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩)
  have hMpos := prefixMGF_pos hk hnon
    (div_nonneg (mul_nonneg hθ.le (Nat.cast_nonneg k)) hkpos.le)
  have hlt := Real.log_lt_log hMpos (prefixMGF_added_lt hk1 hk hπ hπ1 hθ)
  rw [← hval]
  unfold prefixObjective
  have hlin : ((k + 1 : ℕ) : ℝ) * ρ * (θ * k / (k + 1)) = (k : ℝ) * ρ * θ := by
    push_cast
    field_simp
  rw [hlin]
  linarith

noncomputable def rivalMGF (n k : ℕ) (rival : ℕ → ℝ) (θ : ℝ) : ℝ :=
  1 + ∑ j ∈ Icc 1 n, rival j * contactGain n k j θ

noncomputable def rivalObjective (n : ℕ) (ρ : ℝ) (k : ℕ) (rival : ℕ → ℝ) (θ : ℝ) : ℝ :=
  (k : ℝ) * ρ * θ - Real.log (rivalMGF n k rival θ)

noncomputable def rivalRate (n : ℕ) (ρ : ℝ) (k : ℕ) (rival : ℕ → ℝ) : ℝ :=
  ⨆ θ : Set.Ici (0 : ℝ), rivalObjective n ρ k rival θ

theorem prefixMGF_eq_rivalMGF {n k : ℕ} (hk : k ≤ n) (π : ℕ → ℝ) (θ : ℝ) :
    prefixMGF n k π θ = rivalMGF n k (fun j => if j ≤ k then π j else 0) θ := by
  unfold prefixMGF rivalMGF
  congr 1
  have hfilt : (Icc 1 n).filter (fun j => j ≤ k) = Icc 1 k := by
    ext j
    simp only [mem_filter, mem_Icc]
    omega
  rw [← hfilt, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ≤ k
  · simp only [hj, if_true]
  · simp only [hj, if_false, zero_mul]

theorem prefixRate_eq_rivalRate {n k : ℕ} (hk : k ≤ n) (ρ : ℝ) (π : ℕ → ℝ) :
    prefixRate n ρ k π = rivalRate n ρ k (fun j => if j ≤ k then π j else 0) := by
  unfold prefixRate rivalRate prefixObjective rivalObjective
  simp_rw [prefixMGF_eq_rivalMGF hk π]

theorem one_le_rivalMGF {n k : ℕ} (hk : k ≤ n) {rival : ℕ → ℝ}
    (hr : ∀ j ∈ Icc 1 n, 0 ≤ rival j) {θ : ℝ} (hθ : 0 ≤ θ) : 1 ≤ rivalMGF n k rival θ := by
  unfold rivalMGF
  have : 0 ≤ ∑ j ∈ Icc 1 n, rival j * contactGain n k j θ :=
    Finset.sum_nonneg fun j hj =>
      mul_nonneg (hr j hj) (contactGain_nonneg n k j hk (mem_Icc.mp hj).2 hθ)
  linarith

theorem rivalObjective_zero {n k : ℕ} (hk : k ≤ n) (ρ : ℝ) (rival : ℕ → ℝ) :
    rivalObjective n ρ k rival 0 = 0 := by
  unfold rivalObjective rivalMGF
  rw [Finset.sum_eq_zero (fun j hj => by
    rw [contactGain_zero n k j hk (mem_Icc.mp hj).2, mul_zero])]
  simp

theorem rivalMGF_added_lt {n k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ n) {rival : ℕ → ℝ}
    (hr : ∀ j ∈ Icc 1 n, 0 ≤ rival j) (hr1 : 0 < rival 1) {θ : ℝ} (hθ : 0 < θ) :
    rivalMGF n (k + 1) rival (θ * k / (k + 1)) < rivalMGF n k rival θ := by
  unfold rivalMGF
  apply add_lt_add_of_le_of_lt le_rfl
  apply Finset.sum_lt_sum
  · intro j hj
    apply mul_le_mul_of_nonneg_left _ (hr j hj)
    unfold contactGain
    linarith [hyperPGF_added_le n k j hk θ]
  · refine ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
    apply mul_lt_mul_of_pos_left _ hr1
    unfold contactGain
    linarith [hyperPGF_added_lt_one n k hk1 hk hθ.ne']

theorem rival_added_constraint_gt {n k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ n) (ρ : ℝ)
    {rival : ℕ → ℝ} (hr : ∀ j ∈ Icc 1 n, 0 ≤ rival j) (hr1 : 0 < rival 1) {θ : ℝ}
    (hθ : 0 ≤ θ) (hopt : rivalObjective n ρ k rival θ = rivalRate n ρ k rival)
    (hpos : 0 < rivalRate n ρ k rival) :
    ∃ θ', 0 ≤ θ' ∧ rivalRate n ρ k rival < rivalObjective n ρ (k + 1) rival θ' := by
  have hθpos : 0 < θ := by
    rcases lt_or_eq_of_le hθ with h | h
    · exact h
    · rw [← h, rivalObjective_zero (by omega)] at hopt
      linarith
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hφ : 0 ≤ θ * k / (k + 1) := div_nonneg (mul_nonneg hθ (Nat.cast_nonneg k)) hkpos.le
  refine ⟨θ * k / (k + 1), hφ, ?_⟩
  have hMpos : 0 < rivalMGF n (k + 1) rival (θ * k / (k + 1)) :=
    lt_of_lt_of_le one_pos (one_le_rivalMGF hk hr hφ)
  have hlt := Real.log_lt_log hMpos (rivalMGF_added_lt hk1 hk hr hr1 hθpos)
  rw [← hopt]
  unfold rivalObjective
  have hlin : ((k + 1 : ℕ) : ℝ) * ρ * (θ * k / (k + 1)) = (k : ℝ) * ρ * θ := by
    push_cast
    field_simp
  rw [hlin]
  linarith

theorem continuous_contactGain (n k j : ℕ) : Continuous (contactGain n k j) := by
  unfold contactGain hyperPGF hyperNum
  fun_prop

noncomputable def rateRadius (n : ℕ) (ρ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  max 0 (Real.log ((n.choose k : ℝ) / min 1 x) / ((k : ℝ) * (1 - ρ)))

theorem rateRadius_anti {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ < 1) {x0 x : ℝ}
    (hx0 : 0 < x0) (hx : x0 ≤ x) : rateRadius n ρ k x ≤ rateRadius n ρ k x0 := by
  have hC : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hkr : 0 < (k : ℝ) * (1 - ρ) :=
    mul_pos (by exact_mod_cast (show 0 < k by omega)) (by linarith)
  unfold rateRadius
  apply max_le_max le_rfl
  apply div_le_div_of_nonneg_right _ hkr.le
  apply Real.log_le_log (div_pos hC (lt_min one_pos (by linarith)))
  exact div_le_div_of_nonneg_left hC.le (lt_min one_pos hx0) (min_le_min le_rfl hx)

theorem prefixRate_eq_sSup_Icc {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ < 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) (hπk : 0 < π k) {R : ℝ}
    (hR : rateRadius n ρ k (π k) ≤ R) :
    prefixRate n ρ k π = sSup (prefixObjective n ρ k π '' Set.Icc 0 R) := by
  have hR0 : 0 ≤ R := le_trans (le_max_left _ _) hR
  have hbdd := prefixObjective_bddAbove hk1 hk hρ.le hπ hπk
  have hsbdd : BddAbove (prefixObjective n ρ k π '' Set.Icc 0 R) := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B, ?_⟩
    rintro _ ⟨θ, hθ, rfl⟩
    exact hB ⟨⟨θ, hθ.1⟩, rfl⟩
  have hne : (prefixObjective n ρ k π '' Set.Icc 0 R).Nonempty :=
    ⟨_, 0, ⟨le_rfl, hR0⟩, rfl⟩
  have hkr : 0 < (k : ℝ) * (1 - ρ) :=
    mul_pos (by exact_mod_cast (show 0 < k by omega)) (by linarith)
  apply le_antisymm
  · apply ciSup_le
    intro θ
    by_cases hθR : (θ : ℝ) ≤ R
    · exact le_csSup hsbdd ⟨θ, ⟨θ.2, hθR⟩, rfl⟩
    · have h1 := prefixObjective_le_of_leading hk1 hk (ρ := ρ) hπ hπk θ.2
      have h2 : Real.log ((n.choose k : ℝ) / min 1 (π k)) ≤ (k : ℝ) * (1 - ρ) * θ := by
        have h3 : Real.log ((n.choose k : ℝ) / min 1 (π k)) / ((k : ℝ) * (1 - ρ)) < θ :=
          lt_of_le_of_lt (le_trans (le_max_right _ _) hR) (not_le.mp hθR)
        rw [div_lt_iff₀ hkr] at h3
        linarith
      have h0 : prefixObjective n ρ k π 0 ≤ sSup (prefixObjective n ρ k π '' Set.Icc 0 R) :=
        le_csSup hsbdd ⟨0, ⟨le_rfl, hR0⟩, rfl⟩
      rw [prefixObjective_zero hk] at h0
      linarith
  · apply csSup_le hne
    rintro _ ⟨θ, hθ, rfl⟩
    exact prefixObjective_le_prefixRate hk1 hk hρ.le hπ hπk hθ.1

theorem continuous_prefixRate_comp {γ : Type*} [TopologicalSpace γ] {n k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ n) {ρ : ℝ} (hρ : ρ < 1) (p : γ → ℕ → ℝ)
    (hcont : ∀ j ∈ Icc 1 k, Continuous fun g => p g j)
    (hnonneg : ∀ g, ∀ j ∈ Icc 1 k, 0 ≤ p g j) {x0 : ℝ} (hx0 : 0 < x0)
    (hlow : ∀ g, x0 ≤ p g k) : Continuous fun g => prefixRate n ρ k (p g) := by
  set R := rateRadius n ρ k x0
  let F : γ → ℝ → ℝ := fun g θ => (k : ℝ) * ρ * θ - Real.log (max 1 (prefixMGF n k (p g) θ))
  have heq : (fun g => prefixRate n ρ k (p g)) = fun g => sSup (F g '' Set.Icc 0 R) := by
    funext g
    rw [prefixRate_eq_sSup_Icc hk1 hk hρ (hnonneg g) (lt_of_lt_of_le hx0 (hlow g))
      (rateRadius_anti hk1 hk hρ hx0 (hlow g))]
    congr 1
    apply Set.image_congr
    intro θ hθ
    simp only [F, prefixObjective]
    rw [max_eq_right (one_le_prefixMGF hk (hnonneg g) hθ.1)]
  rw [heq]
  apply IsCompact.continuous_sSup isCompact_Icc
  have hM : Continuous fun q : γ × ℝ => prefixMGF n k (p q.1) q.2 := by
    unfold prefixMGF
    apply continuous_const.add
    apply continuous_finsetSum
    intro j hj
    exact ((hcont j hj).comp continuous_fst).mul
      ((continuous_contactGain n k j).comp continuous_snd)
  have hlog : Continuous fun q : γ × ℝ => Real.log (max 1 (prefixMGF n k (p q.1) q.2)) :=
    (continuous_const.max hM).log (fun q => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')
  exact (continuous_const.mul continuous_snd).sub hlog

theorem prefixMGF_congr {n k : ℕ} {π π' : ℕ → ℝ} (h : ∀ j ∈ Icc 1 k, π j = π' j) (θ : ℝ) :
    prefixMGF n k π θ = prefixMGF n k π' θ := by
  unfold prefixMGF
  rw [Finset.sum_congr rfl (fun j hj => by rw [h j hj])]

theorem prefixRate_congr {n : ℕ} {ρ : ℝ} {k : ℕ} {π π' : ℕ → ℝ}
    (h : ∀ j ∈ Icc 1 k, π j = π' j) : prefixRate n ρ k π = prefixRate n ρ k π' := by
  unfold prefixRate prefixObjective
  simp_rw [prefixMGF_congr h]

theorem update_nonneg {k : ℕ} {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {x : ℝ} (hx : 0 ≤ x) :
    ∀ j ∈ Icc 1 k, 0 ≤ Function.update π k x j := by
  intro j hj
  by_cases hjk : j = k
  · rw [hjk, Function.update_self]
    exact hx
  · rw [Function.update_of_ne hjk]
    have := mem_Icc.mp hj
    exact hπ j (mem_Ico.mpr ⟨this.1, lt_of_le_of_ne this.2 hjk⟩)

theorem prefixMGF_update {n k : ℕ} (hk1 : 1 ≤ k) (π : ℕ → ℝ) (x θ : ℝ) :
    prefixMGF n k (Function.update π k x) θ =
      prefixMGF n k (Function.update π k 0) θ + x * contactGain n k k θ := by
  classical
  have hmem : k ∈ Icc 1 k := mem_Icc.mpr ⟨hk1, le_rfl⟩
  unfold prefixMGF
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem, Function.update_self,
    Function.update_self]
  have : ∀ j ∈ (Icc 1 k).erase k, Function.update π k x j * contactGain n k j θ =
      Function.update π k 0 j * contactGain n k j θ := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj),
      Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Finset.sum_congr rfl this]
  ring

theorem contactGain_self_ge (n k : ℕ) (hk : k ≤ n) {θ : ℝ} (hθ : 0 ≤ θ) :
    (Real.exp ((k : ℝ) * θ) - 1) / (n.choose k : ℝ) ≤ contactGain n k k θ := by
  have hC : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hz : 1 ≤ Real.exp θ := Real.one_le_exp hθ
  have hdiff : hyperNum n k k (Real.exp θ) - (n.choose k : ℝ) =
      ∑ p ∈ antidiagonal k, (k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) *
        (Real.exp θ ^ p.1 - 1) := by
    rw [← hyperNum_one n k k hk]
    unfold hyperNum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hle : Real.exp θ ^ k - 1 ≤ hyperNum n k k (Real.exp θ) - (n.choose k : ℝ) := by
    rw [hdiff]
    have h := Finset.single_le_sum (f := fun p : ℕ × ℕ =>
      (k.choose p.1 : ℝ) * ((n - k).choose p.2 : ℝ) * (Real.exp θ ^ p.1 - 1))
      (fun p _ => mul_nonneg (by positivity) (sub_nonneg.mpr (one_le_pow₀ hz)))
      (show (k, 0) ∈ antidiagonal k by simp)
    simpa using h
  unfold contactGain hyperPGF
  rw [Real.exp_nat_mul, div_sub_one hC.ne']
  exact div_le_div_of_nonneg_right hle hC.le

theorem prefixMGF_ge_new_term {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) {θ : ℝ} (hθ : 0 ≤ θ) :
    1 + π k * contactGain n k k θ ≤ prefixMGF n k π θ := by
  unfold prefixMGF
  have h := Finset.single_le_sum (f := fun j => π j * contactGain n k j θ)
    (fun j hj => mul_nonneg (hπ j hj)
      (contactGain_nonneg n k j hk (by have := mem_Icc.mp hj; omega) hθ))
    (mem_Icc.mpr ⟨hk1, le_rfl⟩)
  linarith

theorem prefixRate_update_le_zero {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {x : ℝ} (hx : (n.choose k : ℝ) ≤ x) :
    prefixRate n ρ k (Function.update π k x) ≤ 0 := by
  have hC : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  apply ciSup_le
  intro θ
  have hθ := θ.2
  have hnon := update_nonneg hπ (le_trans hC.le hx)
  have h1 := prefixMGF_ge_new_term hk1 hk hnon hθ
  rw [Function.update_self] at h1
  have h2 := contactGain_self_ge n k hk hθ
  have hT := contactGain_nonneg n k k hk hk hθ
  have h3 : (n.choose k : ℝ) * contactGain n k k θ ≥ Real.exp ((k : ℝ) * θ) - 1 := by
    rw [div_le_iff₀ hC] at h2
    linarith
  have h4 : Real.exp ((k : ℝ) * θ) ≤ prefixMGF n k (Function.update π k x) θ := by
    nlinarith
  have h5 := Real.log_le_log (Real.exp_pos _) h4
  rw [Real.log_exp] at h5
  have h6 : (k : ℝ) * ρ * θ ≤ (k : ℝ) * θ := by
    have : 0 ≤ (k : ℝ) * θ := mul_nonneg (Nat.cast_nonneg _) hθ
    nlinarith
  unfold prefixObjective
  linarith

theorem prefixRate_update_le_binaryKL {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {ε : ℝ}
    (hε : 0 < ε) (hεC : ε / (n.choose k : ℝ) < 1) :
    prefixRate n ρ k (Function.update π k ε) ≤ binaryKL ρ (ε / (n.choose k : ℝ)) := by
  have hC : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  set q := ε / (n.choose k : ℝ) with hq
  have hq0 : 0 < q := div_pos hε hC
  apply ciSup_le
  intro θ
  have hθ := θ.2
  have hnon := update_nonneg hπ hε.le
  have h1 := prefixMGF_ge_new_term hk1 hk hnon hθ
  rw [Function.update_self] at h1
  have h2 := contactGain_self_ge n k hk hθ
  have h3 : 1 - q + q * Real.exp ((k : ℝ) * θ) ≤ prefixMGF n k (Function.update π k ε) θ := by
    have : q * (Real.exp ((k : ℝ) * θ) - 1) ≤ ε * contactGain n k k θ := by
      rw [hq, div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h2 hε.le
    linarith
  have hpos : 0 < 1 - q + q * Real.exp ((k : ℝ) * θ) := by
    have := Real.exp_pos ((k : ℝ) * θ)
    nlinarith
  have h4 := Real.log_le_log hpos h3
  have h5 := binary_objective_le hq0 hεC hρ0 hρ1 ((k : ℝ) * θ)
  unfold prefixObjective
  have : (k : ℝ) * ρ * θ = ρ * ((k : ℝ) * θ) := by ring
  linarith

theorem prefixRate_update_anti {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    prefixRate n ρ k (Function.update π k y) ≤ prefixRate n ρ k (Function.update π k x) := by
  have hnon := update_nonneg hπ hx.le
  apply prefixRate_le_of_prefixMGF_le
    (prefixObjective_bddAbove hk1 hk hρ hnon (by rw [Function.update_self]; exact hx))
    (fun θ hθ => prefixMGF_pos hk hnon hθ)
  intro θ hθ
  rw [prefixMGF_update hk1 π x, prefixMGF_update hk1 π y]
  have := contactGain_nonneg n k k hk hk hθ
  nlinarith

theorem prefixRate_update_strictAnti {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ}
    (hρ : ρ < 1) {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {x y : ℝ} (hx : 0 < x)
    (hxy : x < y) (hpos : 0 < prefixRate n ρ k (Function.update π k y)) :
    prefixRate n ρ k (Function.update π k y) < prefixRate n ρ k (Function.update π k x) := by
  apply prefixRate_lt_of_first_difference hk1 hk hρ (update_nonneg hπ hx.le)
    (update_nonneg hπ (by linarith)) (by rw [Function.update_self]; exact hx)
    (by rw [Function.update_self]; linarith) _ (by
      rw [Function.update_self, Function.update_self]; exact hxy) hpos
  intro j hj
  have hjk : j ≠ k := (mem_Ico.mp hj).2.ne
  rw [Function.update_of_ne hjk, Function.update_of_ne hjk]

theorem continuousOn_prefixRate_update {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ}
    (hρ : ρ < 1) {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {x0 : ℝ} (hx0 : 0 < x0) :
    ContinuousOn (fun x => prefixRate n ρ k (Function.update π k x)) (Set.Ici x0) := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_prefixRate_comp hk1 hk hρ (fun g : Set.Ici x0 => Function.update π k g.1)
    _ _ hx0
  · intro g
    rw [Function.update_self]
    exact g.2
  · intro j _
    by_cases hjk : j = k
    · subst hjk
      simp only [Function.update_self]
      exact continuous_subtype_val
    · simp only [Function.update_of_ne hjk]
      exact continuous_const
  · intro g
    exact update_nonneg hπ (le_trans hx0.le g.2)

open Classical in

noncomputable def stepRoot (n : ℕ) (ρ : ℝ) (k : ℕ) (π : ℕ → ℝ) (J : ℝ) : ℝ :=
  if hx : ∃ x, 0 < x ∧ prefixRate n ρ k (Function.update π k x) = J then Classical.choose hx
  else 0

theorem stepRoot_unique {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ < 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {J : ℝ} (hJ : 0 < J) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) (hFx : prefixRate n ρ k (Function.update π k x) = J)
    (hFy : prefixRate n ρ k (Function.update π k y) = J) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := prefixRate_update_strictAnti hk1 hk hρ hπ hx hxy (by rw [hFy]; exact hJ)
    rw [hFx, hFy] at this
    exact absurd this (lt_irrefl _)
  · exact hxy
  · have := prefixRate_update_strictAnti hk1 hk hρ hπ hy hxy (by rw [hFx]; exact hJ)
    rw [hFx, hFy] at this
    exact absurd this (lt_irrefl _)

theorem stepRoot_spec {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ < 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {J : ℝ} (hJ : 0 < J)
    (hsmall : ∃ x1, 0 < x1 ∧ J < prefixRate n ρ k (Function.update π k x1)) :
    0 < stepRoot n ρ k π J ∧
      prefixRate n ρ k (Function.update π k (stepRoot n ρ k π J)) = J := by
  obtain ⟨x1, hx1, hFx1⟩ := hsmall
  set C : ℝ := (n.choose k : ℝ)
  have hx1C : x1 ≤ C := by
    by_contra hlt
    have := prefixRate_update_le_zero hk1 hk hρ.le hπ (x := x1) (le_of_lt (not_le.mp hlt))
    linarith
  have hcont : ContinuousOn (fun x => prefixRate n ρ k (Function.update π k x)) (Set.Icc x1 C) :=
    (continuousOn_prefixRate_update hk1 hk hρ hπ hx1).mono (fun x hx => hx.1)
  have hivt := intermediate_value_Icc' hx1C hcont
  have hJmem : J ∈ Set.Icc (prefixRate n ρ k (Function.update π k C))
      (prefixRate n ρ k (Function.update π k x1)) :=
    ⟨le_trans (prefixRate_update_le_zero hk1 hk hρ.le hπ le_rfl) hJ.le, hFx1.le⟩
  obtain ⟨x, hxI, hFx⟩ := hivt hJmem
  have hex : ∃ x, 0 < x ∧ prefixRate n ρ k (Function.update π k x) = J :=
    ⟨x, lt_of_lt_of_le hx1 hxI.1, hFx⟩
  unfold stepRoot
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem stepRoot_eq {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ < 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {J : ℝ} (hJ : 0 < J) {x : ℝ} (hx : 0 < x)
    (hFx : prefixRate n ρ k (Function.update π k x) = J) : stepRoot n ρ k π J = x := by
  have hex : ∃ x, 0 < x ∧ prefixRate n ρ k (Function.update π k x) = J := ⟨x, hx, hFx⟩
  have hspec : 0 < stepRoot n ρ k π J ∧
      prefixRate n ρ k (Function.update π k (stepRoot n ρ k π J)) = J := by
    unfold stepRoot
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact stepRoot_unique hk1 hk hρ hπ hJ hspec.1 hx hspec.2 hFx

theorem exists_small_mass_rate_gt {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Ico 1 k, 0 ≤ π j) {J θ : ℝ} (hθ : 0 ≤ θ)
    (hgt : J < prefixObjective n ρ k (Function.update π k 0) θ) :
    ∃ x1, 0 < x1 ∧ J < prefixRate n ρ k (Function.update π k x1) := by
  set M0 := prefixMGF n k (Function.update π k 0) θ
  have hM0 : 0 < M0 := prefixMGF_pos hk (update_nonneg hπ le_rfl) hθ
  have hobj : ∀ x, prefixObjective n ρ k (Function.update π k x) θ =
      (k : ℝ) * ρ * θ - Real.log (M0 + x * contactGain n k k θ) := by
    intro x
    unfold prefixObjective
    rw [prefixMGF_update hk1 π x]
  have hc : ContinuousAt (fun x => (k : ℝ) * ρ * θ - Real.log (M0 + x * contactGain n k k θ))
      0 := by
    apply continuousAt_const.sub
    apply ContinuousAt.log (by fun_prop)
    simp only [zero_mul, add_zero]
    exact hM0.ne'
  have hgt' : J < (k : ℝ) * ρ * θ - Real.log (M0 + 0 * contactGain n k k θ) := by
    rw [← hobj]
    exact hgt
  have hev := (continuousAt_const.eventually_lt hc hgt').filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  obtain ⟨x1, hx1, hx1pos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨x1, hx1pos, lt_of_lt_of_le hx1 ?_⟩
  rw [← hobj]
  exact prefixObjective_le_prefixRate hk1 hk hρ (update_nonneg hπ (le_of_lt hx1pos))
    (by rw [Function.update_self]; exact hx1pos) hθ

theorem continuousAt_stepRoot {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {ρ : ℝ} (hρ : ρ < 1)
    {U : Set ℝ} (hU : IsOpen U) (hUpos : U ⊆ Set.Ioi 0) (q : ℝ → ℕ → ℝ)
    (hqc : ∀ j ∈ Ico 1 k, ContinuousOn (fun J => q J j) U)
    (hqn : ∀ J ∈ U, ∀ j ∈ Ico 1 k, 0 ≤ q J j)
    (hspec : ∀ J ∈ U, 0 < stepRoot n ρ k (q J) J ∧
      prefixRate n ρ k (Function.update (q J) k (stepRoot n ρ k (q J) J)) = J)
    {J0 : ℝ} (hJ0 : J0 ∈ U) : ContinuousAt (fun J => stepRoot n ρ k (q J) J) J0 := by
  set x0 := stepRoot n ρ k (q J0) J0
  obtain ⟨hx0, hF0⟩ := hspec J0 hJ0
  have hJ0pos : 0 < J0 := hUpos hJ0

  have hFc : ∀ a, 0 < a →
      ContinuousAt (fun J => prefixRate n ρ k (Function.update (q J) k a)) J0 := by
    intro a ha
    have hon : ContinuousOn (fun J => prefixRate n ρ k (Function.update (q J) k a)) U := by
      rw [continuousOn_iff_continuous_restrict]
      apply continuous_prefixRate_comp hk1 hk hρ
        (fun g : U => Function.update (q g.1) k a) _ _ ha
      · intro g
        rw [Function.update_self]
      · intro j hj
        by_cases hjk : j = k
        · subst hjk
          simp only [Function.update_self]
          exact continuous_const
        · simp only [Function.update_of_ne hjk]
          have := mem_Icc.mp hj
          exact (continuousOn_iff_continuous_restrict.mp
            (hqc j (mem_Ico.mpr ⟨this.1, lt_of_le_of_ne this.2 hjk⟩)))
      · intro g
        exact update_nonneg (hqn g.1 g.2) ha.le
    exact hon.continuousAt (hU.mem_nhds hJ0)
  have hUev : ∀ᶠ J in nhds J0, J ∈ U := hU.mem_nhds hJ0
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro a' ha'
    set a := max a' (x0 / 2)
    have ha : 0 < a := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hax : a < x0 := max_lt ha' (by linarith)
    have hFa : J0 < prefixRate n ρ k (Function.update (q J0) k a) := by
      have := prefixRate_update_strictAnti hk1 hk hρ (hqn J0 hJ0) ha hax
        (by rw [hF0]; exact hJ0pos)
      rwa [hF0] at this
    have hev := continuousAt_id.eventually_lt (hFc a ha) hFa
    filter_upwards [hev, hUev] with J hJ hJU
    obtain ⟨hr, hFr⟩ := hspec J hJU
    by_contra hle
    push Not at hle
    have hle' : stepRoot n ρ k (q J) J ≤ a := le_trans hle (le_max_left _ _)
    have := prefixRate_update_anti hk1 hk hρ.le (hqn J hJU) hr hle'
    rw [hFr] at this
    simp only [id] at hJ
    linarith
  · intro b hb
    have hbpos : 0 < b := lt_trans hx0 hb
    have hFb : prefixRate n ρ k (Function.update (q J0) k b) < J0 := by
      by_cases hpos : 0 < prefixRate n ρ k (Function.update (q J0) k b)
      · have := prefixRate_update_strictAnti hk1 hk hρ (hqn J0 hJ0) hx0 hb hpos
        rwa [hF0] at this
      · push Not at hpos
        linarith
    have hev := (hFc b hbpos).eventually_lt continuousAt_id hFb
    filter_upwards [hev, hUev] with J hJ hJU
    obtain ⟨hr, hFr⟩ := hspec J hJU
    by_contra hle
    push Not at hle
    have := prefixRate_update_anti hk1 hk hρ.le (hqn J hJU) hbpos hle
    rw [hFr] at this
    simp only [id] at hJ
    linarith

noncomputable def recVec (n : ℕ) (ρ J : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | k + 1 => Function.update (recVec n ρ J k) (k + 1) (stepRoot n ρ (k + 1) (recVec n ρ J k) J)

theorem recVec_succ (n : ℕ) (ρ J : ℝ) (k : ℕ) :
    recVec n ρ J (k + 1) =
      Function.update (recVec n ρ J k) (k + 1) (stepRoot n ρ (k + 1) (recVec n ρ J k) J) :=
  rfl

theorem recVec_succ_of_ne (n : ℕ) (ρ J : ℝ) (k : ℕ) {j : ℕ} (hj : j ≠ k + 1) :
    recVec n ρ J (k + 1) j = recVec n ρ J k j := by
  rw [recVec_succ, Function.update_of_ne hj]

theorem recVec_succ_self (n : ℕ) (ρ J : ℝ) (k : ℕ) :
    recVec n ρ J (k + 1) (k + 1) = stepRoot n ρ (k + 1) (recVec n ρ J k) J := by
  rw [recVec_succ, Function.update_self]

theorem recVec_stable (n : ℕ) (ρ J : ℝ) {j k : ℕ} (hjk : j ≤ k) :
    ∀ k', k ≤ k' → recVec n ρ J k' j = recVec n ρ J k j := by
  intro k' hk'
  induction k', hk' using Nat.le_induction with
  | base => rfl
  | succ k' hkk' ih => rw [recVec_succ_of_ne n ρ J k' (by omega), ih]

theorem recVec_props {n : ℕ} {ρ J : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hJ : 0 < J) :
    ∀ k, k ≤ n → (∀ j ∈ Icc 1 k, 0 < recVec n ρ J k j) ∧
      (∀ j ∈ Icc 1 k, prefixRate n ρ j (recVec n ρ J k) = J) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hk
    obtain ⟨hpos, hrate⟩ := ih (by omega)
    have hπ : ∀ j ∈ Ico 1 (k + 1), 0 ≤ recVec n ρ J k j := by
      intro j hj
      have := mem_Ico.mp hj
      exact (hpos j (mem_Icc.mpr ⟨this.1, by omega⟩)).le
    have hsmall : ∃ x1, 0 < x1 ∧
        J < prefixRate n ρ (k + 1) (Function.update (recVec n ρ J k) (k + 1) x1) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · apply exists_small_mass_rate_gt le_rfl hk hρ1.le hπ (θ := (J + 1) / ρ) (by positivity)
        have hM : prefixMGF n (0 + 1) (Function.update (recVec n ρ J 0) (0 + 1) 0)
            ((J + 1) / ρ) = 1 := by
          unfold prefixMGF
          simp
        unfold prefixObjective
        rw [hM, Real.log_one]
        field_simp
        push_cast
        linarith
      · have hk1 : k ∈ Icc 1 k := mem_Icc.mpr ⟨hk0, le_rfl⟩
        obtain ⟨θ, hθ, hgt⟩ := added_constraint_objective_gt hk0 hk hρ1
          (fun j hj => (hpos j hj).le) (hpos 1 (mem_Icc.mpr ⟨le_rfl, hk0⟩)) (hpos k hk1)
          (by rw [hrate k hk1]; exact hJ)
        rw [hrate k hk1] at hgt
        exact exists_small_mass_rate_gt (by omega) hk hρ1.le hπ hθ hgt
    obtain ⟨hr, hFr⟩ := stepRoot_spec (by omega) hk hρ1 hπ hJ hsmall
    constructor
    · intro j hj
      by_cases hjk : j = k + 1
      · rw [hjk, recVec_succ_self]
        exact hr
      · rw [recVec_succ_of_ne n ρ J k hjk]
        have := mem_Icc.mp hj
        exact hpos j (mem_Icc.mpr ⟨this.1, by omega⟩)
    · intro j hj
      by_cases hjk : j = k + 1
      · rw [hjk, recVec_succ]
        exact hFr
      · have hj' := mem_Icc.mp hj
        have hjle : j ≤ k := by omega
        rw [prefixRate_congr (π' := recVec n ρ J k)
          (fun i hi => recVec_succ_of_ne n ρ J k (by have := (mem_Icc.mp hi).2; omega))]
        exact hrate j (mem_Icc.mpr ⟨hj'.1, hjle⟩)

theorem recVec_step_spec {n : ℕ} {ρ J : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hJ : 0 < J) {k : ℕ}
    (hk : k + 1 ≤ n) :
    0 < stepRoot n ρ (k + 1) (recVec n ρ J k) J ∧
      prefixRate n ρ (k + 1)
        (Function.update (recVec n ρ J k) (k + 1) (stepRoot n ρ (k + 1) (recVec n ρ J k) J)) =
        J := by
  obtain ⟨hpos, hrate⟩ := recVec_props hρ0 hρ1 hJ (k + 1) hk
  have hmem : k + 1 ∈ Icc 1 (k + 1) := mem_Icc.mpr ⟨by omega, le_rfl⟩
  refine ⟨?_, ?_⟩
  · have := hpos (k + 1) hmem
    rwa [recVec_succ_self] at this
  · have := hrate (k + 1) hmem
    rwa [recVec_succ] at this

theorem recVec_continuousOn {n : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ k, k ≤ n → ∀ j ∈ Icc 1 k, ContinuousOn (fun J => recVec n ρ J k j) (Set.Ioi 0) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    simp at hj
  | succ k ih =>
    intro hk j hj
    by_cases hjk : j = k + 1
    · subst hjk
      simp_rw [recVec_succ_self]
      intro J0 hJ0
      apply ContinuousAt.continuousWithinAt
      refine continuousAt_stepRoot (by omega) hk hρ1 isOpen_Ioi le_rfl
        (fun J => recVec n ρ J k) ?_ ?_ ?_ hJ0
      · intro i hi
        have := mem_Ico.mp hi
        exact ih (by omega) i (mem_Icc.mpr ⟨this.1, by omega⟩)
      · intro J hJ i hi
        have := mem_Ico.mp hi
        exact ((recVec_props hρ0 hρ1 hJ k (by omega)).1 i
          (mem_Icc.mpr ⟨this.1, by omega⟩)).le
      · intro J hJ
        exact recVec_step_spec hρ0 hρ1 hJ hk
    · have hfun : (fun J => recVec n ρ J (k + 1) j) = fun J => recVec n ρ J k j :=
        funext fun J => recVec_succ_of_ne n ρ J k hjk
      rw [hfun]
      have := mem_Icc.mp hj
      exact ih (by omega) j (mem_Icc.mpr ⟨this.1, by omega⟩)

theorem exp_ge_tangent (x c : ℝ) : Real.exp c * (1 + x - c) ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x - c)
  have hc := Real.exp_pos c
  rw [Real.exp_sub, le_div_iff₀ hc] at h
  linarith

theorem fullMGF_ge_exp_mean {n : ℕ} {h : ℝ} (hh1 : h ≤ 1) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Icc 1 n, 0 ≤ π j) (hmass : ∑ j ∈ Icc 1 n, π j = h) (θ : ℝ) :
    Real.exp ((∑ j ∈ Icc 1 n, (j : ℝ) * π j) * θ) ≤ fullMGF n h π θ := by
  set m := ∑ j ∈ Icc 1 n, (j : ℝ) * π j with hm
  set c := m * θ with hc
  have h1 : ∀ j ∈ Icc 1 n, π j * (Real.exp c * (1 + (j : ℝ) * θ - c)) ≤
      π j * Real.exp ((j : ℝ) * θ) :=
    fun j hj => mul_le_mul_of_nonneg_left (exp_ge_tangent _ _) (hπ j hj)
  have h2 : (1 - h) * (Real.exp c * (1 + 0 - c)) ≤ (1 - h) * 1 := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have := exp_ge_tangent 0 c
    rwa [Real.exp_zero] at this
  have hsum := Finset.sum_le_sum h1
  have hexp : ∑ j ∈ Icc 1 n, π j * (Real.exp c * (1 + (j : ℝ) * θ - c)) =
      Real.exp c * ((1 - c) * h + θ * m) := by
    have : ∀ j ∈ Icc 1 n, π j * (Real.exp c * (1 + (j : ℝ) * θ - c)) =
        Real.exp c * ((1 - c) * π j + θ * ((j : ℝ) * π j)) := fun j _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hmass, ← hm]
  unfold fullMGF
  have hkey : Real.exp c = (1 - h) * (Real.exp c * (1 + 0 - c)) +
      Real.exp c * ((1 - c) * h + θ * m) := by
    rw [hc]
    ring
  linarith

theorem mean_lt_of_prefixRate_self_pos {n : ℕ} {ρ h : ℝ} (hh1 : h ≤ 1) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Icc 1 n, 0 ≤ π j) (hmass : ∑ j ∈ Icc 1 n, π j = h)
    (hpos : 0 < prefixRate n ρ n π) : ∑ j ∈ Icc 1 n, (j : ℝ) * π j < (n : ℝ) * ρ := by
  by_contra hge
  push Not at hge
  have hle : prefixRate n ρ n π ≤ 0 := by
    apply ciSup_le
    intro θ
    have hθ := θ.2
    unfold prefixObjective
    rw [prefixMGF_self_eq_fullMGF hmass]
    have h1 := fullMGF_ge_exp_mean hh1 hπ hmass θ
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    have h3 : (n : ℝ) * ρ * θ ≤ (∑ j ∈ Icc 1 n, (j : ℝ) * π j) * θ :=
      mul_le_mul_of_nonneg_right hge hθ
    linarith
  linarith

theorem binaryKL_nonneg {ρ q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 ≤ binaryKL ρ q := by
  have h := binary_objective_le hq0 hq1 hρ0 hρ1 0
  simpa using h

theorem binaryKL_pos {ρ q : ℝ} (hq0 : 0 < q) (hqρ : q < ρ) (hρ1 : ρ < 1) :
    0 < binaryKL ρ q := by
  have hρ0 : 0 < ρ := lt_trans hq0 hqρ
  have hmid : (q + ρ) / 2 ∈ Set.Ioo 0 ρ := ⟨by linarith, by linarith⟩
  have hlt := binaryKL_strictAntiOn hρ0 hρ1 ⟨hq0, hqρ⟩ hmid (by linarith)
  have := binaryKL_nonneg (q := (q + ρ) / 2) (by linarith) (by linarith) hρ0 hρ1
  linarith

theorem exists_isRouteSolution {n : ℕ} (hn : 1 ≤ n) {ρ h : ℝ} (hρ1 : ρ < 1) (hh0 : 0 < h)
    (hh1 : h ≤ 1) (hβ : h < (n : ℝ) * ρ) : ∃ π, IsRouteSolution n ρ h π := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hρ0 : 0 < ρ := by
    by_contra hρ
    push Not at hρ
    nlinarith
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  ·
    have hn1' : n = 1 := by omega
    subst hn1'
    refine ⟨fun _ => h, ?_, ?_, ?_, ?_⟩
    · intro j _
      exact hh0
    · simp
    · simpa using hβ
    · intro k hk
      have hk1 : k = 1 := by simp at hk; omega
      rw [hk1]
      exact prefixRate_self_eq_fullRate (by simp)

  set q0 := h / n with hq0
  have hq0pos : 0 < q0 := div_pos hh0 hnpos
  have hq0ρ : q0 < ρ := by
    rw [hq0, div_lt_iff₀ hnpos]
    linarith
  set Jmin := binaryKL ρ q0 with hJmin
  have hJmin_pos : 0 < Jmin := binaryKL_pos hq0pos hq0ρ hρ1
  set ε := h / (2 * n) with hε
  have hεpos : 0 < ε := div_pos hh0 (by positivity)
  set B : ℕ → ℝ := fun k => binaryKL ρ (ε / (n.choose k : ℝ)) with hB
  set Jbig := Jmin + 1 + ∑ k ∈ Icc 1 n, |B k| with hJbig
  have hsumB : 0 ≤ ∑ k ∈ Icc 1 n, |B k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hJle : Jmin ≤ Jbig := by linarith
  set S : ℝ → ℝ := fun J => ∑ j ∈ Icc 1 n, recVec n ρ J n j with hS
  have hScont0 : ContinuousOn S (Set.Ioi 0) :=
    continuousOn_finsetSum _ fun j hj => recVec_continuousOn hρ0 hρ1 n le_rfl j hj
  have hScont : ContinuousOn S (Set.Icc Jmin Jbig) :=
    hScont0.mono (fun J hJ => show J ∈ Set.Ioi 0 from lt_of_lt_of_le hJmin_pos hJ.1)

  have hSmin : h < S Jmin := by
    have hprops := recVec_props hρ0 hρ1 hJmin_pos n le_rfl
    have h1 : recVec n ρ Jmin n 1 = h := by
      rw [recVec_stable n ρ Jmin (le_refl 1) n hn, recVec_succ_self]
      apply stepRoot_eq le_rfl hn hρ1 (by simp) hJmin_pos hh0
      rw [prefixRate_one_eq_binaryKL hn hρ0 hρ1 (by rw [Function.update_self]; exact hh0)
        (by rw [Function.update_self]; exact hq0ρ), Function.update_self]
    have h2 := hprops.1 2 (mem_Icc.mpr ⟨by omega, hn2⟩)
    rw [← h1]
    exact Finset.single_lt_sum (by omega) (mem_Icc.mpr ⟨le_rfl, hn⟩)
      (mem_Icc.mpr ⟨by omega, hn2⟩) h2 (fun k hk _ => (hprops.1 k hk).le)

  have hSbig : S Jbig < h := by
    have hJbig_pos : 0 < Jbig := by linarith
    have hsmall : ∀ j ∈ Icc 1 n, recVec n ρ Jbig n j < ε := by
      intro j hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by have := (mem_Icc.mp hj).1; omega⟩
      have hin : i + 1 ≤ n := (mem_Icc.mp hj).2
      rw [recVec_stable n ρ Jbig (le_refl (i + 1)) n hin, recVec_succ_self]
      obtain ⟨hr, hFr⟩ := recVec_step_spec hρ0 hρ1 hJbig_pos hin
      have hπ : ∀ l ∈ Ico 1 (i + 1), 0 ≤ recVec n ρ Jbig i l := by
        intro l hl
        have := mem_Ico.mp hl
        exact ((recVec_props hρ0 hρ1 hJbig_pos i (by omega)).1 l
          (mem_Icc.mpr ⟨this.1, by omega⟩)).le
      by_contra hge
      push Not at hge
      have hC : (1 : ℝ) ≤ (n.choose (i + 1) : ℝ) := by
        exact_mod_cast Nat.choose_pos hin
      have hεC : ε / (n.choose (i + 1) : ℝ) < 1 := by
        rw [div_lt_one (by linarith)]
        have : ε < 1 := by
          rw [hε, div_lt_one (by positivity)]
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have : (2 : ℝ) ≤ 2 * n := by linarith
          linarith
        linarith
      have h1 := prefixRate_update_anti (by omega) hin hρ1.le hπ hεpos hge
      have h2 := prefixRate_update_le_binaryKL (by omega) hin hρ0 hρ1 hπ hεpos hεC
      have h3 : B (i + 1) ≤ ∑ k ∈ Icc 1 n, |B k| :=
        le_trans (le_abs_self _) (Finset.single_le_sum (f := fun k => |B k|)
          (fun k _ => abs_nonneg _) hj)
      rw [hFr] at h1
      simp only [hB] at h3
      linarith
    have hlt := Finset.sum_lt_sum_of_nonempty (s := Icc 1 n)
      ⟨1, mem_Icc.mpr ⟨le_rfl, hn⟩⟩ hsmall
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hlt
    have hcard : ((n + 1 - 1 : ℕ) : ℝ) = n := by simp
    rw [hcard] at hlt
    have : (n : ℝ) * ε = h / 2 := by
      rw [hε]
      field_simp
    simp only [hS]
    linarith
  obtain ⟨J, hJI, hSJ⟩ := intermediate_value_Icc' hJle hScont ⟨hSbig.le, hSmin.le⟩
  have hJpos : 0 < J := lt_of_lt_of_le hJmin_pos hJI.1
  obtain ⟨hpos, hrate⟩ := recVec_props hρ0 hρ1 hJpos n le_rfl
  have hmass : ∑ j ∈ Icc 1 n, recVec n ρ J n j = h := hSJ
  have hfull : fullRate n ρ h (recVec n ρ J n) = J := by
    rw [← prefixRate_self_eq_fullRate hmass]
    exact hrate n (mem_Icc.mpr ⟨hn, le_rfl⟩)
  refine ⟨recVec n ρ J n, hpos, hmass, ?_, ?_⟩
  · apply mean_lt_of_prefixRate_self_pos hh1 (fun j hj => (hpos j hj).le) hmass
    rw [hrate n (mem_Icc.mpr ⟨hn, le_rfl⟩)]
    exact hJpos
  · intro k hk
    rw [hrate k hk, hfull]

theorem existsUnique_isRouteSolution {n : ℕ} (hn : 1 ≤ n) {ρ h : ℝ} (hρ1 : ρ < 1)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hβ : h < (n : ℝ) * ρ) :
    ∃ π, IsRouteSolution n ρ h π ∧
      ∀ π', IsRouteSolution n ρ h π' → ∀ j ∈ Icc 1 n, π' j = π j := by
  obtain ⟨π, hπ⟩ := exists_isRouteSolution hn hρ1 hh0 hh1 hβ
  exact ⟨π, hπ, fun π' hπ' => IsRouteSolution.unique hρ1 hπ' hπ⟩

theorem differentiable_prefixMGF (n k : ℕ) (π : ℕ → ℝ) : Differentiable ℝ (prefixMGF n k π) := by
  unfold prefixMGF contactGain hyperPGF hyperNum
  fun_prop

theorem prefixObjective_first_order {n k : ℕ} (hk : k ≤ n) {ρ : ℝ} {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Icc 1 k, 0 ≤ π j) {θ : ℝ} (hθ : 0 < θ)
    (hmax : ∀ θ', 0 ≤ θ' → prefixObjective n ρ k π θ' ≤ prefixObjective n ρ k π θ) :
    deriv (fun t => Real.log (prefixMGF n k π t)) θ = (k : ℝ) * ρ := by
  have hloc : IsLocalMax (prefixObjective n ρ k π) θ :=
    Filter.eventually_of_mem (Ioi_mem_nhds hθ) (fun t ht => hmax t (le_of_lt ht))
  have hd := hloc.deriv_eq_zero
  have hMd : DifferentiableAt ℝ (fun t => Real.log (prefixMGF n k π t)) θ :=
    ((differentiable_prefixMGF n k π) θ).log (prefixMGF_pos hk hπ hθ.le).ne'
  have hder : HasDerivAt (prefixObjective n ρ k π)
      ((k : ℝ) * ρ * 1 - deriv (fun t => Real.log (prefixMGF n k π t)) θ) θ :=
    ((hasDerivAt_id θ).const_mul ((k : ℝ) * ρ)).sub hMd.hasDerivAt
  rw [hder.deriv] at hd
  linarith

theorem IsRouteSolution.optimizer_first_order {n : ℕ} {ρ h : ℝ} {π : ℕ → ℝ}
    (hS : IsRouteSolution n ρ h π) (hρ : ρ < 1) {k : ℕ} (hk : k ∈ Icc 1 n) :
    ∃ θ, 0 < θ ∧ prefixObjective n ρ k π θ = prefixRate n ρ k π ∧
      deriv (fun t => Real.log (prefixMGF n k π t)) θ = (k : ℝ) * ρ := by
  obtain ⟨θ, hθ, hval, hmax⟩ := hS.positive_optimizer hρ hk
  exact ⟨θ, hθ, hval,
    prefixObjective_first_order (mem_Icc.mp hk).2 (hS.nonneg_prefix (mem_Icc.mp hk).2) hθ hmax⟩

end Ample
end FCAppendix
