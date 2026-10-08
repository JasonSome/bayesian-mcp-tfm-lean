import FCAppendix.Ample.ContactLaw

namespace FCAppendix.Ample

open Finset
open scoped BigOperators

noncomputable def classMass {n : ℕ} (μ : FiniteLaw (Finset (Fin n))) (j : ℕ) : ℝ :=
  μ.prob (fun T => T.card = j)

def PermInvariant {n : ℕ} (μ : FiniteLaw (Finset (Fin n))) : Prop :=
  ∀ (e : Equiv.Perm (Fin n)) T, μ.mass (e.finsetCongr T) = μ.mass T

theorem sum_classMass {n : ℕ} (μ : FiniteLaw (Finset (Fin n))) :
    ∑ j ∈ Icc 1 n, classMass μ j = μ.prob (fun T => T ≠ ∅) := by
  classical
  simp only [classMass, FiniteLaw.prob_eq_expect]
  rw [← μ.expect_finset_sum]
  apply μ.expect_congr
  intro T
  by_cases hT : T = ∅
  · simp [hT]
  · have hc := card_mem_Icc_of_ne hT
    simp [hT, hc]

theorem validLaw_classMass {n : ℕ} (μ : FiniteLaw (Finset (Fin n))) :
    ValidLaw n (classMass μ) := by
  refine ⟨fun j _ => μ.prob_nonneg _, ?_⟩
  rw [sum_classMass]
  exact μ.prob_le_one _

theorem mass_empty_eq_classMass {n : ℕ} (μ : FiniteLaw (Finset (Fin n))) :
    μ.mass ∅ = 1 - ∑ j ∈ Icc 1 n, classMass μ j := by
  rw [sum_classMass, μ.prob_compl]
  have he : μ.prob (fun T => T = ∅) = μ.mass ∅ := by
    simpa only [FiniteLaw.prob_eq_expect] using μ.expect_singleton ∅
  rw [he]
  ring

theorem mass_eq_of_card_eq {n : ℕ} {μ : FiniteLaw (Finset (Fin n))}
    (hμ : PermInvariant μ) {T U : Finset (Fin n)} (hcard : T.card = U.card) :
    μ.mass T = μ.mass U := by
  obtain ⟨e, he⟩ := exists_perm_map_eq T U hcard
  have hh := hμ e T
  simpa only [Equiv.finsetCongr_apply, he] using hh.symm

theorem sum_card_indicator {n j : ℕ} (hj : j ≤ n) :
    (∑ T : Finset (Fin n), if T.card = j then (1 : ℝ) else 0) = n.choose j := by
  classical
  rw [sum_finset_card_eq n (fun k => if k = j then (1 : ℝ) else 0)]
  have hj' : j ∈ range (n + 1) := mem_range.mpr (by omega)
  simp [mul_ite, hj']

theorem classMass_eq_mass_mul_choose {n : ℕ} {μ : FiniteLaw (Finset (Fin n))}
    (hμ : PermInvariant μ) (T : Finset (Fin n)) :
    classMass μ T.card = μ.mass T * (n.choose T.card : ℝ) := by
  classical
  have hc : T.card ≤ n := by simpa using Finset.card_le_univ T
  simp only [classMass, FiniteLaw.prob_eq_expect, FiniteLaw.expect]
  calc
    _ = ∑ U : Finset (Fin n), μ.mass T * (if U.card = T.card then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro U _
      by_cases he : U.card = T.card
      · rw [if_pos he, mass_eq_of_card_eq hμ he]
      · simp only [if_neg he, mul_zero]
    _ = μ.mass T * (∑ U : Finset (Fin n), if U.card = T.card then 1 else 0) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [sum_card_indicator hc]

theorem eq_contactLaw_of_permInvariant {n : ℕ} {μ : FiniteLaw (Finset (Fin n))}
    (hμ : PermInvariant μ) :
    μ = contactLaw n (classMass μ) (validLaw_classMass μ) := by
  apply FiniteLaw.ext
  intro T
  change μ.mass T = contactWeight n (classMass μ) T
  by_cases hT : T = ∅
  · subst T
    rw [contactWeight_empty, mass_empty_eq_classMass]
  · rw [contactWeight_of_ne _ hT, classMass_eq_mass_mul_choose hμ]
    have hc : T.card ≤ n := by simpa using Finset.card_le_univ T
    have hC : (n.choose T.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hc).ne'
    field_simp

theorem classMass_contactLaw {n j : ℕ} {lawWeights : ℕ → ℝ} (hlam : ValidLaw n lawWeights)
    (hj : j ∈ Icc 1 n) : classMass (contactLaw n lawWeights hlam) j = lawWeights j := by
  classical
  simp only [classMass, FiniteLaw.prob_eq_expect]
  rw [contactLaw_expect_card_fun n lawWeights hlam (fun k => if k = j then (1 : ℝ) else 0)]
  have hj0 : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
  simp [hj, Ne.symm hj0]

end FCAppendix.Ample
