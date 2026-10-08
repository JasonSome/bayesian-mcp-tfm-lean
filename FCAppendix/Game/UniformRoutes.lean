import FCAppendix.Game.LocalInformation

namespace FCAppendix
namespace Game

open scoped BigOperators

abbrev RecipientSet (n k : ℕ) := {R : Finset (Fin n) // R.card = k}

theorem recipientSet_nonempty (n k : ℕ) (hk : k ≤ n) : Nonempty (RecipientSet n k) := by
  classical
  obtain ⟨R, _, hR⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simpa using hk)
  exact ⟨⟨R, hR⟩⟩

noncomputable def uniformRecipients (n k : ℕ) (hk : k ≤ n) : FiniteLaw (RecipientSet n k) := by
  letI : Nonempty (RecipientSet n k) := recipientSet_nonempty n k hk
  exact FiniteLaw.uniform _

noncomputable def renameRecipients {n k : ℕ} (e : Equiv.Perm (Fin n)) :
    RecipientSet n k ≃ RecipientSet n k where
  toFun R := ⟨R.val.map e.toEmbedding, by simp⟩
  invFun R := ⟨R.val.map e.symm.toEmbedding, by simp⟩
  left_inv R := by
    apply Subtype.ext
    ext j
    simp
  right_inv R := by
    apply Subtype.ext
    ext j
    simp

theorem mem_renameRecipients {n k : ℕ} (e : Equiv.Perm (Fin n))
    (R : RecipientSet n k) (j : Fin n) :
    j ∈ (renameRecipients e R).val ↔ e.symm j ∈ R.val := by
  classical
  constructor
  · intro hj
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hj
    have : e.symm j = a := by rw [← he]; simp
    simpa [this] using ha
  · intro hj
    exact Finset.mem_map.mpr ⟨e.symm j, hj, e.apply_symm_apply j⟩

noncomputable def recipientMarginal (n k : ℕ) (hk : k ≤ n) (j : Fin n) : ℝ :=
  (uniformRecipients n k hk).prob (fun R => j ∈ R.val)

theorem recipientMarginal_eq (n k : ℕ) (hk : k ≤ n) (j l : Fin n) :
    recipientMarginal n k hk j = recipientMarginal n k hk l := by
  classical
  letI : Nonempty (RecipientSet n k) := recipientSet_nonempty n k hk
  have h := FiniteLaw.uniform_expect_equiv
    (renameRecipients (Equiv.swap j l))
    (fun R : RecipientSet n k => if j ∈ R.val then (1 : ℝ) else 0)
  have hm : ∀ R : RecipientSet n k,
      (j ∈ (renameRecipients (Equiv.swap j l) R).val) ↔ l ∈ R.val := by
    intro R
    rw [mem_renameRecipients]
    simp
  simp_rw [hm] at h
  unfold recipientMarginal
  rw [FiniteLaw.prob_eq_expect, FiniteLaw.prob_eq_expect]
  exact h.symm

theorem sum_membership_real {α : Type*} [Fintype α] [DecidableEq α] (R : Finset α) :
    (∑ a, if a ∈ R then (1 : ℝ) else 0) = (R.card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  simp

theorem sum_recipientMarginals (n k : ℕ) (hk : k ≤ n) :
    (∑ j, recipientMarginal n k hk j) = (k : ℝ) := by
  classical
  unfold recipientMarginal
  simp_rw [FiniteLaw.prob_eq_expect]
  rw [← FiniteLaw.expect_finset_sum]
  calc
    _ = (uniformRecipients n k hk).expect (fun _ => (k : ℝ)) := by
      apply FiniteLaw.expect_congr
      intro R
      rw [sum_membership_real, R.property]
    _ = _ := FiniteLaw.expect_const _ _

theorem recipientMarginal_formula (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (j : Fin n) :
    recipientMarginal n k hk j = (k : ℝ) / n := by
  have hsum := sum_recipientMarginals n k hk
  have he : (∑ l : Fin n, recipientMarginal n k hk l) =
      (n : ℝ) * recipientMarginal n k hk j := by
    calc
      _ = ∑ _l : Fin n, recipientMarginal n k hk j := by
        apply Finset.sum_congr rfl
        intro l _
        exact recipientMarginal_eq n k hk l j
      _ = _ := by simp
  rw [he] at hsum
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  apply (eq_div_iff hnR).mpr
  simpa [mul_comm] using hsum

end Game
end FCAppendix
