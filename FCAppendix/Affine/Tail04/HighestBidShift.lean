import FCAppendix.Existence.HighestBidPolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.HighestBidShift
open Game Game.HighestBid Set Classical
open scoped BigOperators

variable {m c : ℕ}

def shift (L : LocalList m) : LocalList m := fun i => (L i).map (·+1)

lemma feasible_shift (L : LocalList m) (S : Finset (Fin m)) :
    LocallyFeasible (shift L) c S ↔ LocallyFeasible L c S := by
  have hp (i : Fin m) : shift L i ≠ none ↔ L i ≠ none := by
    cases he : L i <;> simp [shift,he]
  simp only [LocallyFeasible,hp]

lemma revenue_shift (L : LocalList m) (S : Finset (Fin m))
    (hS : ∀ i∈S,L i ≠ none) :
    revenue (shift L) S = revenue L S + S.card := by
  calc
    _ = ∑ i∈S,(Bayes.entryBid (L i)+1) := by
      apply Finset.sum_congr rfl
      intro i hi
      cases he : L i with
      | none => exact (hS i hi he).elim
      | some b => simp [shift,he,Bayes.entryBid]
    _ = _ := by simp [Finset.sum_add_distrib,revenue]

lemma max_cardinality (L : LocalList m) (hL : Bayes.NonnegativeList L)
    (T : Finset (Fin m)) (hT : LocallyFeasible L c T) :
    T.card ≤ (selection L c).card := by
  by_contra hn
  have hc : (selection L c).card < c := (lt_of_not_ge hn).trans_le hT.1
  have hnot : ¬T ⊆ selection L c := by
    intro hsub
    exact hn (Finset.card_le_card hsub)
  obtain ⟨i,hi,his⟩ := Finset.not_subset.mp hnot
  let U := insert i (selection L c)
  have hU : LocallyFeasible L c U := by
    constructor
    · simp only [U,Finset.card_insert_of_notMem his]
      omega
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hT.2 _ hi
      · exact (selection_best L c).1.2 j hj
  have hrev : revenue L U = Bayes.entryBid (L i)+revenue L (selection L c) :=
    Finset.sum_insert his
  have he : revenue L U = revenue L (selection L c) := by
    apply le_antisymm (revenue_le_selection L c U hU)
    rw [hrev]
    exact le_add_of_nonneg_left (hL i)
  have hcard := card_le_selection_of_revenue_eq L c U hU he
  simp only [U,Finset.card_insert_of_notMem his] at hcard
  omega

theorem selection_shift (L : LocalList m) (hL : Bayes.NonnegativeList L) :
    selection (shift L) c = selection L c := by
  apply best_unique (selection_best (shift L) c)
  refine ⟨(feasible_shift L _).mpr (selection_best L c).1,?_⟩
  intro T hT
  have hT' := (feasible_shift L T).mp hT
  have hcard := max_cardinality L hL T hT'
  have hcast : (T.card:ℝ) ≤ (selection L c).card := by exact_mod_cast hcard
  have hscore := (selection_best L c).2 T hT'
  have hRT := revenue_shift L T hT'.2
  have hRS := revenue_shift L (selection L c) (selection_best L c).1.2
  change toLex (revenue (shift L) T,toLex (T.card,OrderDual.toDual (code m T))) ≤
    toLex (revenue (shift L) (selection L c),
      toLex ((selection L c).card,OrderDual.toDual (code m (selection L c))))
  rw [hRT,hRS]
  simp only [score,Prod.Lex.toLex_le_toLex] at hscore
  simp only [Prod.Lex.toLex_le_toLex]
  rcases hscore with hr | ⟨hr,hrest⟩
  · exact Or.inl (add_lt_add_of_lt_of_le hr hcast)
  · rcases hrest with hn | ⟨hn,hcode⟩
    · have hcast' : (T.card:ℝ) < (selection L c).card := by exact_mod_cast hn
      exact Or.inl (by rw [hr];linarith)
    · exact Or.inr ⟨by rw [hr,hn],Or.inr ⟨hn,hcode⟩⟩

end FCAppendix.Affine.Tail04.HighestBidShift
