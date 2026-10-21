import FCAppendix.Proposer.MeasurableLotteryPolicy
import FCAppendix.Game.PosteriorFeasible
import Mathlib.Data.Prod.Lex

noncomputable section
namespace FCAppendix.Game.HighestBid
open MeasureTheory Set Classical
open scoped BigOperators

def code (m : ℕ) (S : Finset (Fin m)) : ℕ := (Fintype.equivFin _ S).val

theorem code_injective (m : ℕ) : Function.Injective (code m) := by
  intro S T h
  apply (Fintype.equivFin _).injective
  exact Fin.ext h

def revenue {m : ℕ} (L : LocalList m) (S : Finset (Fin m)) : ℝ :=
  ∑ i ∈ S, Bayes.entryBid (L i)

theorem measurable_revenue {m : ℕ} (S : Finset (Fin m)) :
    Measurable (fun L : LocalList m => revenue L S) :=
  Finset.measurable_sum _ fun i _ => Bayes.measurable_entryBid.comp (measurable_pi_apply i)

abbrev Score := ℝ ×ₗ (ℕ ×ₗ ℕᵒᵈ)

def score {m : ℕ} (L : LocalList m) (S : Finset (Fin m)) : Score :=
  toLex (revenue L S, toLex (S.card, OrderDual.toDual (code m S)))

theorem score_injective {m : ℕ} (L : LocalList m) : Function.Injective (score L) := by
  intro S T h
  apply code_injective m
  exact congrArg (fun x : Score => OrderDual.ofDual (ofLex (ofLex x).2).2) h

theorem measurableSet_score_le {m : ℕ} (S T : Finset (Fin m)) :
    MeasurableSet {L : LocalList m | score L S ≤ score L T} := by
  simp only [score, Prod.Lex.toLex_le_toLex]
  exact (measurableSet_lt (measurable_revenue S) (measurable_revenue T)).union
    ((measurableSet_eq_fun (measurable_revenue S) (measurable_revenue T)).inter
      (MeasurableSet.const _))

def Best {m : ℕ} (L : LocalList m) (c : ℕ) (S : Finset (Fin m)) : Prop :=
  LocallyFeasible L c S ∧ ∀ T, LocallyFeasible L c T → score L T ≤ score L S

theorem exists_best {m : ℕ} (L : LocalList m) (c : ℕ) : ∃ S, Best L c S := by
  obtain ⟨S, hS, hm⟩ := Finset.exists_max_image
    (Finset.univ.filter (LocallyFeasible L c)) (score L) ⟨∅, by simp [LocallyFeasible]⟩
  refine ⟨S, (Finset.mem_filter.mp hS).2, ?_⟩
  intro T hT
  exact hm T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)

theorem best_unique {m : ℕ} {L : LocalList m} {c : ℕ} {S T : Finset (Fin m)}
    (hS : Best L c S) (hT : Best L c T) : S = T :=
  score_injective L (le_antisymm (hT.2 S hS.1) (hS.2 T hT.1))

def selection {m : ℕ} (L : LocalList m) (c : ℕ) : Finset (Fin m) :=
  (exists_best L c).choose

theorem selection_best {m : ℕ} (L : LocalList m) (c : ℕ) :
    Best L c (selection L c) := (exists_best L c).choose_spec

theorem measurableSet_best {m : ℕ} (c : ℕ) (S : Finset (Fin m)) :
    MeasurableSet {L : LocalList m | Best L c S} := by
  have hf (T : Finset (Fin m)) : MeasurableSet {L : LocalList m | LocallyFeasible L c T} :=
    measurableSet_locallyFeasible.preimage (measurable_id.prodMk measurable_const)
  have he : {L : LocalList m | Best L c S} =
      {L | LocallyFeasible L c S} ∩ ⋂ T, ({L | LocallyFeasible L c T}ᶜ ∪
        {L | score L T ≤ score L S}) := by ext L; simp [Best, imp_iff_not_or]
  rw [he]
  exact (hf S).inter (MeasurableSet.iInter fun T =>
    (hf T).compl.union (measurableSet_score_le T S))

theorem measurable_selection (m c : ℕ) : Measurable (fun L : LocalList m => selection L c) := by
  apply measurable_to_countable'
  intro S
  have he : (fun L : LocalList m => selection L c) ⁻¹' {S} = {L | Best L c S} := by
    ext L
    constructor
    · intro h
      exact h ▸ selection_best L c
    · intro h
      exact best_unique (selection_best L c) h
  rw [he]
  exact measurableSet_best c S

theorem revenue_le_selection {m : ℕ} (L : LocalList m) (c : ℕ)
    (T : Finset (Fin m)) (hT : LocallyFeasible L c T) :
    revenue L T ≤ revenue L (selection L c) := by
  have h := (selection_best L c).2 T hT
  rcases Prod.Lex.toLex_le_toLex.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

theorem card_le_selection_of_revenue_eq {m : ℕ} (L : LocalList m) (c : ℕ)
    (T : Finset (Fin m)) (hT : LocallyFeasible L c T)
    (heq : revenue L T = revenue L (selection L c)) : T.card ≤ (selection L c).card := by
  have h := (selection_best L c).2 T hT
  rcases Prod.Lex.toLex_le_toLex.mp h with hlt | ⟨_, hcard⟩
  · exact (lt_irrefl _ (heq ▸ hlt)).elim
  · rcases Prod.Lex.toLex_le_toLex.mp hcard with hlt | ⟨heq, _⟩
    · exact hlt.le
    · exact heq.le

def localPolicy (m c : ℕ) : LocalPolicy m c Unit :=
  fun L _ => ⟨selection L c, (selection_best L c).1⟩

theorem measurable_localPolicy (m c : ℕ) :
    Measurable (fun x : LocalList m × Unit => (localPolicy m c x.1 x.2).val) :=
  (measurable_selection m c).comp measurable_fst

theorem selection_optimal {m : ℕ} (L : LocalList m) (c : ℕ) :
    Finite.Optimal c (fun i => Bayes.entryBid (L i)) (selection L c) := by
  refine ⟨(selection_best L c).1.1, ?_⟩
  intro T hT
  let U := T.filter (fun i => L i ≠ none)
  have hU : LocallyFeasible L c U :=
    ⟨(Finset.card_filter_le _ _).trans hT, fun i hi => (Finset.mem_filter.mp hi).2⟩
  have he : revenue L U = ∑ i ∈ T, Bayes.entryBid (L i) := by
    dsimp [revenue, U]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases L i <;> simp [Bayes.entryBid]
  exact he ▸ revenue_le_selection L c U hU

theorem selection_fills_spare {m : ℕ} (L : LocalList m) (c : ℕ)
    (hL : Bayes.NonnegativeList L)
    (hcap : (Finset.univ.filter (fun i => L i ≠ none)).card ≤ c) :
    selection L c = Finset.univ.filter (fun i => L i ≠ none) := by
  let H := Finset.univ.filter (fun i => L i ≠ none)
  have hH : LocallyFeasible L c H :=
    ⟨hcap, fun i hi => (Finset.mem_filter.mp hi).2⟩
  have hsub : selection L c ⊆ H := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (selection_best L c).1.2 i hi⟩
  have heq : revenue L H = revenue L (selection L c) := by
    apply le_antisymm (revenue_le_selection L c H hH)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    exact hL i
  exact Finset.eq_of_subset_of_card_le hsub
    (card_le_selection_of_revenue_eq L c H hH heq)

theorem selection_iff_rank {m : ℕ} (L : LocalList m) (c : ℕ)
    (hL : Bayes.NonnegativeList L) (i : Fin m) (b : ℝ) (hb : 0 ≤ b)
    (hi : L i = some b) (hno : ∀ j, j ≠ i → L j ≠ some b) :
    i ∈ selection L c ↔ (Finset.univ.filter (fun j => b < Bayes.entryBid (L j))).card < c := by
  have hbi : Bayes.entryBid (L i) = b := by simp [hi, Bayes.entryBid]
  have hopt := selection_optimal L c
  constructor
  · intro hs
    by_contra h
    have hh := Finite.excluded_of_many_better c (fun j => Bayes.entryBid (L j))
      (selection L c) hopt i
    rw [hbi] at hh
    exact hh (le_of_not_gt h) hs
  · intro hfew
    by_cases hbpos : 0 < b
    · apply Finite.included_of_few_competitors c (fun j => Bayes.entryBid (L j))
        (selection L c) hopt i (hbi ▸ hbpos)
      have he : (Finset.univ.filter (fun j => j ≠ i ∧
          Bayes.entryBid (L i) ≤ Bayes.entryBid (L j))) =
          Finset.univ.filter (fun j => b < Bayes.entryBid (L j)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbi]
        by_cases hj : j = i
        · subst j
          simp [hbi]
        · have hne : Bayes.entryBid (L j) ≠ b := by
            cases he : L j with
            | none => simpa [he, Bayes.entryBid] using hbpos.ne
            | some a =>
              intro ha
              exact hno j hj (by simpa [he, Bayes.entryBid] using ha)
          exact ⟨fun h => lt_of_le_of_ne h.2 hne.symm,
            fun h => ⟨hj, h.le⟩⟩
      simpa only [he] using hfew
    · have hbzero : b = 0 := le_antisymm (le_of_not_gt hbpos) hb
      let H := Finset.univ.filter (fun j => L j ≠ none)
      let T := Finset.univ.filter (fun j => b < Bayes.entryBid (L j))
      have hsub : H ⊆ insert i T := by
        intro j hj
        by_cases hji : j = i
        · exact Finset.mem_insert.mpr (Or.inl hji)
        · apply Finset.mem_insert.mpr
          right
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have hnonneg := hL j
          have hne : Bayes.entryBid (L j) ≠ 0 := by
            cases he : L j with
            | none => exact ((Finset.mem_filter.mp hj).2 he).elim
            | some a =>
              intro ha
              have ha0 : a = 0 := ha
              exact hno j hji (by simp [he, ha0, hbzero])
          rw [hbzero]
          exact lt_of_le_of_ne hnonneg hne.symm
      have hcap : H.card ≤ c := by
        have hh := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        change T.card < c at hfew
        omega
      rw [selection_fills_spare L c hL hcap]
      simp [hi]

end FCAppendix.Game.HighestBid
