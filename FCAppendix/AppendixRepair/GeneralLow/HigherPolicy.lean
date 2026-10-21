import FCAppendix.AppendixRepair.Information
import FCAppendix.Affine.Hybrid.ClassifiedPolicy

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.HigherPolicy
open MeasureTheory ProbabilityTheory Game Bayes Set
open scoped BigOperators

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def highSet (C : Information.Classifier) (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => Information.tag C (L i) = 1 ∨
    Information.tag C (L i) = 2)

theorem mem_highSet (C : Information.Classifier) (L : LocalList m) (i : Fin m) :
    i ∈ highSet C L ↔ Information.tag C (L i) = 1 ∨ Information.tag C (L i) = 2 := by
  simp [highSet]

theorem highSet_present (C : Information.Classifier) (L : LocalList m) (i : Fin m)
    (hi : i ∈ highSet C L) : L i ≠ none := by
  intro hn
  rcases (mem_highSet C L i).mp hi with h | h <;> simp [hn, Information.tag] at h

theorem highSet_not_low (C : Information.Classifier) (L : LocalList m) (i : Fin m)
    (hi : i ∈ highSet C L) : Information.tag C (L i) ≠ 0 := by
  rcases (mem_highSet C L i).mp hi with h | h <;> simp [h]

theorem higher_optimal_iff (C : Information.Classifier) (c : ℕ) (L : LocalList m)
    (r : Fin m → ℝ) (S : Finset (Fin m)) (hS : S ⊆ highSet C L) :
    Finite.Optimal c (fun i => if i ∈ highSet C L then r i else 0) S ↔
      S.card ≤ c ∧ ∀ T : Finset (Fin m), T ⊆ highSet C L → T.card ≤ c →
        (∑ i ∈ T, r i) ≤ ∑ i ∈ S, r i := by
  classical
  have hsum (T : Finset (Fin m)) (hT : T ⊆ highSet C L) :
      (∑ i ∈ T, if i ∈ highSet C L then r i else 0) = ∑ i ∈ T, r i :=
    Finset.sum_congr rfl fun i hi => if_pos (hT hi)
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro T hT hcap
    simpa only [hsum T hT, hsum S hS] using h.2 T hcap
  · rintro ⟨hcap, hbest⟩
    refine ⟨hcap, ?_⟩
    intro T hT
    let U := T.filter (fun i => i ∈ highSet C L)
    have hU : U ⊆ highSet C L := fun _ hi => (Finset.mem_filter.mp hi).2
    have hcard : U.card ≤ c := (Finset.card_filter_le _ _).trans hT
    have hreceipt : (∑ i ∈ T, if i ∈ highSet C L then r i else 0) =
        ∑ i ∈ U, r i := by simp only [U, Finset.sum_filter]
    rw [hreceipt, hsum S hS]
    exact hbest U hU hcard

theorem highSet_card (C : Information.Classifier) (L : LocalList m) :
    (highSet C L).card = Information.localCount C L 1 + Information.localCount C L 2 := by
  classical
  simp only [highSet, Finset.card_eq_sum_ones, Finset.sum_filter,
    Information.localCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : Information.tag C (L i) = 1
  · simp [h1]
  · by_cases h2 : Information.tag C (L i) = 2 <;> simp [h1, h2]

theorem localCounts_sum (C : Information.Classifier) (L : LocalList m) :
    Information.localCount C L 0 + Information.localCount C L 1 +
      Information.localCount C L 2 + Information.localCount C L 3 = m := by
  classical
  calc
    _ = ∑ i : Fin m,
        ((if Information.tag C (L i) = 0 then 1 else 0) +
         (if Information.tag C (L i) = 1 then 1 else 0) +
         (if Information.tag C (L i) = 2 then 1 else 0) +
         (if Information.tag C (L i) = 3 then 1 else 0)) := by
      simp only [Information.localCount, Finset.sum_add_distrib]
    _ = ∑ _i : Fin m, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases ht : Information.tag C (L i) with ⟨k, hk⟩
      interval_cases k <;> simp [Fin.ext_iff]
    _ = m := by simp

theorem measurable_highSet (C : Information.Classifier) :
    Measurable (highSet (m := m) C) := by
  classical
  apply measurable_to_countable'
  intro S
  have he : highSet (m := m) C ⁻¹' {S} =
      ⋂ i : Fin m, {L : LocalList m | (i ∈ S ↔
        Information.tag C (L i) = 1 ∨ Information.tag C (L i) = 2)} := by
    ext L
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_setOf_eq]
    exact ⟨fun h i => by rw [← h]; exact mem_highSet C L i,
      fun h => Finset.ext fun i => (mem_highSet C L i).trans (h i).symm⟩
  rw [he]
  apply MeasurableSet.iInter
  intro i
  have hm := ((measurableSet_eq_fun
    ((Information.measurable_tag C).comp (measurable_pi_apply i)) measurable_const).union
    (measurableSet_eq_fun
      ((Information.measurable_tag C).comp (measurable_pi_apply i)) measurable_const) :
    MeasurableSet {L : LocalList m | Information.tag C (L i) = 1 ∨
      Information.tag C (L i) = 2})
  by_cases hi : i ∈ S
  · simp only [hi, true_iff]
    exact hm
  · simp only [hi, false_iff]
    exact hm.compl

def otherHigh (C : Information.Classifier) (L : LocalList m) : ℕ :=
  Information.localCount C L 1 + Information.localCount C L 3

theorem measurable_otherHigh (C : Information.Classifier) :
    Measurable (otherHigh (m := m) C) :=
  (Information.measurable_localCount C 1).add (Information.measurable_localCount C 3)

theorem measurable_highCard (C : Information.Classifier) :
    Measurable (fun L : LocalList m => (highSet C L).card) :=
  (measurable_of_countable Finset.card).comp (measurable_highSet C)

def highWeight (C : Information.Classifier) (κ : ℝ) (L : LocalList m) (i : Fin m) : ℝ :=
  if Information.tag C (L i) = 1 then κ * entryBid (L i) else entryBid (L i)

theorem measurable_highWeight (C : Information.Classifier) (κ : ℝ) (i : Fin m) :
    Measurable (fun L : LocalList m => highWeight C κ L i) := by
  exact Measurable.ite
    (measurableSet_eq_fun ((Information.measurable_tag C).comp (measurable_pi_apply i))
      measurable_const)
    (measurable_const.mul (measurable_entryBid.comp (measurable_pi_apply i)))
    (measurable_entryBid.comp (measurable_pi_apply i))

def weightedPart (C : Information.Classifier) (κ : ℝ) (L : LocalList m) : LocalList m :=
  fun i => if i ∈ highSet C L then some (highWeight C κ L i) else none

theorem measurable_weightedPart (C : Information.Classifier) (κ : ℝ) :
    Measurable (weightedPart (m := m) C κ) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    ((measurable_highSet C) (MeasurableSet.of_discrete :
      MeasurableSet {S : Finset (Fin m) | i ∈ S}))
    (measurable_some.comp (measurable_highWeight C κ i)) measurable_const

theorem weightedPart_present (C : Information.Classifier) (κ : ℝ)
    (L : LocalList m) (i : Fin m) :
    weightedPart C κ L i ≠ none ↔ i ∈ highSet C L := by
  classical
  simp [weightedPart]

theorem weightedPart_receipt (C : Information.Classifier) (κ : ℝ)
    (L : LocalList m) (i : Fin m) :
    entryBid (weightedPart C κ L i) =
      if i ∈ highSet C L then highWeight C κ L i else 0 := by
  classical
  by_cases hi : i ∈ highSet C L <;> simp [weightedPart, hi, entryBid]

structure HigherSelector (C : Information.Classifier) (c : ℕ) (Seed : Type*)
    [MeasurableSpace Seed] where
  select : Fin 2 → LocalList m → Seed → Finset (Fin m)
  measurable : ∀ j, Measurable (Function.uncurry (select j))
  card_le : ∀ j L z, (select j L z).card ≤ c
  subset_high : ∀ j L z, select j L z ⊆ highSet C L

def highSelection (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed)
    (j : Fin 2) (L : LocalList m) (z : Seed) : Finset (Fin m) :=
  if (highSet C L).card < c then highSet C L
  else if otherHigh C L < c then HighestBid.selection (weightedPart C κ L) c
  else HC.select j L z

theorem highSelection_subset_highSet (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed) :
    highSelection C κ c HC j L z ⊆ highSet C L := by
  classical
  unfold highSelection
  split_ifs
  · exact Finset.Subset.refl _
  · intro i hi
    exact (weightedPart_present C κ L i).mp
      ((HighestBid.selection_best (weightedPart C κ L) c).1.2 i hi)
  · exact HC.subset_high j L z

theorem highSelection_card (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed) :
    (highSelection C κ c HC j L z).card ≤ min c (highSet C L).card := by
  apply le_min
  · unfold highSelection
    split_ifs with h
    · exact h.le
    · exact (HighestBid.selection_best (weightedPart C κ L) c).1.1
    · exact HC.card_le j L z
  · exact Finset.card_le_card (highSelection_subset_highSet C κ c HC j L z)

theorem measurable_highSelection (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) :
    Measurable (Function.uncurry (highSelection C κ c HC j)) := by
  apply Measurable.ite
    (measurableSet_lt ((measurable_highCard C).comp measurable_fst) measurable_const)
    ((measurable_highSet C).comp measurable_fst)
  exact Measurable.ite
    (measurableSet_lt ((measurable_otherHigh C).comp measurable_fst) measurable_const)
    ((HighestBid.measurable_selection m c).comp
      ((measurable_weightedPart C κ).comp measurable_fst)) (HC.measurable j)

theorem highSelection_eq_all (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed)
    (h : (highSet C L).card < c) :
    highSelection C κ c HC j L z = highSet C L := by
  simp only [highSelection, if_pos h]

theorem highSelection_eq_weighted (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed)
    (h : c ≤ (highSet C L).card) (ho : otherHigh C L < c) :
    highSelection C κ c HC j L z = HighestBid.selection (weightedPart C κ L) c := by
  simp only [highSelection, if_neg (not_lt.mpr h), if_pos ho]

theorem highSelection_eq_HC (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed)
    (h : c ≤ (highSet C L).card) (ho : c ≤ otherHigh C L) :
    highSelection C κ c HC j L z = HC.select j L z := by
  simp only [highSelection, if_neg (not_lt.mpr h), if_neg (not_lt.mpr ho)]

theorem highSelection_optimal_high (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed)
    (r : Fin m → ℝ) (hr : ∀ i ∈ highSet C L, 0 ≤ r i)
    (hspare : otherHigh C L < c → ∀ i ∈ highSet C L, r i = highWeight C κ L i)
    (hHC : c ≤ (highSet C L).card → c ≤ otherHigh C L →
      Finite.Optimal c (fun i => if i ∈ highSet C L then r i else 0) (HC.select j L z)) :
    Finite.Optimal c (fun i => if i ∈ highSet C L then r i else 0)
      (highSelection C κ c HC j L z) := by
  classical
  by_cases h : (highSet C L).card < c
  · rw [highSelection_eq_all C κ c HC j L z h]
    apply Affine.Hybrid.optimal_of_order_slack c _ _ h.le
    · intro i hi
      simpa only [if_pos hi] using hr i hi
    · intro i hi k hk
      simpa only [if_pos hi, if_neg hk] using hr i hi
    · intro _ k hk
      simp only [if_neg hk, le_refl]
  · have hn : c ≤ (highSet C L).card := le_of_not_gt h
    by_cases ho : otherHigh C L < c
    · rw [highSelection_eq_weighted C κ c HC j L z hn ho]
      have he : (fun i => if i ∈ highSet C L then r i else 0) =
          fun i => entryBid (weightedPart C κ L i) := by
        funext i
        rw [weightedPart_receipt]
        by_cases hi : i ∈ highSet C L
        · simp only [if_pos hi, hspare ho i hi]
        · simp only [if_neg hi]
      rw [he]
      exact HighestBid.selection_optimal (weightedPart C κ L) c
    · rw [highSelection_eq_HC C κ c HC j L z hn (le_of_not_gt ho)]
      exact hHC hn (le_of_not_gt ho)

theorem highSelection_fills (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed)
    (r : Fin m → ℝ) (hr : ∀ i ∈ highSet C L, 0 < r i)
    (hopt : Finite.Optimal c (fun i => if i ∈ highSet C L then r i else 0)
      (highSelection C κ c HC j L z)) (h : c ≤ (highSet C L).card) :
    (highSelection C κ c HC j L z).card = c := by
  classical
  apply le_antisymm hopt.1
  by_contra hn
  have hlt : (highSelection C κ c HC j L z).card < (highSet C L).card := by omega
  obtain ⟨i, hiH, hiS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hp : 0 < (if i ∈ highSet C L then r i else 0) := by
    simpa only [if_pos hiH] using hr i hiH
  have hf := Finite.optimal_fills c _ _ hopt i hiS hp
  omega

theorem union_optimal (C : Information.Classifier) (κ : ℝ) (c : ℕ)
    (HC : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed)
    (r : Fin m → ℝ) (S : Finset (Fin m))
    (hr : ∀ i, 0 ≤ r i) (hhigh : ∀ i ∈ highSet C L, 0 < r i)
    (hpriority : ∀ i ∈ highSet C L, ∀ k ∉ highSet C L, r k ≤ r i)
    (hdisj : Disjoint (highSet C L) S)
    (hlow : Finite.Optimal (c - (highSet C L).card)
      (fun i => if i ∈ highSet C L then 0 else r i) S)
    (hspare : otherHigh C L < c → ∀ i ∈ highSet C L, r i = highWeight C κ L i)
    (hHC : c ≤ (highSet C L).card → c ≤ otherHigh C L →
      Finite.Optimal c (fun i => if i ∈ highSet C L then r i else 0) (HC.select j L z)) :
    Finite.Optimal c r (highSelection C κ c HC j L z ∪ S) := by
  classical
  by_cases h : (highSet C L).card < c
  · rw [highSelection_eq_all C κ c HC j L z h]
    exact Affine.Hybrid.priority_union_optimal c r (highSet C L) S h.le hdisj hr
      hpriority hlow
  · have hn : c ≤ (highSet C L).card := le_of_not_gt h
    have hz : S = ∅ := by
      apply Finset.card_eq_zero.mp
      have hc := hlow.1
      omega
    rw [hz, Finset.union_empty]
    have hopt := highSelection_optimal_high C κ c HC j L z r
      (fun i hi => (hhigh i hi).le) hspare hHC
    exact Affine.Hybrid.priority_full_optimal c r (highSet C L) _
      (highSelection_subset_highSet C κ c HC j L z)
      (highSelection_fills C κ c HC j L z r hhigh hopt hn)
      hr hpriority hopt

end FCAppendix.Appendix08.GeneralLow.HigherPolicy
