import FCAppendix.AppendixRepair.GeneralLow.ExactLow
import FCAppendix.AppendixRepair.GeneralLow.HigherPosterior

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.DirectGame
open MeasureTheory ProbabilityTheory Set Game Bayes Information
open Affine Affine.Hybrid HigherPolicy HigherPosterior
open scoped BigOperators

open FCAppendix.AppendixRepair.GeneralLow

variable {m c : ℕ}

local instance : Nonempty (JointAction 2) := ⟨Interim.abstain 2⟩

def lowSelect (C : Classifier) (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (L : LocalList m) (z : unitInterval) : Finset (Fin m) :=
  ExactLow.select ξ hξ hξ1 (part C 0 L) (ownResidual C c L) (otherResidual C c L) z

theorem lowSelect_feasible (C : Classifier) (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (L : LocalList m) (z : unitInterval) :
    LocallyFeasible (part C 0 L) (ownResidual C c L) (lowSelect C ξ hξ hξ1 c L z) :=
  ExactLow.select_feasible ξ hξ hξ1 (part C 0 L) (ownResidual C c L)
    (otherResidual C c L) z

theorem lowSelect_present (C : Classifier) (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (L : LocalList m) (z : unitInterval) (i : Fin m)
    (hi : i ∈ lowSelect C ξ hξ hξ1 c L z) :
    L i ≠ none ∧ tag C (L i) = 0 := by
  have hp := (lowSelect_feasible C ξ hξ hξ1 c L z).2 i hi
  by_cases ht : tag C (L i) = 0
  · exact ⟨by simpa only [part, if_pos ht] using hp, ht⟩
  · simp only [part, if_neg ht, ne_eq, not_true_eq_false] at hp

theorem lowSelect_empty_of_high_saturated (C : Classifier) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (L : LocalList m) (z : unitInterval)
    (hc : c ≤ (highSet C L).card) : lowSelect C ξ hξ hξ1 c L z = ∅ := by
  apply Finset.card_eq_zero.mp
  have hl := (lowSelect_feasible C ξ hξ hξ1 c L z).1
  rw [highSet_card] at hc
  dsimp only [ownResidual] at hl
  omega

theorem measurable_lowSelect (C : Classifier) (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) : Measurable (Function.uncurry (lowSelect (m := m) C ξ hξ hξ1 c)) :=
  ExactLow.measurable_select ξ hξ hξ1
    (fun x : LocalList m × unitInterval => part C 0 x.1)
    ((measurable_part C 0).comp measurable_fst)
    (fun x => ownResidual C c x.1) (fun x => otherResidual C c x.1)
    ((measurable_ownResidual C c).comp measurable_fst)
    ((measurable_otherResidual C c).comp measurable_fst) Prod.snd measurable_snd

def rawSelection (C : Classifier) (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval)
    (j : Fin 2) (L : LocalList m) (z : unitInterval) : Finset (Fin m) :=
  highSelection C (1 - ξ) c HC j L z ∪ lowSelect C ξ hξ hξ1 c L z

theorem rawSelection_feasible (C : Classifier) (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (HC : HigherSelector (m := m) C c unitInterval)
    (j : Fin 2) (L : LocalList m) (z : unitInterval) :
    LocallyFeasible L c (rawSelection C ξ hξ hξ1 c HC j L z) := by
  constructor
  · apply (Finset.card_union_le _ _).trans
    have hh := highSelection_card C (1 - ξ) c HC j L z
    have hl := (lowSelect_feasible C ξ hξ hξ1 c L z).1
    have hr : ownResidual C c L ≤ c - (highSet C L).card := by
      rw [highSet_card]
      dsimp only [ownResidual]
      omega
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hh | hl
    · exact highSet_present C L i (highSelection_subset_highSet C (1 - ξ) c HC j L z hh)
    · exact (lowSelect_present C ξ hξ hξ1 c L z i hl).1

theorem rawSelection_low_membership (C : Classifier) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval)
    (j : Fin 2) (L : LocalList m) (z : unitInterval) (i : Fin m)
    (hi : tag C (L i) = 0) :
    i ∈ rawSelection C ξ hξ hξ1 c HC j L z ↔ i ∈ lowSelect C ξ hξ hξ1 c L z := by
  have hh : i ∉ highSelection C (1 - ξ) c HC j L z := by
    intro h
    exact highSet_not_low C L i (highSelection_subset_highSet C (1 - ξ) c HC j L z h) hi
  simp only [rawSelection, Finset.mem_union, hh, false_or]

theorem rawSelection_high_membership (C : Classifier) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval)
    (j : Fin 2) (L : LocalList m) (z : unitInterval) (i : Fin m)
    (hi : i ∈ highSet C L) :
    i ∈ rawSelection C ξ hξ hξ1 c HC j L z ↔
      i ∈ highSelection C (1 - ξ) c HC j L z := by
  have hl : i ∉ lowSelect C ξ hξ hξ1 c L z := by
    intro h
    exact highSet_not_low C L i hi (lowSelect_present C ξ hξ hξ1 c L z i h).2
  simp only [rawSelection, Finset.mem_union, hl, or_false]

theorem measurable_rawSelection (C : Classifier) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval) (j : Fin 2) :
    Measurable (Function.uncurry (rawSelection C ξ hξ hξ1 c HC j)) :=
  (measurable_of_countable (fun p : Finset (Fin m) × Finset (Fin m) => p.1 ∪ p.2)).comp
    ((measurable_highSelection C (1 - ξ) c HC j).prodMk
      (measurable_lowSelect C ξ hξ hξ1 c))

def selection (C : Classifier) (d ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval)
    (j : Fin 2) (L : LocalList m) (z : unitInterval) : Finset (Fin m) := by
  classical
  exact if CompatibleList C d (1 - ξ) L then rawSelection C ξ hξ hξ1 c HC j L z
    else HighestBid.selection L c

theorem selection_feasible (C : Classifier) (d ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (HC : HigherSelector (m := m) C c unitInterval)
    (j : Fin 2) (L : LocalList m) (z : unitInterval) :
    LocallyFeasible L c (selection C d ξ hξ hξ1 c HC j L z) := by
  unfold selection
  split
  · exact rawSelection_feasible C ξ hξ hξ1 c HC j L z
  · exact (HighestBid.selection_best L c).1

theorem measurable_selection (C : Classifier) (d ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval) (j : Fin 2) :
    Measurable (Function.uncurry (selection C d ξ hξ hξ1 c HC j)) :=
  Measurable.ite ((measurableSet_compatibleList C d (1 - ξ)).preimage measurable_fst)
    (measurable_rawSelection C ξ hξ hξ1 c HC j)
    ((HighestBid.measurable_selection m c).comp measurable_fst)

def localPolicy (C : Classifier) (d ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval) (j : Fin 2) : LocalPolicy m c unitInterval :=
  fun L z => ⟨selection C d ξ hξ hξ1 c HC j L z,
    selection_feasible C d ξ hξ hξ1 c HC j L z⟩

theorem selection_low_membership (C : Classifier) (d ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval)
    (j : Fin 2) (L : LocalList m) (z : unitInterval) (i : Fin m)
    (hL : CompatibleList C d (1 - ξ) L) (hi : tag C (L i) = 0) :
    i ∈ selection C d ξ hξ hξ1 c HC j L z ↔ i ∈ lowSelect C ξ hξ hξ1 c L z := by
  rw [selection, if_pos hL]
  exact rawSelection_low_membership C ξ hξ hξ1 c HC j L z i hi

theorem selection_high_membership (C : Classifier) (d ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval)
    (j : Fin 2) (L : LocalList m) (z : unitInterval) (i : Fin m)
    (hL : CompatibleList C d (1 - ξ) L) (hi : i ∈ highSet C L) :
    i ∈ selection C d ξ hξ hξ1 c HC j L z ↔
      i ∈ highSelection C (1 - ξ) c HC j L z := by
  rw [selection, if_pos hL]
  exact rawSelection_high_membership C ξ hξ hξ1 c HC j L z i hi

theorem inclusionCount_eq_zero_of_high_saturated (C : Classifier) (d ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (HC : HigherSelector (m := m) C c unitInterval)
    (x : Realization m 2) (z : Fin 2 → unitInterval) (i : Fin m)
    (hi : C.label (x.action i).bid = 0)
    (hcomp : ∀ j, CompatibleList C d (1 - ξ) (observe x j))
    (hcap : ∀ j, c ≤ (highSet C (observe x j)).card) :
    inclusionCount x (localPolicy C d ξ hξ hξ1 c HC) z i = 0 := by
  rw [inclusionCount_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hn : i ∉ allocation x (localPolicy C d ξ hξ hξ1 c HC) z j := by
    intro hmem
    change i ∈ selection C d ξ hξ hξ1 c HC j (observe x j) (z j) at hmem
    by_cases hrec : j ∈ x.recipients i
    · have ht : tag C (observe x j i) = 0 := by simp [observe, hrec, tag, hi]
      have hlo := (selection_low_membership C d ξ hξ hξ1 c HC j (observe x j)
        (z j) i (hcomp j) ht).mp hmem
      rw [lowSelect_empty_of_high_saturated C ξ hξ hξ1 c _ _ (hcap j)] at hlo
      exact Finset.notMem_empty i hlo
    · have hvisible := (selection_feasible C d ξ hξ hξ1 c HC j (observe x j) (z j)).2 i hmem
      exact hvisible (by simp [observe, hrec])
  simp only [if_neg hn]

def game (m c : ℕ) (P : ProbabilityMeasure (ℝ × JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (C : Classifier) (d : ℝ) (HC : HigherSelector (m := m) C c unitInterval) :
    FiniteGame m 2 c unitInterval where
  F := (P : Measure (ℝ × JointAction 2)).fst
  hF := inferInstance
  σ := (P : Measure (ℝ × JointAction 2)).condKernel
  hσ := inferInstance
  seedLaw := volume
  hseed := inferInstance
  policy := localPolicy C d ((1 - η) / 2) (by linarith) (by linarith) c HC
  policy_measurable := measurable_selection C d ((1 - η) / 2)
    (by linarith) (by linarith) c HC
  A := Schedule.affine 2 η hη0 hη1.le
  G := Schedule.once 2
  g := 0
  g_nonneg := le_rfl

theorem joint_law (P : ProbabilityMeasure (ℝ × JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (C : Classifier) (d : ℝ) (HC : HigherSelector (m := m) C c unitInterval) :
    (game m c P η hη0 hη1 C d HC).F ⊗ₘ (game m c P η hη0 hη1 C d HC).σ =
      (P : Measure (ℝ × JointAction 2)) := by
  change (P : Measure (ℝ × JointAction 2)).fst ⊗ₘ
    (P : Measure (ℝ × JointAction 2)).condKernel = _
  exact Measure.disintegrate _ _

def emptyHigher (C : Classifier) (c : ℕ) : HigherSelector (m := m) C c unitInterval where
  select := fun _ _ _ => ∅
  measurable := fun _ => measurable_const
  card_le := by intros; simp
  subset_high := by intros; exact Finset.empty_subset _

theorem lowSelect_same_decoded_data (C D : Classifier) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (x y : Realization m 2) (h : SameLowObservation C D x y)
    (j : Fin 2) (z : unitInterval) :
    lowSelect C ξ hξ hξ1 c (observe x j) z =
      lowSelect D ξ hξ hξ1 c (observe y j) z := by
  obtain ⟨hl, ho, ht⟩ := same_decoded_low_data C D c x y h j
  simp only [lowSelect, hl, ho, ht]

theorem lowSelect_on_profile (C : Classifier) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (kind : Fin m → Fin 3) (x : Realization m 2)
    (hc : Correct C kind x) (hr : Routes kind x) (j : Fin 2) (z : unitInterval) :
    lowSelect C ξ hξ hξ1 c (observe x j) z =
      ExactLow.select ξ hξ hξ1
        (fun i => if kind i = 0 then some (x.action i).bid else none)
        (min (countKind kind 0) (c - countKind kind 1 - privateAt kind x j))
        (min (countKind kind 0) (c - countKind kind 1 - privateAt kind x (other j))) z := by
  obtain ⟨ho, ht⟩ := residuals_correct C c kind x hc hr j
  have hl : part C 0 (observe x j) =
      (fun i => if kind i = 0 then some (x.action i).bid else none) := by
    simpa using broadcast_part_observe C kind x hc hr 0 (by decide) j
  rw [lowSelect, ho, ht, hl]

end FCAppendix.Appendix08.GeneralLow.DirectGame
