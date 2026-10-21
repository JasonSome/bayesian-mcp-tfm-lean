import FCAppendix.AppendixRepair.Information

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory Game Set Information

structure BidClasses (d : ℝ) where
  lowSet : Set ℝ
  activeSet : Set ℝ
  privateSet : Set ℝ
  measurable_lowSet : MeasurableSet lowSet
  measurable_activeSet : MeasurableSet activeSet
  measurable_privateSet : MeasurableSet privateSet
  disjoint_low_active : Disjoint lowSet activeSet
  disjoint_low_private : Disjoint lowSet privateSet
  disjoint_active_private : Disjoint activeSet privateSet
  low_interval : Icc 0 d ⊆ lowSet

namespace BidClasses
variable {d : ℝ} (B : BidClasses d)

def classifier : Classifier := by
  classical
  exact {
    label := fun b => if b ∈ B.lowSet then 0 else if b ∈ B.activeSet then 1 else 2
    measurable_label := Measurable.ite B.measurable_lowSet measurable_const
      (Measurable.ite B.measurable_activeSet measurable_const measurable_const) }

@[simp] theorem classifier_low {b : ℝ} (hb : b ∈ B.lowSet) :
    B.classifier.label b = 0 := by
  simp [classifier, hb]

theorem classifier_low_iff (b : ℝ) :
    B.classifier.label b = 0 ↔ b ∈ B.lowSet := by
  by_cases hb : b ∈ B.lowSet
  · simp [classifier, hb]
  · by_cases ha : b ∈ B.activeSet <;> simp [classifier, hb, ha]

@[simp] theorem classifier_active {b : ℝ} (hb : b ∈ B.activeSet) :
    B.classifier.label b = 1 := by
  have hl : b ∉ B.lowSet := fun h =>
    (Set.disjoint_left.mp B.disjoint_low_active) h hb
  simp [classifier, hl, hb]

theorem classifier_active_iff (b : ℝ) :
    B.classifier.label b = 1 ↔ b ∈ B.activeSet := by
  constructor
  · intro h
    by_cases hl : b ∈ B.lowSet
    · simp [classifier, hl] at h
    · by_contra ha
      simp [classifier, hl, ha] at h
  · exact B.classifier_active

@[simp] theorem classifier_private {b : ℝ} (hb : b ∈ B.privateSet) :
    B.classifier.label b = 2 := by
  have hl : b ∉ B.lowSet := fun h =>
    (Set.disjoint_left.mp B.disjoint_low_private) h hb
  have ha : b ∉ B.activeSet := fun h =>
    (Set.disjoint_left.mp B.disjoint_active_private) h hb
  simp [classifier, hl, ha]

theorem classifier_low_bid {b : ℝ} (hb0 : 0 ≤ b) (hbd : b ≤ d) :
    B.classifier.label b = 0 := B.classifier_low (B.low_interval ⟨hb0, hbd⟩)

theorem classifier_outside {b : ℝ}
    (hl : b ∉ B.lowSet) (ha : b ∉ B.activeSet) :
    B.classifier.label b = 2 := by
  simp [classifier, hl, ha]

theorem correct {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    (hboxes : ∀ i,
      (kind i = 0 → (x.action i).bid ∈ B.lowSet) ∧
      (kind i = 1 → (x.action i).bid ∈ B.activeSet) ∧
      (kind i = 2 → (x.action i).bid ∈ B.privateSet)) :
    Correct B.classifier kind x := by
  intro i
  rcases hk : kind i with ⟨k, hklt⟩
  interval_cases k
  · exact B.classifier_low ((hboxes i).1 (by simp [hk]))
  · exact B.classifier_active ((hboxes i).2.1 (by simp [hk]))
  · exact B.classifier_private ((hboxes i).2.2 (by simp [hk]))

theorem local_information {m : ℕ} (kind : Fin m → Fin 3)
    (x : Realization m 2) (c : ℕ) (j : Fin 2)
    (hboxes : ∀ i,
      (kind i = 0 → (x.action i).bid ∈ B.lowSet) ∧
      (kind i = 1 → (x.action i).bid ∈ B.activeSet) ∧
      (kind i = 2 → (x.action i).bid ∈ B.privateSet))
    (hr : Routes kind x) :
    localCount B.classifier (observe x j) 0 = countKind kind 0 ∧
    localCount B.classifier (observe x j) 1 = countKind kind 1 ∧
    localCount B.classifier (observe x j) 2 = privateAt kind x j ∧
    privateAt kind x (other j) =
      m - localCount B.classifier (observe x j) 0 -
        localCount B.classifier (observe x j) 1 -
        localCount B.classifier (observe x j) 2 ∧
    ownResidual B.classifier c (observe x j) =
      min (countKind kind 0) (c - countKind kind 1 - privateAt kind x j) ∧
    otherResidual B.classifier c (observe x j) =
      min (countKind kind 0) (c - countKind kind 1 - privateAt kind x (other j)) := by
  have hc := B.correct kind x hboxes
  obtain ⟨hl, ha, hp⟩ := local_counts_correct B.classifier kind x hc hr j
  obtain ⟨ho, ht⟩ := residuals_correct B.classifier c kind x hc hr j
  exact ⟨hl, ha, hp, reconstruct_other_private B.classifier kind x hc hr j, ho, ht⟩

end BidClasses
end FCAppendix.Appendix08.GeneralLow
