import FCAppendix.AppendixRepair.GeneralLow.ExactLow
import FCAppendix.AppendixRepair.Information
import FCAppendix.Affine.Hybrid.NativeFocalReindex

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.ReferenceContext
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Affine.Hybrid.NativeContinuation
open Information
open FCAppendix.AppendixRepair.GeneralLow
open scoped BigOperators

variable {m : ℕ}

def classifier (d U : ℝ) : Information.Classifier :=
  thresholdClassifier d U

theorem tag_eq (d U : ℝ) (o : Option ℝ) :
    Information.tag (classifier d U) o = TaggedLocal.tag d U o :=
  threshold_tag_eq d U o

theorem localCount_eq (d U : ℝ) (L : LocalList m) (k : Fin 4) :
    Information.localCount (classifier d U) L k = TaggedLocal.localCount d U L k := by
  simp only [Information.localCount, TaggedLocal.localCount, tag_eq]

theorem lowPart_eq (d U : ℝ) (L : LocalList m) :
    Information.part (classifier d U) 0 L = TaggedLocal.lowList d U L := by
  exact threshold_low_part_eq d U L

theorem classified_routes {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) :
    Information.Routes (fun i => (classifier d U).label (z i).1.2.bid)
      (drawsRealization z) := by
  constructor
  · intro i hi
    rcases hz i with h | h
    · simp only [drawsRealization, h.2, firstK_full_two]
    · have hlo : ¬ (z i).1.2.bid ≤ d := not_le.mpr (hdU.trans_lt h.1)
      have hl : (classifier d U).label (z i).1.2.bid = 2 := by
        simp [classifier, thresholdClassifier, hlo, not_le.mpr h.1]
      exact False.elim (hi hl)
  · intro i hi
    rcases hz i with h | h
    · by_cases hb : (z i).1.2.bid ≤ d
      · simp [classifier, thresholdClassifier, hb] at hi
      · simp [classifier, thresholdClassifier, hb, h.1] at hi
    · simpa only [drawsRealization, card_firstK _ _ (z i).1.2.routeCount_le] using h.2

theorem lowPart_actual {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (j : Fin 2) :
    Information.part (classifier d U) 0 (observe (drawsRealization z) j) =
      eraseActiveList (upperSet d (actualContext U z).1) (actualContext U z).1 := by
  rw [lowPart_eq, ← erase_active_broadcast_list hdU]
  have he := observedContext_eq_actual z hz j
  have hb : broadcastPart U (observe (drawsRealization z) j) = (actualContext U z).1 :=
    congrArg Prod.fst he
  rw [hb]

theorem countLow_eq_visible {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (j : Fin 2) :
    Information.localCount (classifier d U) (observe (drawsRealization z) j) 0 =
      (ExactLow.visible (eraseActiveList (upperSet d (actualContext U z).1)
        (actualContext U z).1)).card := by
  rw [← lowPart_actual hdU z hz j]
  classical
  rw [ExactLow.visible, Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold Information.localCount
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : Information.tag (classifier d U) (observe (drawsRealization z) j i) = 0
  · have hp : observe (drawsRealization z) j i ≠ none := by
      intro hn
      simp [hn, Information.tag] at ht
    simp [Information.part, ht, hp]
  · simp [Information.part, ht]

theorem countActive_eq {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (j : Fin 2) :
    Information.localCount (classifier d U) (observe (drawsRealization z) j) 1 =
      (upperSet d (actualContext U z).1).card := by
  rw [localCount_eq, ← activeSet_broadcast_card hdU]
  have he := congrArg Prod.fst (observedContext_eq_actual z hz j)
  rw [show broadcastPart U (observe (drawsRealization z) j) =
    (actualContext U z).1 from he]

theorem countPrivate_eq {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (j : Fin 2) :
    Information.localCount (classifier d U) (observe (drawsRealization z) j) 2 =
      contextUpper j (actualContext U z) := by
  rw [localCount_eq, ← localCount_upper_eq hdU,
    ← contextUpper_observed U j (observe (drawsRealization z) j),
    observedContext_eq_actual z hz j]

theorem ownResidual_eq {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (c : ℕ) (j : Fin 2) :
    Information.ownResidual (classifier d U) c (observe (drawsRealization z) j) =
      min (ExactLow.visible (eraseActiveList (upperSet d (actualContext U z).1)
        (actualContext U z).1)).card
        (residual c j (actualContext U z) - (upperSet d (actualContext U z).1).card) := by
  unfold Information.ownResidual
  rw [countLow_eq_visible hdU z hz j, countActive_eq hdU z hz j,
    countPrivate_eq hdU z hz j]
  dsimp only [NativeContinuation.residual]
  congr 1
  omega

theorem otherResidual_eq {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (c : ℕ) (j : Fin 2) :
    Information.otherResidual (classifier d U) c (observe (drawsRealization z) j) =
      min (ExactLow.visible (eraseActiveList (upperSet d (actualContext U z).1)
        (actualContext U z).1)).card
        (residual c (Information.other j) (actualContext U z) -
          (upperSet d (actualContext U z).1).card) := by
  let kind := fun i => (classifier d U).label (z i).1.2.bid
  have hc : Correct (classifier d U) kind (drawsRealization z) := fun _ => rfl
  have hr := classified_routes hdU z hz
  have h₁ := (residuals_correct (classifier d U) c kind (drawsRealization z) hc hr j).2
  have h₂ := (residuals_correct (classifier d U) c kind (drawsRealization z) hc hr
    (Information.other j)).1
  rw [h₁, ← h₂]
  exact ownResidual_eq hdU z hz c (Information.other j)

end FCAppendix.Appendix08.GeneralLow.ReferenceContext
