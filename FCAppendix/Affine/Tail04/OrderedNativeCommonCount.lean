import FCAppendix.Affine.Tail04.OrderedNativeCountCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeCommonCount
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeCountCoordinates OrderedNativeCountCoordinates
open LocalCoordinates SortedCoordinates NativeObservationPair EqualPrivateSignal

variable {m c : ℕ} (D : Data m c)

lemma menu_zero {L K : LocalList m} (hL : D.offCommon L=∅) (hK : D.offCommon K=∅) :
    D.offCommon (zeroList D L K)=∅ := by
  unfold zeroList
  split
  · exact hL
  · exact hK

lemma menu_one {L K : LocalList m} (hL : D.offCommon L=∅) (hK : D.offCommon K=∅) :
    D.offCommon (oneList D L K)=∅ := by
  unfold oneList
  split
  · exact hK
  · exact hL

lemma zero_ids {L K : LocalList m} (h : D.E.Compatible L K) :
    ids D.E 1 (zeroList D L K)=ids D.E 1 L := by
  unfold zeroList
  split
  · rfl
  · exact (D.E.common_ids h (Or.inr rfl)).symm

lemma zero_present {L K : LocalList m} (h : D.E.Compatible L K)
    (i : Fin m) (hi : i∈ids D.E 1 L) : i∈ids D.E 1 (zeroList D L K) := by
  rw [zero_ids D h]
  exact hi

theorem pair_common {L K : LocalList m} (h : D.E.Compatible L K)
    (hL : D.offCommon L=∅) (hK : D.offCommon K=∅)
    (i : Fin m) (hi : i∈ids D.E 1 L) (u v : Seed) :
    let Z:=zeroList D L K
    let O:=oneList D L K
    pair D L K i u v=
      originalPairCount
        (D.zeroSampler (ids D.E 1 Z).card (D.finiteCount (ids D.E 2 Z))
          (D.finiteCount (ids D.E 3 Z)))
        (D.oneSampler (ids D.E 1 Z).card (D.finiteCount (ids D.E 2 Z))
          (D.finiteCount (ids D.E 3 Z)))
        (D.parameter (ids D.E 1 Z) (D.finiteCount (ids D.E 2 Z))
          (D.finiteCount (ids D.E 3 Z)) Z)
        (Sum.inl (rankFin (ids D.E 1 Z) (bidVector Z) ⟨i,zero_present D h i hi⟩))
        (Sum.inl (rankFin (ids D.E 1 Z) (bidVector Z) ⟨i,zero_present D h i hi⟩))
        ((privateRow D.E (ids D.E 2 Z) Z,(zeroSeed D L u v).1),
          (privateRow D.E (ids D.E 3 Z) O,(oneSeed D L u v).1)) := by
  dsimp only
  rw [pair_eq_restored D h]
  exact listPairCount_common D (ordered_compatible D h) (menu_zero D hL hK)
    (menu_one D hL hK) i (zero_present D h i hi) (zeroSeed D L u v) (oneSeed D L u v)

end FCAppendix.Affine.Tail04.OrderedNativeCommonCount
