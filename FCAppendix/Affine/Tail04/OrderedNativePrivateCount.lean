import FCAppendix.Affine.Tail04.OrderedNativeCountCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePrivateCount
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeCountCoordinates LocalCoordinates SortedCoordinates
open EqualPrivateSignal JoinedHighPolicy Hybrid

variable {m c : ℕ} (D : Data m c)

def privateDecision (j : Fin 2) (L : LocalList m) (i : Fin m) (u : Seed) : Bool :=
  if hi : i∈ids D.E 2 L then
    if OrderedNativePolicy.role D.E j L=0 then
      decide (Sum.inr (rankFin (ids D.E 2 L) (privateKey D.E L) ⟨i,hi⟩)∈
        D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L))
          (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
            (D.finiteCount (ids D.E 3 L)) L,privateRow D.E (ids D.E 2 L) L) u.1)
    else
      decide (Sum.inr (rankFin (ids D.E 2 L) (privateKey D.E L) ⟨i,hi⟩)∈
        D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 3 L))
          (D.finiteCount (ids D.E 2 L))
          (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 3 L))
            (D.finiteCount (ids D.E 2 L)) L,privateRow D.E (ids D.E 2 L) L) u.1)
  else false

lemma privateDecision_eq (j : Fin 2) (L : LocalList m) (hL : D.offCommon L=∅)
    (i : Fin m) (hi : i∈ids D.E 2 L ∨ L i=none) (u : Seed) :
    privateDecision D j L i u=decide (i∈(OrderedNativePolicy.policy D j L u).val) := by
  rcases hi with hi | hi
  · unfold privateDecision
    simp only [dif_pos hi]
    rw [OrderedNativePolicy.policy_on_menu D j L hL u]
    by_cases hr : OrderedNativePolicy.role D.E j L=0
    · simp only [hr,ite_true,own_zero_private D L i hi u]
    · have hr1 : OrderedNativePolicy.role D.E j L=1 := by
        have hh := (OrderedNativePolicy.role D.E j L).isLt
        omega
      simp only [hr1,if_neg (by decide : (1:Fin 2)≠0),own_one_private D L i hi u]
  · have hn : i∉ids D.E 2 L := by
      simp [ids,hi,Observable.Regions.localTag]
    have ha : i∉(OrderedNativePolicy.policy D j L u).val := fun hh =>
      (OrderedNativePolicy.policy D j L u).property.2 i hh hi
    simp only [privateDecision,dif_neg hn,ha,decide_false]

theorem boundedCount_private (x : Realization m 2) (s : Fin 2→Seed) (i : Fin m)
    (hmenu : ∀ j,D.offCommon (observe x j)=∅)
    (hi : ∀ j,i∈ids D.E 2 (observe x j) ∨ observe x j i=none) :
    Game.boundedCount x (OrderedNativePolicy.policy D) s i=
      boolPairCount (privateDecision D 0 (observe x 0) i (s 0),
        privateDecision D 1 (observe x 1) i (s 1)) := by
  rw [OrderedNativeCountCoordinates.boundedCount_eq_pair D]
  unfold OrderedNativeCountCoordinates.pair
  rw [privateDecision_eq D 0 _ (hmenu 0) i (hi 0) (s 0),
    privateDecision_eq D 1 _ (hmenu 1) i (hi 1) (s 1)]

end FCAppendix.Affine.Tail04.OrderedNativePrivateCount
