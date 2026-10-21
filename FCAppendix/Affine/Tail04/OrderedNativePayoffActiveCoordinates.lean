import FCAppendix.Affine.Tail04.NativeActiveFiberCoordinates
import FCAppendix.Affine.Tail04.OrderedNativePayoffExperiment

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffActiveCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeMenuReports NativeCountCoordinates NativeDeletedCounts
open NativeFiberEnumerations NativeFocalCoordinates PartialNativeCoordinates
open LocalCoordinates SortedCoordinates PrivateIdentitySort PrivateRowSorting SortedAllNoise
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy OriginalPopulation OriginalValues
open Hybrid NativeFlag NativeActiveFiberCoordinates OrderedNativePayoffExperiment

def countedPrivateRow {N c : ℕ} (K : Data (N+1) c) (i : Fin (N+1))
    (kind : Fin N→Fin 4) (tag : Fin 4) (r : Fin N→UserDraw 2) :
    Row (K.finiteCount (rivalSet i kind tag)).val K.E.R K.E.Rp K.E.H :=
  privateRowRaw K.E i kind tag r

section Cast
variable {m c A B : ℕ} (K : NativeLocalPolicy.Data m c)
  (H0 H1 : Fin (m+1)) (Q : PublicScenario.Data)

lemma pairedOutcome_cast (h : A=B) (b : Fin B → Icc (1:ℝ) K.E.U) (i : Fin B)
    (low : Bool) (z : unitInterval×Pairs K H0 H1) :
    pairedOutcome K H0 H1 Q (b ∘ Fin.cast h) (Fin.cast h.symm i) low z=
      pairedOutcome K H0 H1 Q b i low z := by
  cases h
  rfl
end Cast

section Coordinates
variable {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c)
  (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hQ : ∀ A,K.publicChoice A=PublicScenario.localChoice K.E Q μL A)
  (P : ValueParameters) (t : ℝ)
  (i : Fin (N+1)) (kind : Fin N → Fin 4)
  (ω : Sample (N+1) 2 NativeLocalPolicy.Seed)
  (hr : ∀ l,l≠i → sourceBands P K.E t (ω.1.1 l).1)
  (hk : rivalKinds K.E i ω.1=kind)
  (b : Icc (1:ℝ) K.E.U)
  (hb : Function.Injective (fun q =>
    (Fin.cons (α:=fun _=>Icc (1:ℝ) K.E.U) b (commonRow K.E i kind (fun r => ω.1.1 (i.succAbove r))) q:ℝ)))
  (low : Bool) (u : unitInterval)
  (hseed : ∀ j : Fin 2,seedOnList μL (K.E.roleList 0 (presentList ω.1 i b j))=
    if low then some u else none)

include hQ hr hk hb hseed in

theorem listPair_count (j : Fin 2) :
    NativeCountCoordinates.listPairCount K
      (presentList ω.1 i b j) (presentList ω.1 i b (otherProposer j)) i
      (ω.1.2 j) (ω.1.2 (otherProposer j))=
    pairedOutcome K
      (K.finiteCount (rivalSet i kind (NativeContinuation.upperTag j)))
      (K.finiteCount (rivalSet i kind (NativeContinuation.upperTag (otherProposer j)))) Q
      (Fin.cons (α:=fun _=>Icc (1:ℝ) K.E.U) b (commonRow K.E i kind (fun r => ω.1.1 (i.succAbove r)))) 0 low
      (u,((sortRow K.E _ (countedPrivateRow K i kind (NativeContinuation.upperTag j)
        (fun r => ω.1.1 (i.succAbove r))),(ω.1.2 j).1),
        (sortRow K.E _ (countedPrivateRow K i kind (NativeContinuation.upperTag (otherProposer j))
          (fun r => ω.1.1 (i.succAbove r))),(ω.1.2 (otherProposer j)).1))) := by
  let E:=K.E
  let C:=rivalSet i kind 1
  let H0:=K.finiteCount (rivalSet i kind (NativeContinuation.upperTag j))
  let H1:=K.finiteCount (rivalSet i kind (NativeContinuation.upperTag (otherProposer j)))
  let a:=RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2
  let L : Fin 2 → LocalList (N+1):=fun s => presentList ω.1 i b s
  let raw:=Fin.cons (α:=fun _=>Icc (1:ℝ) K.E.U) b (commonRow E i kind (fun r => ω.1.1 (i.succAbove r)))
  let hc:=insert_card C i (focal_not_mem_rivalSet i kind 1)
  let raw' := raw ∘ Fin.cast hc
  let j0 : Fin (insert i C).card:=Fin.cast hc.symm 0
  have hm (r : Fin N) : MenuAction E (ω.1.1 (i.succAbove r)).1.2 :=
    source_menu E P t _ (hr _ (Fin.succAbove_ne i r))
  have hrm (l : Fin (N+1)) (hl : l≠i) : MenuAction E (ω.1.1 l).1.2 :=
    source_menu E P t _ (hr l hl)
  have ho (s : Fin 2) : observe (deviated i a ω) s=L s :=
    observe_deviated_of_mem i a ω s (by simp [a,RawRoutes.action,Hybrid.firstK_full_two])
  have hcompat0 : E.Compatible (L 0) (L 1) := by
    simpa only [ho] using compatible_deviation E i a ω (active_report_menu K b) hrm
  have hcompat : E.Compatible (L j) (L (otherProposer j)) := by
    fin_cases j
    · change E.Compatible (L 0) (L 1)
      exact hcompat0
    · change E.Compatible (L 1) (L 0)
      exact E.compatible_symm hcompat0
  have hmenu (s : Fin 2) : K.offCommon (L s)=∅ := by
    rw [←ho s]
    exact onMenu_deviation K i a ω (active_report_menu K b) hrm s
  have hids (s : Fin 2) := PartialNativeCoordinates.active_ids E i ω.1 hm b s
  dsimp only [E] at hids
  simp only [hk] at hids
  have h0 : ids E 1 (L j)=insert i C ∧
      ids E 2 (L j)=rivalSet i kind (NativeContinuation.upperTag j) ∧
      ids E 3 (L j)=rivalSet i kind (NativeContinuation.upperTag (otherProposer j)) :=
    by simpa only [L] using! (hids j).2
  have hi : i∈ids E 1 (L j) := by rw [h0.1];exact Finset.mem_insert_self _ _
  have hs : activeBids E (insert i C) (L j)=sortedBox raw' := by
    rw [sortedBox_cast]
    exact active_bids E i kind ω.1 hm hk b j
  have hj : rankFin (insert i C) (bidVector (L j)) ⟨i,Finset.mem_insert_self _ _⟩=
      focalRank (fun q => (raw' q:ℝ)) j0 := by
    change _=focalRank ((fun q => (raw q:ℝ)) ∘ Fin.cast hc) (Fin.cast hc.symm 0)
    rw [focalRank_cast]
    exact active_rank E i kind ω.1 hm hk b hb j
  have hp : K.parameter (insert i C) H0 H1 (L j)=
      let q := NativeHighExperiment.choice K H0 H1 Q raw' low u
      ((q.1,sortedBox raw'),(K.signalLaw H0,q.2)) := by
    unfold NativeLocalPolicy.Data.parameter
    rw [hs,hQ]
    dsimp only [PublicScenario.localChoice]
    rw [hseed j]
    cases low <;> rfl
  have hp0 := private_row E i kind ω.1 hm hk j (b:ℝ)
  have hp1 := private_row E i kind ω.1 hm hk (otherProposer j) (b:ℝ)
  dsimp only [E,L] at h0 hj hp hp0 hp1
  dsimp only [E,L] at hcompat
  have hn := NativeCountCoordinates.listPairCount_common K hcompat
    (hmenu j) (hmenu (otherProposer j)) i hi (ω.1.2 j) (ω.1.2 (otherProposer j))
  have transport (A0 F0 F1 : Finset (Fin (N+1)))
      (Lzero Lone : LocalList (N+1)) (hi0 : i∈A0)
      (hA : A0=insert i C) (hF0 : F0=rivalSet i kind (NativeContinuation.upperTag j))
      (hF1 : F1=rivalSet i kind (NativeContinuation.upperTag (otherProposer j)))
      (hL0 : Lzero=presentList ω.1 i b j)
      (hL1 : Lone=presentList ω.1 i b (otherProposer j)) :
      originalPairCount
        (K.zeroSampler A0.card (K.finiteCount F0) (K.finiteCount F1))
        (K.oneSampler A0.card (K.finiteCount F0) (K.finiteCount F1))
        (K.parameter A0 (K.finiteCount F0) (K.finiteCount F1) Lzero)
        (Sum.inl (rankFin A0 (bidVector Lzero) ⟨i,hi0⟩))
        (Sum.inl (rankFin A0 (bidVector Lzero) ⟨i,hi0⟩))
        ((LocalCoordinates.privateRow K.E F0 Lzero,(ω.1.2 j).1),
          (LocalCoordinates.privateRow K.E F1 Lone,(ω.1.2 (otherProposer j)).1))=
      pairedOutcome K H0 H1 Q raw' j0 low
        (u,((sortRow E _ (countedPrivateRow K i kind (NativeContinuation.upperTag j)
          (fun r => ω.1.1 (i.succAbove r))),(ω.1.2 j).1),
          (sortRow E _ (countedPrivateRow K i kind (NativeContinuation.upperTag (otherProposer j))
            (fun r => ω.1.1 (i.succAbove r))),(ω.1.2 (otherProposer j)).1))) := by
    subst A0
    subst F0
    subst F1
    subst Lzero
    subst Lone
    rw [hj,hp,hp0,hp1]
    rfl
  calc
    _=pairedOutcome K H0 H1 Q raw' j0 low
        (u,((sortRow E _ (countedPrivateRow K i kind (NativeContinuation.upperTag j)
          (fun r => ω.1.1 (i.succAbove r))),(ω.1.2 j).1),
          (sortRow E _ (countedPrivateRow K i kind (NativeContinuation.upperTag (otherProposer j))
            (fun r => ω.1.1 (i.succAbove r))),(ω.1.2 (otherProposer j)).1))) :=
      hn.trans (transport _ _ _ _ _ _ h0.1 h0.2.1 h0.2.2 rfl rfl)
    _=_ := pairedOutcome_cast K H0 H1 Q hc raw 0 low _

variable (Γ : FiniteGame (N+1) 2 c Seed)
  (hpolicy : Γ.policy=OrderedNativePolicy.policy K)

include hQ hr hk hb hseed hpolicy in

theorem active_count :
    focalCount Γ i (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2) ω=
      rawOutcome K (K.finiteCount (rivalSet i kind 2))
        (K.finiteCount (rivalSet i kind 3)) Q
        (Fin.cons (α:=fun _=>Icc (1:ℝ) K.E.U) b (commonRow K.E i kind (fun r => ω.1.1 (i.succAbove r)))) 0 low
        (u,((countedPrivateRow K i kind 2 (fun r => ω.1.1 (i.succAbove r)),
          countedPrivateRow K i kind 3 (fun r => ω.1.1 (i.succAbove r))),(ω.1.2,ω.2))) := by
  let E:=K.E
  let a:=RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2
  let L : Fin 2 → LocalList (N+1):=fun j => presentList ω.1 i b j
  have hrm (l : Fin (N+1)) (hl : l≠i) : MenuAction E (ω.1.1 l).1.2 :=
    source_menu E P t _ (hr l hl)
  have hm (r : Fin N) : MenuAction E (ω.1.1 (i.succAbove r)).1.2 := hrm _ (Fin.succAbove_ne i r)
  have ho (j : Fin 2) : observe (deviated i a ω) j=L j :=
    observe_deviated_of_mem i a ω j (by simp [a,RawRoutes.action,firstK_full_two])
  have hcompat : E.Compatible (L 0) (L 1) := by
    simpa only [ho] using compatible_deviation E i a ω (active_report_menu K b) hrm
  have hids := PartialNativeCoordinates.active_ids E i ω.1 hm b 0
  have hu0 : NativeContinuation.upperTag 0=(2:Fin 4) := by decide
  have hu1 : NativeContinuation.upperTag 1=(3:Fin 4) := by decide
  have ho0 : otherProposer 0=(1:Fin 2) := by decide
  have ho1 : otherProposer 1=(0:Fin 2) := by decide
  dsimp only [E] at hids
  simp only [hk,ho0,hu0,hu1] at hids
  have hz : OrderedNativePolicy.role E 0 (L 0)=0 ↔
      (rivalSet i kind 2).card≤(rivalSet i kind 3).card := by
    rw [OrderedNativeCountCoordinates.role_zero_iff,
      ←LocalCoordinates.ids_card,E.otherPrivateCount_eq_missing,hids.2.2.1,hids.2.2.2]
  dsimp only [a,L] at ho
  change Game.boundedCount _ Γ.policy _ _=_
  rw [hpolicy,OrderedNativeCountCoordinates.boundedCount_eq_pair]
  simp only [ho]
  rw [OrderedNativeCountCoordinates.pair_eq_restored K hcompat]
  by_cases h : (rivalSet i kind 2).card≤(rivalSet i kind 3).card
  · have hr0 := hz.mpr h
    dsimp only [E] at hr0
    simp only [OrderedNativeCountCoordinates.zeroList,OrderedNativeCountCoordinates.oneList,
      OrderedNativeCountCoordinates.zeroSeed,OrderedNativeCountCoordinates.oneSeed,if_pos hr0]
    have hh := listPair_count K Q μL hQ P t i kind ω hr hk b hb low u hseed 0
    simp only [ho0] at hh
    simpa only [rawOutcome,orderedOutcome,NativeLocalPolicy.Data.finiteCount,if_pos h,
      NativeHighExperiment.sortedPairs,countedPrivateRow] using! hh
  · have hr0 := fun hh => h (hz.mp hh)
    dsimp only [E] at hr0
    simp only [OrderedNativeCountCoordinates.zeroList,OrderedNativeCountCoordinates.oneList,
      OrderedNativeCountCoordinates.zeroSeed,OrderedNativeCountCoordinates.oneSeed,if_neg hr0]
    have hh := listPair_count K Q μL hQ P t i kind ω hr hk b hb low u hseed 1
    simp only [ho1] at hh
    simpa only [rawOutcome,orderedOutcome,NativeLocalPolicy.Data.finiteCount,if_neg h,
      swapPairs,NativeHighExperiment.sortedPairs,Prod.swap_prod_mk,countedPrivateRow] using! hh

end Coordinates
end FCAppendix.Affine.Tail04.OrderedNativePayoffActiveCoordinates
