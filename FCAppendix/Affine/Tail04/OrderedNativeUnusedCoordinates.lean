import FCAppendix.Affine.Tail04.NativeUnusedCoordinates
import FCAppendix.Affine.Tail04.OrderedNativeCountCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeUnusedCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeUnusedCoordinates NativeObservationPair NativeCountCoordinates
open NativeMenuReports NativeFocalCoordinates PartialNativeCoordinates NativeActiveFiberCoordinates
open LocalCoordinates SortedCoordinates JoinedHighPolicy LocalHighCommon Hybrid
open EqualPrivateSignal EqualPrivateUpper PrivateRowSorting NativeHighExperiment

def countedPrivateRow {N c : ℕ} (D : Data (N+1) c) (i : Fin (N+1))
    (kind : Fin N→Fin 4) (tag : Fin 4) (r : Fin N→UserDraw 2) :
    Row (D.finiteCount (rivalSet i kind tag)).val D.E.R D.E.Rp D.E.H :=
  privateRowRaw D.E i kind tag r

variable {N c : ℕ} (D : Data (N+1) c) (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hpublic : ∀ n z,D.publicChoice n z=PublicScenario.localChoice D.E Q μL n z)
  (i : Fin (N+1)) (kind : Fin N→Fin 4)
  (ω : Background (N+1) 2 Seed)
  (hr : ∀r : Fin N,MenuAction D.E (ω.1 (i.succAbove r)).1.2)
  (hk : rivalKinds D.E i ω=kind)
  (b : ℝ) (hb : D.E.localTag (some b)=1) (hbo : b∉Icc (1:ℝ) D.E.U)

include hpublic hr hk in

lemma raw_parameter (H0 H1 : Fin ((N+1)+1)) (side : Fin 2) (u : unitInterval)
    (hu : seedOnList μL (D.E.roleList 0 (presentList ω i b side))=some u) :
    D.parameter (rivalSet i kind 1) H0 H1 (presentList ω i b side)=
      PartialNativePublicWeight.drawnParameter D Q (rivalSet i kind 1).card H0 H1
        (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind (fun r => ω.1 (i.succAbove r)))) u := by
  simp only [Data.parameter,hpublic,PublicScenario.localChoice,hu,
    PartialNativePublicWeight.drawnParameter]
  rw [common_bids D.E i kind ω hr hk b side]

include hr hb in
lemma compatible : D.E.Compatible (presentList ω i b 0) (presentList ω i b 1) := by
  intro l
  by_cases hl : l=i
  · subst l
    rw [presentList_self,presentList_self]
    exact Or.inl ⟨rfl,Or.inr hb⟩
  · obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
    have ho0 : otherProposer 0=(1:Fin 2) := by decide
    simpa only [present_other_observed,ho0] using!
      NativeMenuReports.menu_compatible D.E (ω.1 (i.succAbove r)) (hr r) 0

include hpublic hr hk hb hbo in

theorem sampler_pair (j : Fin 2) (u : unitInterval)
    (hseed : ∀s : Fin 2,seedOnList μL (D.E.roleList 0 (presentList ω i b s))=some u)
    (huse : D.FocalUse (rivalSet i kind 1).card
      (D.finiteCount (rivalSet i kind (NativeContinuation.upperTag j)))
      (D.finiteCount (rivalSet i kind (NativeContinuation.upperTag (otherProposer j))))
      (PartialNativePublicWeight.drawnParameter D Q (rivalSet i kind 1).card
        (D.finiteCount (rivalSet i kind (NativeContinuation.upperTag j)))
        (D.finiteCount (rivalSet i kind (NativeContinuation.upperTag (otherProposer j))))
        (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind (fun r => ω.1 (i.succAbove r)))) u)) :
    let H0:=D.finiteCount (rivalSet i kind (NativeContinuation.upperTag j))
    let H1:=D.finiteCount (rivalSet i kind (NativeContinuation.upperTag (otherProposer j)))
    let p:=PartialNativePublicWeight.drawnParameter D Q (rivalSet i kind 1).card H0 H1 (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind (fun r => ω.1 (i.succAbove r)))) u
    (∀s : Seed,i∈(D.completedPolicy 0 (presentList ω i b j) s).val ↔
      none∈D.zeroFocal (rivalSet i kind 1).card H0 H1 ((p,b),
        sortRow D.E H0.val (countedPrivateRow D i kind (NativeContinuation.upperTag j)
          (fun r => ω.1 (i.succAbove r)))) s.1) ∧
    (∀s : Seed,i∈(D.completedPolicy 1 (presentList ω i b (otherProposer j)) s).val ↔
      none∈D.oneFocal (rivalSet i kind 1).card H0 H1 ((p,b),
        sortRow D.E H1.val (countedPrivateRow D i kind (NativeContinuation.upperTag (otherProposer j))
          (fun r => ω.1 (i.succAbove r)))) s.1) := by
  dsimp only
  have hs0 := raw_ids D.E i ω hr b hb j
  have hs1 := raw_ids D.E i ω hr b hb (otherProposer j)
  have hA0 := old_common_ids D.E i ω hr b hb j
  have hA1 := old_common_ids D.E i ω hr b hb (otherProposer j)
  simp only [hk,otherProposer_other] at hs0 hs1 hA0 hA1
  have hoff0 := offCommon_singleton D.E i ω hr b hb D rfl hbo j
  have hoff1 := offCommon_singleton D.E i ω hr b hb D rfl hbo (otherProposer j)
  have hu0 : D.UseFocal 0 i (presentList ω i b j) := by
    simp only [Data.UseFocal,hoff0,true_and]
    rw [NativeRawFactor.focalKey_self D i (presentList ω i b j)]
    simp only [Data.FocalUseAtKey,if_true]
    erw [hA0,hs0.2.2.1,hs0.2.2.2,
      raw_parameter D Q μL hpublic i kind ω hr hk b _ _ j u (hseed j)]
    exact huse
  have hu1 : D.UseFocal 1 i (presentList ω i b (otherProposer j)) := by
    simp only [Data.UseFocal,hoff1,true_and]
    rw [NativeRawFactor.focalKey_self D i (presentList ω i b (otherProposer j))]
    simp only [Data.FocalUseAtKey,if_neg (by decide : (1:Fin 2)≠0)]
    erw [hA1,hs1.2.2.1,hs1.2.2.2,
      raw_parameter D Q μL hpublic i kind ω hr hk b _ _ (otherProposer j) u
        (hseed (otherProposer j))]
    exact huse
  constructor
  · intro s
    have h := completed_zero D i (presentList ω i b j) hu0 s
    erw [hA0,hs0.2.2.1,hs0.2.2.2,
      raw_parameter D Q μL hpublic i kind ω hr hk b _ _ j u (hseed j),
      private_row D.E i kind ω hr hk j b] at h
    simpa only [presentList_self,entryBid] using! h
  · intro s
    have h := completed_one D i (presentList ω i b (otherProposer j)) hu1 s
    erw [hA1,hs1.2.2.1,hs1.2.2.2,
      raw_parameter D Q μL hpublic i kind ω hr hk b _ _ (otherProposer j) u
        (hseed (otherProposer j)),
      private_row D.E i kind ω hr hk (otherProposer j) b] at h
    simpa only [presentList_self,entryBid] using! h

end FCAppendix.Affine.Tail04.OrderedNativeUnusedCoordinates
