import FCAppendix.Affine.Tail04.PartialNativePublicWeight
import FCAppendix.Affine.Tail04.NativeFocalFactor

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeUnusedCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeObservationPair NativePrivatePosterior NativeMenuReports
open PartialNativeCoordinates NativeActiveFiberCoordinates NativeFocalFactor
open LocalCoordinates SortedCoordinates JoinedHighPolicy LocalHighCommon Hybrid
open EqualPrivateSignal EqualPrivateUpper
open scoped BigOperators

section OriginalIds
variable {N c : ℕ} {Seed : Type*} (E : Observable.Regions)
  (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
  (hr : ∀ r : Fin N,MenuAction E (ω.1 (i.succAbove r)).1.2)
  (b : ℝ) (hb : E.localTag (some b)=1)

include hr hb in
theorem raw_ids (j : Fin 2) :
    ids E 0 (presentList ω i b j)=rivalSet i (rivalKinds E i ω) 0 ∧
    ids E 1 (presentList ω i b j)=insert i (rivalSet i (rivalKinds E i ω) 1) ∧
    ids E 2 (presentList ω i b j)=
      rivalSet i (rivalKinds E i ω) (NativeContinuation.upperTag j) ∧
    ids E 3 (presentList ω i b j)=
      rivalSet i (rivalKinds E i ω) (NativeContinuation.upperTag (otherProposer j)) := by
  have hf (k : Fin 4) := focal_not_mem_rivalSet i (rivalKinds E i ω) k
  refine ⟨?_,?_,?_,?_⟩ <;> ext l <;> by_cases hl : l=i
  all_goals try { subst l; simp [ids,presentList_self,hb,hf] }
  all_goals obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_low_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      Finset.mem_insert,Fin.succAbove_ne,false_or,mem_rivalSet_succAbove,rivalKinds] using
      observed_active_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_private_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_absent_tag E _ (hr r) j

include hr hb in
lemma old_common_ids (j : Fin 2) :
    (ids E 1 (presentList ω i b j)).erase i=rivalSet i (rivalKinds E i ω) 1 := by
  rw [(raw_ids E i ω hr b hb j).2.1]
  exact Finset.erase_insert (focal_not_mem_rivalSet i _ 1)

include hr hb in
lemma offCommon_singleton (D : Data (N+1) c) (hE : D.E=E)
    (hbo : b∉Icc (1:ℝ) E.U) (j : Fin 2) :
    D.offCommon (presentList ω i b j)={i} := by
  ext l
  by_cases hl : l=i
  · subst l
    simp only [Data.offCommon,Finset.mem_filter,Finset.mem_univ,
      hE,presentList_self,hb,entryBid,hbo,not_false_eq_true,and_self,Finset.mem_singleton]
  · constructor
    · intro hh
      obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
      have hx := Finset.mem_filter.mp hh
      rw [hE,present_other_observed] at hx
      exact False.elim (hx.2.2 (menu_active_box E _ (hr r) j hx.2.1))
    · intro hh
      exact False.elim (hl (Finset.mem_singleton.mp hh))

include hr hb in
lemma raw_low_seed_enumeration (j : Fin 2) (μL : Measure ℝ)
    (n : ℕ) (e : Fin (n+1)≃{r : Fin N // rivalKinds E i ω r=0}) :
    seedOnList μL (E.roleList 0 (presentList ω i b j))=
      some (conditionalMinimumSeed μL n
        (fun l => (ω.1 (i.succAbove (e l).val)).1.2.bid)) := by
  let b1 : Icc (1:ℝ) E.U := ⟨1,le_rfl,E.one_le_U⟩
  have hb0 : E.localTag (some b)≠0 := by rw [hb];decide
  have hb10 : E.localTag (some (b1:ℝ))≠0 := by rw [tag_common E b1.2];decide
  rw [low_roleList_change_nonlow E i ω b b1 hb0 hb10 j]
  exact active_low_seed_enumeration E i ω hr b1 j μL n e

include hr hb in
lemma raw_no_low_seed (j : Fin 2) (μL : Measure ℝ)
    (hl : ∀ r : Fin N,rivalKinds E i ω r≠0) :
    seedOnList μL (E.roleList 0 (presentList ω i b j))=none := by
  let b1 : Icc (1:ℝ) E.U := ⟨1,le_rfl,E.one_le_U⟩
  have hb0 : E.localTag (some b)≠0 := by rw [hb];decide
  have hb10 : E.localTag (some (b1:ℝ))≠0 := by rw [tag_common E b1.2];decide
  rw [low_roleList_change_nonlow E i ω b b1 hb0 hb10 j]
  exact active_no_low_seed E i ω hr b1 j μL hl

end OriginalIds

section LocalMembership
variable {m c : ℕ} (D : Data m c)

theorem completed_zero (i : Fin m) (L : LocalList m)
    (hu : D.UseFocal 0 i L) (u : Seed) :
    i∈(D.completedPolicy 0 L u).val ↔
      none∈D.zeroFocal ((ids D.E 1 L).erase i).card
        (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L))
        ((D.parameter ((ids D.E 1 L).erase i) (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)) L,entryBid (L i)),
            privateRow D.E (ids D.E 2 L) L) u.1 := by
  have hAi := focal_active D 0 i L hu
  have hiP : i∉ids D.E 2 L := fun hP =>
    Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (1:Fin 4)≠2) L) hAi hP
  have hAP : Disjoint ((ids D.E 1 L).erase i) (ids D.E 2 L) :=
    (ids_disjoint D.E (by decide : (1:Fin 4)≠2) L).mono_left (Finset.erase_subset _ _)
  have hi : i∉(ids D.E 1 L).erase i∪ids D.E 2 L := by simp [hiP]
  have huse := hu.2
  rw [NativeRawFactor.focalKey_self D] at huse
  rw [D.completed_focal 0 i L hu u]
  change i∈D.focalSelection 0 i L u.1 ↔ _
  rw [Data.focalSelection,if_pos hu,NativeRawFactor.focalKey_self D]
  simp only [Data.focalAtKey,dif_pos hAP,dif_pos hi,if_pos huse,if_true,
    FocalIdentity.focal_mem_transport]
  rfl

theorem completed_one (i : Fin m) (L : LocalList m)
    (hu : D.UseFocal 1 i L) (u : Seed) :
    i∈(D.completedPolicy 1 L u).val ↔
      none∈D.oneFocal ((ids D.E 1 L).erase i).card
        (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L))
        ((D.parameter ((ids D.E 1 L).erase i) (D.finiteCount (ids D.E 3 L))
          (D.finiteCount (ids D.E 2 L)) L,entryBid (L i)),
            privateRow D.E (ids D.E 2 L) L) u.1 := by
  have hAi := focal_active D 1 i L hu
  have hiP : i∉ids D.E 2 L := fun hP =>
    Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (1:Fin 4)≠2) L) hAi hP
  have hAP : Disjoint ((ids D.E 1 L).erase i) (ids D.E 2 L) :=
    (ids_disjoint D.E (by decide : (1:Fin 4)≠2) L).mono_left (Finset.erase_subset _ _)
  have hi : i∉(ids D.E 1 L).erase i∪ids D.E 2 L := by simp [hiP]
  have huse := hu.2
  rw [NativeRawFactor.focalKey_self D] at huse
  rw [D.completed_focal 1 i L hu u]
  change i∈D.focalSelection 1 i L u.1 ↔ _
  rw [Data.focalSelection,if_pos hu,NativeRawFactor.focalKey_self D]
  simp only [Data.focalAtKey,dif_pos hAP,dif_pos hi,if_pos huse,
    if_neg (by decide : (1:Fin 2)≠0),FocalIdentity.focal_mem_transport]
  rfl

end LocalMembership

section OriginalPublic
variable {N c : ℕ} (D : Data (N+1) c) (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hpublic : ∀ n z,D.publicChoice n z=PublicScenario.localChoice D.E Q μL n z)
  (i : Fin (N+1)) (kind : Fin N→ Fin 4)
  (ω : Background (N+1) 2 Seed)
  (hr : ∀ r : Fin N,MenuAction D.E (ω.1 (i.succAbove r)).1.2)
  (hk : rivalKinds D.E i ω=kind)
  (b : ℝ) (hb : D.E.localTag (some b)=1) (hbo : b∉Icc (1:ℝ) D.E.U)

include hpublic hr hk in
lemma raw_parameter (side : Fin 2) (u : unitInterval)
    (hu : seedOnList μL (D.E.roleList 0 (presentList ω i b side))=some u) :
    D.parameter (rivalSet i kind 1) (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3)) (presentList ω i b side)=
      PartialNativePublicWeight.drawnParameter D Q (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3)) (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind (fun r => ω.1 (i.succAbove r)))) u := by
  simp only [Data.parameter,hpublic,PublicScenario.localChoice,hu,
    PartialNativePublicWeight.drawnParameter]
  rw [common_bids D.E i kind ω hr hk b side]

include hpublic hr hk hb hbo in
lemma raw_use_zero (u : unitInterval)
    (hu : seedOnList μL (D.E.roleList 0 (presentList ω i b 0))=some u) :
    D.UseFocal 0 i (presentList ω i b 0) ↔
      D.FocalUse (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3))
        (PartialNativePublicWeight.drawnParameter D Q (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3)) (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind (fun r => ω.1 (i.succAbove r)))) u) := by
  have hs := raw_ids D.E i ω hr b hb 0
  have hA := old_common_ids D.E i ω hr b hb 0
  simp only [hk] at hs hA
  have hoff := offCommon_singleton D.E i ω hr b hb D rfl hbo 0
  have hu0 : NativeContinuation.upperTag 0=(2:Fin 4) := by decide
  have hu1 : NativeContinuation.upperTag 1=(3:Fin 4) := by decide
  have ho : otherProposer 0=(1:Fin 2) := by decide
  simp only [ho,hu0,hu1] at hs
  simp only [Data.UseFocal,hoff,true_and]
  rw [NativeRawFactor.focalKey_self D i (presentList ω i b 0)]
  simp only [Data.FocalUseAtKey,if_true]
  erw [hA,hs.2.2.1,hs.2.2.2,
    raw_parameter D Q μL hpublic i kind ω hr hk b 0 u hu]

include hpublic hr hk hb hbo in
lemma raw_use_one (u : unitInterval)
    (hu : seedOnList μL (D.E.roleList 0 (presentList ω i b 1))=some u) :
    D.UseFocal 1 i (presentList ω i b 1) ↔
      D.FocalUse (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3))
        (PartialNativePublicWeight.drawnParameter D Q (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3)) (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind (fun r => ω.1 (i.succAbove r)))) u) := by
  have hs := raw_ids D.E i ω hr b hb 1
  have hA := old_common_ids D.E i ω hr b hb 1
  simp only [hk] at hs hA
  have hoff := offCommon_singleton D.E i ω hr b hb D rfl hbo 1
  have hu0 : NativeContinuation.upperTag 0=(2:Fin 4) := by decide
  have hu1 : NativeContinuation.upperTag 1=(3:Fin 4) := by decide
  have ho : otherProposer 1=(0:Fin 2) := by decide
  simp only [ho,hu0,hu1] at hs
  simp only [Data.UseFocal,hoff,true_and]
  rw [NativeRawFactor.focalKey_self D i (presentList ω i b 1)]
  simp only [Data.FocalUseAtKey,if_neg (by decide : (1:Fin 2)≠0)]
  erw [hA,hs.2.2.1,hs.2.2.2,
    raw_parameter D Q μL hpublic i kind ω hr hk b 1 u hu]

include hpublic hr hk hb hbo in
theorem actual_sampler_pair (u : unitInterval)
    (hseed : ∀ j : Fin 2,seedOnList μL (D.E.roleList 0 (presentList ω i b j))=some u)
    (huse : D.FocalUse (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3))
      (PartialNativePublicWeight.drawnParameter D Q (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3)) (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind (fun r => ω.1 (i.succAbove r)))) u)) :
    let p:=PartialNativePublicWeight.drawnParameter D Q (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3)) (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind (fun r => ω.1 (i.succAbove r)))) u
    (∀ s : Seed,i∈(D.completedPolicy 0 (presentList ω i b 0) s).val ↔
      none∈D.zeroFocal (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3)) ((p,b),
        PrivateRowSorting.sortRow D.E (D.finiteCount (rivalSet i kind 2)).val (privateRowRaw D.E i kind 2
          (fun r => ω.1 (i.succAbove r)))) s.1) ∧
    (∀ s : Seed,i∈(D.completedPolicy 1 (presentList ω i b 1) s).val ↔
      none∈D.oneFocal (rivalSet i kind 1).card (D.finiteCount (rivalSet i kind 2)) (D.finiteCount (rivalSet i kind 3)) ((p,b),
        PrivateRowSorting.sortRow D.E (D.finiteCount (rivalSet i kind 3)).val (privateRowRaw D.E i kind 3
          (fun r => ω.1 (i.succAbove r)))) s.1) := by
  dsimp only
  have hz := (raw_use_zero D Q μL hpublic i kind ω hr hk b hb hbo u (hseed 0)).mpr huse
  have ho := (raw_use_one D Q μL hpublic i kind ω hr hk b hb hbo u (hseed 1)).mpr huse
  have hu0 : NativeContinuation.upperTag 0=(2:Fin 4) := by decide
  have hu1 : NativeContinuation.upperTag 1=(3:Fin 4) := by decide
  have ho0 : otherProposer 0=(1:Fin 2) := by decide
  have ho1 : otherProposer 1=(0:Fin 2) := by decide
  constructor
  · intro s
    have h := completed_zero D i (presentList ω i b 0) hz s
    have hs := raw_ids D.E i ω hr b hb 0
    have hA := old_common_ids D.E i ω hr b hb 0
    simp only [hk] at hs hA
    simp only [ho0,hu0,hu1] at hs
    erw [hA,hs.2.2.1,hs.2.2.2,
      raw_parameter D Q μL hpublic i kind ω hr hk b 0 u (hseed 0),
      private_row D.E i kind ω hr hk 0 b] at h
    simpa only [presentList_self,entryBid] using! h
  · intro s
    have h := completed_one D i (presentList ω i b 1) ho s
    have hs := raw_ids D.E i ω hr b hb 1
    have hA := old_common_ids D.E i ω hr b hb 1
    simp only [hk] at hs hA
    simp only [ho1,hu0,hu1] at hs
    erw [hA,hs.2.2.1,hs.2.2.2,
      raw_parameter D Q μL hpublic i kind ω hr hk b 1 u (hseed 1),
      private_row D.E i kind ω hr hk 1 b] at h
    simpa only [presentList_self,entryBid] using! h

end OriginalPublic
end FCAppendix.Affine.Tail04.NativeUnusedCoordinates
