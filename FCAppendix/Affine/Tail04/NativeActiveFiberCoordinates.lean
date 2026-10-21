import FCAppendix.Affine.Tail04.NativeFiberEnumerations
import FCAppendix.Affine.Tail04.NativeHighExperiment
import FCAppendix.Affine.Tail04.FiberCategoryEquiv

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeActiveFiberCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeMenuReports NativeCountCoordinates NativeDeletedCounts
open NativeFiberEnumerations NativeFocalCoordinates PartialNativeCoordinates
open LocalCoordinates SortedCoordinates PrivateIdentitySort PrivateRowSorting SortedAllNoise
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy OriginalPopulation OriginalValues

section Coordinates
variable {N : ℕ} (E : Observable.Regions) (i : Fin (N+1)) (kind : Fin N → Fin 4)

abbrev commonSize := (rivalSet i kind 1).card
abbrev zeroSize := (rivalSet i kind 2).card
abbrev oneSize := (rivalSet i kind 3).card

def commonIndex : Fin (commonSize i kind) ≃ OriginalFiberProduct.Common kind :=
  (categoryEnumeration i kind 1).trans (FiberCategoryEquiv.common kind).symm
def zeroIndex : Fin (zeroSize i kind) ≃ OriginalFiberProduct.Zero kind :=
  (categoryEnumeration i kind 2).trans (FiberCategoryEquiv.zero kind).symm
def oneIndex : Fin (oneSize i kind) ≃ OriginalFiberProduct.One kind :=
  (categoryEnumeration i kind 3).trans (FiberCategoryEquiv.one kind).symm

def commonRow (r : Fin N → UserDraw 2) : Fin (commonSize i kind) → Icc (1:ℝ) E.U :=
  fun j => OriginalCommonLaw.commonDecode E (r (categoryEnumeration i kind 1 j)).1

def privateRowRaw (k : Fin 4) (r : Fin N → UserDraw 2) :
    Row (rivalSet i kind k).card E.R E.Rp E.H :=
  fun j => decode E (r (categoryEnumeration i kind k j)).1.2.bid

lemma measurable_commonRow : Measurable (commonRow E i kind) :=
  measurable_pi_lambda _ fun j => (OriginalCommonLaw.measurable_commonDecode E).comp
    (measurable_fst.comp (measurable_pi_apply (categoryEnumeration i kind 1 j).val))

lemma measurable_privateRowRaw (k : Fin 4) : Measurable (privateRowRaw E i kind k) :=
  measurable_pi_lambda _ fun j => (measurable_decode E).comp ((measurable_bid 2).comp
    (measurable_fst.snd.comp (measurable_pi_apply (categoryEnumeration i kind k j).val)))

lemma numericalRows_exact {Z : Type*} (r : (Fin N → UserDraw 2)×Z) :
    OriginalFiberProduct.fiberRows kind (commonSize i kind) (zeroSize i kind) (oneSize i kind)
      (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind)
      (fun x : UserDraw 2 => OriginalCommonLaw.commonDecode E x.1)
      (fun x : UserDraw 2 => decode E x.1.2.bid) r=
        ((commonRow E i kind r.1,privateRowRaw E i kind 2 r.1,privateRowRaw E i kind 3 r.1),r.2) := rfl

lemma observedEntry_of_not_absent (x : UserDraw 2) (j : Fin 2)
    (hx : E.localTag (NativePrivatePosterior.observedEntry j x)≠3) :
    NativePrivatePosterior.observedEntry j x=some x.1.2.bid := by
  by_cases hj : j∈firstK x.2 x.1.2.routeCount
  · simp only [NativePrivatePosterior.observedEntry,if_pos hj]
  · exact False.elim (hx (by simp [NativePrivatePosterior.observedEntry,hj,
      Observable.Regions.localTag]))

variable {Seed : Type*} (ω : Background (N+1) 2 Seed)
  (hr : ∀ r,MenuAction E (ω.1 (i.succAbove r)).1.2)
  (hk : rivalKinds E i ω=kind)

include E hr hk in
lemma common_source_entry (j : Fin 2) (q : Fin (commonSize i kind)) (b : ℝ) :
    presentList ω i b j (baselineEmbedding (rivalSet i kind 1) q)=
      some (ω.1 (i.succAbove (categoryEnumeration i kind 1 q))).1.2.bid := by
  rw [←categoryEnumeration_identity i kind 1 q,present_other_observed]
  apply observedEntry_of_not_absent E
  have htag : E.coarseTag (ω.1 (i.succAbove (categoryEnumeration i kind 1 q)))=1 := by
    exact (congrFun hk (categoryEnumeration i kind 1 q)).trans
      (categoryEnumeration i kind 1 q).2
  have ha := (observed_active_tag E _ (hr (categoryEnumeration i kind 1 q)) j).mpr htag
  simpa only [ha] using (by decide : (1:Fin 4)≠3)

include hr hk in
lemma common_source_box (q : Fin (commonSize i kind)) :
    (ω.1 (i.succAbove (categoryEnumeration i kind 1 q))).1.2.bid∈Icc (1:ℝ) E.U := by
  have htag : E.coarseTag (ω.1 (i.succAbove (categoryEnumeration i kind 1 q)))=1 := by
    exact (congrFun hk (categoryEnumeration i kind 1 q)).trans
      (categoryEnumeration i kind 1 q).2
  have ha := (observed_active_tag E _ (hr (categoryEnumeration i kind 1 q)) 0).mpr htag
  have hb := menu_active_box E _ (hr (categoryEnumeration i kind 1 q)) 0 ha
  rw [observedEntry_of_not_absent E _ 0 (by simpa only [ha] using (by decide : (1:Fin 4)≠3))] at hb
  exact hb

include hr hk in
lemma common_source_value (q : Fin (commonSize i kind)) :
    (commonRow E i kind (fun r => ω.1 (i.succAbove r)) q:ℝ)=
      (ω.1 (i.succAbove (categoryEnumeration i kind 1 q))).1.2.bid :=
  OriginalValues.clipToBand_eq 1 E.U E.one_le_U (common_source_box E i kind ω hr hk q)

include E hr hk in
lemma private_source_entry (j : Fin 2)
    (q : Fin (rivalSet i kind (Hybrid.NativeContinuation.upperTag j)).card) (b : ℝ) :
    presentList ω i b j (baselineEmbedding (rivalSet i kind (Hybrid.NativeContinuation.upperTag j)) q)=
      some (ω.1 (i.succAbove (categoryEnumeration i kind (Hybrid.NativeContinuation.upperTag j) q))).1.2.bid := by
  rw [←categoryEnumeration_identity i kind _ q,present_other_observed]
  apply observedEntry_of_not_absent E
  have htag : E.coarseTag (ω.1 (i.succAbove (categoryEnumeration i kind (Hybrid.NativeContinuation.upperTag j) q)))=
      Hybrid.NativeContinuation.upperTag j := by
    exact (congrFun hk (categoryEnumeration i kind (Hybrid.NativeContinuation.upperTag j) q)).trans
      (categoryEnumeration i kind (Hybrid.NativeContinuation.upperTag j) q).2
  have hp := (observed_private_tag E _ (hr (categoryEnumeration i kind (Hybrid.NativeContinuation.upperTag j) q)) j).mpr htag
  simpa only [hp] using (by decide : (2:Fin 4)≠3)

include hr hk in
theorem private_row (j : Fin 2) (b : ℝ) :
    LocalCoordinates.privateRow E (rivalSet i kind (Hybrid.NativeContinuation.upperTag j))
      (presentList ω i b j)=
        sortRow E _ (privateRowRaw E i kind (Hybrid.NativeContinuation.upperTag j)
          (fun r => ω.1 (i.succAbove r))) := by
  rw [PrivateIdentitySort.native_privateRow_eq_sorted]
  congr 1
  funext q
  rw [private_source_entry E i kind ω hr hk j q b]
  rfl

include hr hk in
lemma common_all_box (b : ℝ) (j : Fin 2) :
    ∀ l∈rivalSet i kind 1,entryBid (presentList ω i b j l)∈Icc (1:ℝ) E.U := by
  intro l hl
  obtain ⟨q,hq⟩ := (baseline (rivalSet i kind 1)).surjective ⟨l,hl⟩
  have hv : baselineEmbedding (rivalSet i kind 1) q=l := congrArg Subtype.val hq
  rw [←hv,common_source_entry E i kind ω hr hk j q b]
  exact common_source_box E i kind ω hr hk q

include hr hk in
theorem common_bids (b : ℝ) (j : Fin 2) :
    activeBids E (rivalSet i kind 1) (presentList ω i b j)=
      sortedBox (commonRow E i kind (fun r => ω.1 (i.succAbove r))) := by
  rw [activeBids_eq_sorted_baseline E _ _ (common_all_box E i kind ω hr hk b j)]
  congr 1
  funext q
  apply Subtype.ext
  change entryBid (presentList ω i b j (baselineEmbedding (rivalSet i kind 1) q))=
    (commonRow E i kind (fun r => ω.1 (i.succAbove r)) q:ℝ)
  rw [common_source_entry E i kind ω hr hk j q b]
  exact (common_source_value E i kind ω hr hk q).symm

include hr hk in
lemma active_all_box (b : Icc (1:ℝ) E.U) (j : Fin 2) :
    ∀ l∈insert i (rivalSet i kind 1),entryBid (presentList ω i b j l)∈Icc (1:ℝ) E.U := by
  intro l hl
  rcases Finset.mem_insert.mp hl with rfl | hl
  · simpa only [presentList_self,entryBid] using b.2
  · obtain ⟨q,hq⟩ := (baseline (rivalSet i kind 1)).surjective ⟨l,hl⟩
    have hv : baselineEmbedding (rivalSet i kind 1) q=l := congrArg Subtype.val hq
    rw [←hv,common_source_entry E i kind ω hr hk j q b]
    exact common_source_box E i kind ω hr hk q

lemma sortedBox_cast {a d : ℕ} (h : a=d) {L U : ℝ} (b : Fin d → Icc L U) :
    sortedBox (b ∘ Fin.cast h)=sortedBox b ∘ Fin.cast h := by
  cases h
  rfl

lemma focalRank_cast {a d : ℕ} (h : a=d) (b : Fin d → ℝ) (k : Fin d) :
    focalRank (b ∘ Fin.cast h) (Fin.cast h.symm k)=Fin.cast h.symm (focalRank b k) := by
  cases h
  rfl

include hr hk in
theorem active_bids (b : Icc (1:ℝ) E.U) (j : Fin 2) :
    activeBids E (insert i (rivalSet i kind 1)) (presentList ω i b j)=
      sortedBox (Fin.cons (α:=fun _ => Icc (1:ℝ) E.U) b (commonRow E i kind (fun r => ω.1 (i.succAbove r)))) ∘
        Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind 1)) := by
  let S := rivalSet i kind 1
  let e := focalFirst S i (focal_not_mem_rivalSet i kind 1)
  rw [NativeFiberEnumerations.common_sorted E _ _ e (active_all_box E i kind ω hr hk b j)]
  have hrow : NativeFiberEnumerations.commonRow E (insert i S) (presentList ω i b j) e
      (active_all_box E i kind ω hr hk b j)=
      (Fin.cons (α:=fun _ => Icc (1:ℝ) E.U) b (commonRow E i kind (fun r => ω.1 (i.succAbove r)))) ∘
        Fin.cast (insert_card S i (focal_not_mem_rivalSet i kind 1)) := by
    apply funext
    intro q
    apply Subtype.ext
    have he := congrFun (focalFirst_row S i (focal_not_mem_rivalSet i kind 1)
      (fun l => entryBid (presentList ω i b j l))) q
    change entryBid (presentList ω i b j ((focalFirst S i (focal_not_mem_rivalSet i kind 1)) q).val)=_
    rw [he]
    dsimp only [Function.comp_apply]
    generalize Fin.cast (insert_card S i (focal_not_mem_rivalSet i kind 1)) q=k
    refine Fin.cases ?_ (fun r => ?_) k
    · simp only [Fin.cons_zero,presentList_self,entryBid]
    · simp only [Fin.cons_succ]
      change entryBid (presentList ω i b j (baselineEmbedding (rivalSet i kind 1) r))=_
      rw [common_source_entry E i kind ω hr hk j r b]
      exact (common_source_value E i kind ω hr hk r).symm
  rw [hrow,sortedBox_cast]

include hr hk in
theorem active_rank (b : Icc (1:ℝ) E.U)
    (hb : Function.Injective (fun q =>
      (Fin.cons (α:=fun _ => Icc (1:ℝ) E.U) b (commonRow E i kind (fun r => ω.1 (i.succAbove r))) q:ℝ))) (j : Fin 2) :
    rankFin (insert i (rivalSet i kind 1)) (bidVector (presentList ω i b j))
      ⟨i,Finset.mem_insert_self _ _⟩=
        Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind 1)).symm
          (focalRank (fun q => (Fin.cons (α:=fun _ => Icc (1:ℝ) E.U) b (commonRow E i kind
            (fun r => ω.1 (i.succAbove r))) q:ℝ)) 0) := by
  let S := insert i (rivalSet i kind 1)
  let row := Fin.cons (α:=fun _ => Icc (1:ℝ) E.U) b (commonRow E i kind (fun r => ω.1 (i.succAbove r)))
  let hcard := insert_card _ i (focal_not_mem_rivalSet i kind 1)
  let r := rankFin S (bidVector (presentList ω i b j)) ⟨i,Finset.mem_insert_self _ _⟩
  have hv : (activeBids E S (presentList ω i b j) r:ℝ)=(b:ℝ) := by
    rw [activeBids_exact E S _ (active_all_box E i kind ω hr hk b j) r]
    simp only [r,enumerate_rank,presentList_self,entryBid]
  rw [active_bids E i kind ω hr hk b j] at hv
  have he : permutation (fun q => (row q:ℝ)) (Fin.cast hcard r)=0 := hb (by
    simpa only [row,Function.comp_apply,sortedBox,sorted,Fin.cons_zero] using hv)
  have hrank : Fin.cast hcard r=focalRank (fun q => (row q:ℝ)) 0 := by
    apply (permutation (fun q => (row q:ℝ))).injective
    simpa only [focalRank,Equiv.apply_symm_apply] using he
  apply Fin.ext
  simpa only [Fin.val_cast] using!
    congrArg (fun q : Fin ((rivalSet i kind 1).card+1) => q.val) hrank

end Coordinates

section NativeTerminal
variable {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c)
  (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hQ : ∀ A,K.publicChoice A=PublicScenario.localChoice K.E Q μL A)
  (P : ValueParameters) (t : ℝ)
  (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (hpolicy : Γ.policy=K.completedPolicy)
  (i : Fin (N+1)) (kind : Fin N → Fin 4)
  (ω : Sample (N+1) 2 NativeLocalPolicy.Seed)
  (hr : ∀ l,l≠i → sourceBands P K.E t (ω.1.1 l).1)
  (hk : rivalKinds K.E i ω.1=kind)

include hQ P t hpolicy hr hk in
theorem active_count (b : Icc (1:ℝ) K.E.U)
    (hb : Function.Injective (fun q =>
      (Fin.cons (α:=fun _ => Icc (1:ℝ) K.E.U) b (commonRow K.E i kind (fun r => ω.1.1 (i.succAbove r))) q:ℝ)))
    (lowPresent : Bool) (u : unitInterval)
    (hseed : Hybrid.seedOnList μL (K.E.roleList 0 (presentList ω.1 i b 0))=
      if lowPresent then some u else none) :
    focalCount Γ i (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2) ω=
      NativeHighExperiment.outcome K (K.finiteCount (rivalSet i kind 2))
        (K.finiteCount (rivalSet i kind 3)) Q
        (Fin.cons (α:=fun _ => Icc (1:ℝ) K.E.U) b (commonRow K.E i kind (fun r => ω.1.1 (i.succAbove r)))) 0 lowPresent
        (u,((privateRowRaw K.E i kind 2 (fun r => ω.1.1 (i.succAbove r)),
          privateRowRaw K.E i kind 3 (fun r => ω.1.1 (i.succAbove r))),(ω.1.2,ω.2))) := by
  let E:=K.E
  let C:=rivalSet i kind 1
  let H0:=K.finiteCount (rivalSet i kind 2)
  let H1:=K.finiteCount (rivalSet i kind 3)
  let a:=RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2
  let L : Fin 2 → LocalList (N+1):=fun j => presentList ω.1 i b j
  let raw:=Fin.cons (α:=fun _ => Icc (1:ℝ) K.E.U) b (commonRow E i kind (fun r => ω.1.1 (i.succAbove r)))
  let hc:=insert_card C i (focal_not_mem_rivalSet i kind 1)
  let raw' := raw ∘ Fin.cast hc
  let j0 : Fin (insert i C).card:=Fin.cast hc.symm 0
  have hm (r : Fin N) : MenuAction E (ω.1.1 (i.succAbove r)).1.2 :=
    source_menu E P t _ (hr _ (Fin.succAbove_ne i r))
  have ho (j : Fin 2) : observe (deviated i a ω) j=L j :=
    observe_deviated_of_mem i a ω j (by simp [a,RawRoutes.action,Hybrid.firstK_full_two])
  have hkE : rivalKinds E i ω.1=kind := hk
  have hids (j : Fin 2) : ids E 0 (L j)=rivalSet i kind 0 ∧
      ids E 1 (L j)=insert i (rivalSet i kind 1) ∧
      ids E 2 (L j)=rivalSet i kind (Hybrid.NativeContinuation.upperTag j) ∧
      ids E 3 (L j)=rivalSet i kind (Hybrid.NativeContinuation.upperTag (Hybrid.otherProposer j)) := by
    simpa only [L,hkE] using! PartialNativeCoordinates.active_ids E i ω.1 hm b j
  have hu0 : Hybrid.NativeContinuation.upperTag (0:Fin 2)=(2:Fin 4) := by decide
  have hu1 : Hybrid.NativeContinuation.upperTag (1:Fin 2)=(3:Fin 4) := by decide
  have ho0 : Hybrid.otherProposer (0:Fin 2)=(1:Fin 2) := by decide
  have h0 : ids E 1 (L 0)=insert i C ∧ ids E 2 (L 0)=rivalSet i kind 2 ∧
      ids E 3 (L 0)=rivalSet i kind 3 := by
    simpa only [L,C,ho0,hu0,hu1] using (hids 0).2
  have h1 : ids E 2 (L 1)=rivalSet i kind 3 := by
    simpa only [L,hu1] using (hids 1).2.2.1
  have hs : activeBids E (insert i C) (L 0)=sortedBox raw' := by
    rw [sortedBox_cast]
    exact active_bids E i kind ω.1 hm hk b 0
  have hj : rankFin (insert i C) (bidVector (L 0)) ⟨i,Finset.mem_insert_self _ _⟩=
      focalRank (fun q => (raw' q:ℝ)) j0 := by
    change _=focalRank ((fun q => (raw q:ℝ)) ∘ Fin.cast hc) (Fin.cast hc.symm 0)
    rw [focalRank_cast]
    exact active_rank E i kind ω.1 hm hk b hb 0
  have hp : K.parameter (insert i C) H0 H1 (L 0)=
      let q := NativeHighExperiment.choice K H0 H1 Q raw' lowPresent u
      ((q.1,sortedBox raw'),(K.signalLaw H0,q.2)) := by
    unfold NativeLocalPolicy.Data.parameter
    rw [hs,hQ]
    dsimp only [PublicScenario.localChoice]
    rw [hseed]
    cases lowPresent <;> rfl
  have hp0 := private_row E i kind ω.1 hm hk 0 (b:ℝ)
  have hp1 := private_row E i kind ω.1 hm hk 1 (b:ℝ)
  rw [hu0] at hp0
  rw [hu1] at hp1
  dsimp only [a,L] at ho
  dsimp only [E,L] at h0 hj hp hp0 hp1
  have hn := NativeMenuReports.native_active_focal_count K P t Γ hpolicy i b ω hr
  calc
    _=NativeHighExperiment.outcome K H0 H1 Q raw' j0 lowPresent
        (u,((privateRowRaw E i kind 2 (fun r => ω.1.1 (i.succAbove r)),
          privateRowRaw E i kind 3 (fun r => ω.1.1 (i.succAbove r))),(ω.1.2,ω.2))) := by
      have transport (A0 F0 F1 : Finset (Fin (N+1)))
          (Lzero Lone : LocalList (N+1)) (hi0 : i∈A0)
          (hA : A0=insert i C) (hF0 : F0=rivalSet i kind 2)
          (hF1 : F1=rivalSet i kind 3) (hL0 : Lzero=L 0) (hL1 : Lone=L 1) :
          originalPairCount
            (K.zeroSampler A0.card (K.finiteCount F0) (K.finiteCount F1))
            (K.oneSampler A0.card (K.finiteCount F0) (K.finiteCount F1))
            (K.parameter A0 (K.finiteCount F0) (K.finiteCount F1) Lzero)
            (Sum.inl (rankFin A0 (bidVector Lzero) ⟨i,hi0⟩))
            (Sum.inl (rankFin A0 (bidVector Lzero) ⟨i,hi0⟩))
            ((LocalCoordinates.privateRow K.E F0 Lzero,(ω.1.2 0).1),
              (LocalCoordinates.privateRow K.E F1 Lone,(ω.1.2 1).1))=
            NativeHighExperiment.outcome K H0 H1 Q raw' j0 lowPresent
              (u,((privateRowRaw E i kind 2 (fun r => ω.1.1 (i.succAbove r)),
                privateRowRaw E i kind 3 (fun r => ω.1.1 (i.succAbove r))),(ω.1.2,ω.2))) := by
        subst A0
        subst F0
        subst F1
        subst Lzero
        subst Lone
        rw [hj,hp,hp0,hp1]
        rfl
      exact hn.trans (transport _ _ _ _ _ _
        ((congrArg (ids K.E 1) (ho 0)).trans h0.1)
        ((congrArg (ids K.E 2) (ho 0)).trans h0.2.1)
        ((congrArg (ids K.E 3) (ho 0)).trans h0.2.2)
        (ho 0) (ho 1))
    _=_ := NativeHighExperiment.outcome_cast K H0 H1 Q hc raw 0 lowPresent _

end NativeTerminal
end FCAppendix.Affine.Tail04.NativeActiveFiberCoordinates
