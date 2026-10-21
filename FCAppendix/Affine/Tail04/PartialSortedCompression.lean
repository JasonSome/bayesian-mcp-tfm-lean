import FCAppendix.Affine.Tail04.PartialNativePublicWeight
import FCAppendix.Affine.Tail04.SourceMenuError
import FCAppendix.Affine.Tail04.PublicWeightLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialSortedCompression
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open MenuError NativeTypicalCount EqualPrivateSignal Hybrid
open NativeLocalPolicy NativeMenuReports NativeActiveFiberCoordinates
open NativeFiberEnumerations PartialNativeCoordinates PartialNativePublicWeight
open OriginalFlagCompression OriginalNoiseProduct SourceMenuError
open scoped BigOperators

section Coordinates
variable {N c : ℕ} (E : Observable.Regions) (i : Fin (N+1))
  (kind : Fin N→ Fin 4) (r : Fin N→ UserDraw 2)
  (hk : ∀ j,E.coarseTag (r j)=kind j)

def categoryActiveEquiv : {j : Fin N // kind j=1}≃
    Active (fun j : Fin N => categoryFlag E 1 (r j)) where
  toFun j := ⟨j.val,by simp only [categoryFlag,hk,j.property,if_true]⟩
  invFun j := ⟨j.val,by
    by_contra h
    have hj := j.property
    simp only [categoryFlag,hk,if_neg h] at hj
    exact Bool.noConfusion hj⟩
  left_inv j := Subtype.ext rfl
  right_inv j := Subtype.ext rfl

def originalActiveEquiv : Fin (commonSize i kind)≃
    Active (fun j : Fin N => categoryFlag E 1 (r j)) :=
  (categoryEnumeration i kind 1).trans (categoryActiveEquiv E kind r hk)

def sortedActiveEquiv : Fin (commonSize i kind)≃
    Active (fun j : Fin N => categoryFlag E 1 (r j)) :=
  (PrivateRowSorting.permutation (fun j => (commonRow E i kind r j:ℝ))).trans
    (originalActiveEquiv E i kind r hk)

include hk in
lemma commonSize_eq_original :
    commonSize i kind=privateCount N (fun _ : Unit => fun j => (r j,(0:unitInterval)))
      (categoryFlag E 1) () := by
  exact (active_card _ (originalActiveEquiv E i kind r hk)).symm

include hk in
lemma category_count_eq_original (k : Fin 4) (z : Fin N→ unitInterval) :
    (rivalSet i kind k).card=
      privateCount N (fun _ : Unit => zipRow N (r,z)) (categoryFlag E k) () := by
  rw [rivalSet_card_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
  unfold privateCount boolCount
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : kind j=k <;> simp [zipRow,categoryFlag,hk,h]

include hk in
lemma private_tuple_eq_original (D : Data (N+1) c)
    (z : Fin N→ unitInterval) (side j : Fin 2) :
    (partialPrivateFin D i kind side j).val=
      partialPrivateCount N (fun _ : Unit => zipRow N (r,z))
        (categoryFlag E (NativeContinuation.upperTag j)) side j () := by
  simp only [partialPrivateFin,partialPrivateCount]
  congr 1
  exact category_count_eq_original E i kind r hk _ z

lemma menu_active_box (x : UserDraw 2) (hx : MenuAction E x.1.2)
    (ha : categoryFlag E 1 x=true) : nativeBid x∈Icc (1:ℝ) E.U := by
  have ht : E.coarseTag x=1 := by
    by_contra h
    simp [categoryFlag,h] at ha
  have hl := (observed_active_tag E x hx 0).mpr ht
  have hb := NativeMenuReports.menu_active_box E x hx 0 hl
  rw [NativeActiveFiberCoordinates.observedEntry_of_not_absent E x 0
    (by simpa only [hl] using (by decide : (1:Fin 4)≠3))] at hb
  exact hb

variable (hr : ∀ j,MenuAction E (r j).1.2)

include hk hr in
lemma common_value (j : Fin (commonSize i kind)) :
    (commonRow E i kind r j:ℝ)=nativeBid (r (categoryEnumeration i kind 1 j).val) := by
  apply OriginalValues.clipToBand_eq 1 E.U E.one_le_U
  apply menu_active_box E _ (hr _)
  simp only [categoryFlag,hk,(categoryEnumeration i kind 1 j).property,if_true]

include hr in
lemma sorted_values :
    TypicalGuard.bids (SortedAllNoise.sortedBox (commonRow E i kind r))=
      compressedBids (fun j : Fin N => categoryFlag E 1 (r j))
        (sortedActiveEquiv E i kind r hk) (fun j => nativeBid (r j)) := by
  funext j
  change (commonRow E i kind r
      (PrivateRowSorting.permutation (fun j => (commonRow E i kind r j:ℝ)) j):ℝ)=_
  exact common_value E i kind r hk hr _

end Coordinates

section PositiveCount
variable {X Ω : Type*} {N : ℕ} (row : Ω→ Fin N→ X×unitInterval)
  (target : Ω→ Fin (N+1)) (active private0 private1 : X→ Bool)
  (p : X→ unitInterval) (bid : X→ℝ)
  (ξ share ρ B R Rp width : ℝ) (hshare : share∈Icc (0:ℝ) 1)
  (reg : Bool) (side : Fin 2) (x : Ω)

lemma active_positive_of_weight_one
    (hw : partialGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width hshare reg side x=1) :
    0< privateCount N row active x := by
  by_contra h
  have hA : privateCount N row active x=0 := Nat.eq_zero_of_not_pos h
  have hM : flaggedMixedCount N row target active p false x=0 :=
    Nat.eq_zero_of_le_zero (hA ▸ partial_mixed_le_active N row target active p x)
  simp only [partialGuardWeight,scalarSourceWeight,hM,TypicalGuardStatistics.weight,
    TypicalGuardStatistics.Structural,lt_self_iff_false,and_false,if_false] at hw
  norm_num at hw

end PositiveCount

section Scalar
variable {N c : ℕ} (D : Data (N+1) c) (Q : PublicScenario.Data)
  (hQc : Q.c=c) (hQξ : Q.ξ=D.ξ)
  (hQν : ∀ H : Fin (N+2),Q.marksLaw H.val=D.marksLaw H)
  (hc : c=iidCapacity (99/200) N)
  (P : ValueParameters) (t : ℝ) (ht : P.M≤ t)
  (hB0 : Q.B0=Central.B D.ξ)
  (he0 : ∀ reg,PublicScenario.e0 Q reg=SourceMenuPopulation.baseFlag P reg)
  (hmean : ∀ reg (H : Fin (N+2)),
    privateMean H.val reg (D.marksLaw H)=SourceMenuPopulation.keptShare P t reg*H.val)
  (i : Fin (N+1)) (kind : Fin N→ Fin 4) (r : Fin N→ UserDraw 2)
  (hk : ∀ j,D.E.coarseTag (r j)=kind j)
  (hr : ∀ j,MenuAction D.E (r j).1.2)

include hB0 he0 hr in
lemma source_flags (reg : Bool) (j : Fin (commonSize i kind)) :
    sourceFlagProb (PublicScenario.e0 Q reg) Q.B0
      (TypicalGuard.bids (SortedAllNoise.sortedBox (commonRow D.E i kind r))) j=
        (nativeFlag P D.ξ reg (r (sortedActiveEquiv D.E i kind r hk j).val):ℝ) := by
  rw [hB0,he0,sorted_values D.E i kind r hk hr]
  rfl

include hQc hQξ hQν hc hmean hr in
theorem source_partial_phi (hN : 0< N) (side : Fin 2) (reg : Bool)
    (z : Fin N→ unitInterval) (target : Fin (commonSize i kind)) :
    targetTypicalWeight
      (TypicalGuardStatistics.phi (commonSize i kind)
        (partialPrivateFin D i kind side 0).val (partialPrivateFin D i kind side 1).val
        Q.c Q.ξ D.E.U D.E.R D.E.Rp D.width reg
        (Q.marksLaw (partialPrivateFin D i kind side 0).val)
        (Q.marksLaw (partialPrivateFin D i kind side 1).val))
      (TypicalGuard.bids (SortedAllNoise.sortedBox (commonRow D.E i kind r))) target
      (compressedFlags (fun j : Fin N => categoryFlag D.E 1 (r j))
        (sortedActiveEquiv D.E i kind r hk)
        (OriginalFlagMeasure.flags (fun j => nativeFlag P D.ξ reg (r j)) z))=
      partialGuardWeight N (fun _ : Unit => zipRow N (r,z))
        (fun _ => ((sortedActiveEquiv D.E i kind r hk target).val).succ)
        (categoryFlag D.E 1) (categoryFlag D.E 2) (categoryFlag D.E 3)
        (nativeFlag P D.ξ reg) nativeBid D.ξ (SourceMenuPopulation.keptShare P t reg)
        (99/200) D.E.U D.E.R D.E.Rp D.width
        (SourceMenuPopulation.keptShare_bounds P t ht reg).1 reg side () := by
  rcases hc with rfl
  rw [hQc,hQξ,hQν,hQν,sorted_values D.E i kind r hk hr]
  have h0 := private_tuple_eq_original D.E i kind r hk D z side 0
  have h1 := private_tuple_eq_original D.E i kind r hk D z side 1
  have hu0 : NativeContinuation.upperTag 0=(2:Fin 4) := by decide
  have hu1 : NativeContinuation.upperTag 1=(3:Fin 4) := by decide
  simp only [hu0] at h0
  simp only [hu1] at h1
  let a : Fin N→ Bool := fun j => categoryFlag D.E 1 (r j)
  let e := sortedActiveEquiv D.E i kind r hk
  let b : Fin N→ℝ := fun j => nativeBid (r j)
  let f : Fin N→ Bool := OriginalFlagMeasure.flags (fun j => nativeFlag P D.ξ reg (r j)) z
  have hh := actual_phi_compression a N
    (partialPrivateFin D i kind side 0).val (partialPrivateFin D i kind side 1).val hN
    D.ξ (SourceMenuPopulation.keptShare P t reg) (99/200) D.E.U D.E.R D.E.Rp D.width
    (SourceMenuPopulation.keptShare_bounds P t ht reg).1 reg
    (SourceMenuPopulation.keptShare_bounds P t ht reg).2
    (D.marksLaw (partialPrivateFin D i kind side 0))
    (D.marksLaw (partialPrivateFin D i kind side 1))
    (hmean reg _) (hmean reg _) e b f target
  have hM : fullMixedCount a f (e target).val=
      flaggedMixedCount N (fun _ : Unit => zipRow N (r,z))
        (fun _ => ((e target).val).succ) (categoryFlag D.E 1) (nativeFlag P D.ξ reg) false () :=
    (mixed_card_compression a e f target).symm.trans
      (partial_mixed_compression (zipRow N (r,z)) (categoryFlag D.E 1)
        (nativeFlag P D.ξ reg) e target)
  have hW : fullReciprocal a b f (e target).val=
      (N:ℝ)*flaggedReciprocal N (fun _ : Unit => zipRow N (r,z))
        (fun _ => ((e target).val).succ) (categoryFlag D.E 1)
        (nativeFlag P D.ξ reg) nativeBid 1 false () :=
    (reciprocal_compression a e b f target).symm.trans
      (partial_reciprocal_compression (zipRow N (r,z)) (categoryFlag D.E 1)
        (nativeFlag P D.ξ reg) nativeBid e target hN
        (fun j hj => (menu_active_box D.E (r j) (hr j) hj).1))
  have hN0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [hM,hW,mul_div_cancel_left₀ _ hN0] at hh
  refine hh.trans ?_
  dsimp only [partialGuardWeight]
  rw [h0,h1]
  rfl

end Scalar
end FCAppendix.Affine.Tail04.PartialSortedCompression
