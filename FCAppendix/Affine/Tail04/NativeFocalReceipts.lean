import FCAppendix.Affine.Tail04.NativeFocalInsertion

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalCoordinates SortedCoordinates JoinedHighPolicy
open scoped BigOperators

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

def focalPair (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) : FocalResponse.UnitPair :=
  FocalInsertion.pair N H0.val H1.val c D.ξ (regime p.1.1)
    (owner0 p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) y (D.marksLaw H0) (D.marksLaw H1)

def focalMean0 (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) : Fin N → ℝ :=
  FocalInsertion.activeMean N H0.val c D.ξ (regime p.1.1) (owner0 p.1.1) (mixed p.1.1)
    (publicBids p) y (D.focalPair N H0 H1 p y).left (D.marksLaw H0)

def focalMean1 (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) : Fin N → ℝ :=
  FocalInsertion.activeMean N H1.val c D.ξ (regime p.1.1) (owner1 p.1.1) (mixed p.1.1)
    (publicBids p) y (D.focalPair N H0 H1 p y).right (D.marksLaw H1)

def focalPrice0 (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) : ℝ :=
  FocalInsertion.meanPrice N H0.val c D.ξ (regime p.1.1) (owner0 p.1.1) (mixed p.1.1)
    (publicBids p) (D.focalPair N H0 H1 p y).left (D.marksLaw H0)

def focalPrice1 (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) : ℝ :=
  FocalInsertion.meanPrice N H1.val c D.ξ (regime p.1.1) (owner1 p.1.1) (mixed p.1.1)
    (publicBids p) (D.focalPair N H0 H1 p y).right (D.marksLaw H1)

def zeroFocalReceipt (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ)
    (row : Row H0.val D.E.R D.E.Rp D.E.H) : FocalInsertion.Target N H0.val → ℝ :=
  FocalInsertion.receipt (publicBids p) y (D.focalMean1 N H0 H1 p y)
    (D.focalPair N H0 H1 p y).right D.ξ row

def oneFocalReceipt (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ)
    (row : Row H1.val D.E.R D.E.Rp D.E.H) : FocalInsertion.Target N H1.val → ℝ :=
  FocalInsertion.receipt (publicBids p) y (D.focalMean0 N H0 H1 p y)
    (D.focalPair N H0 H1 p y).left D.ξ row

lemma focal_threshold (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ)
    (hp : D.FocalUse N H0 H1 p) (hy : 0≤ y) :
    (∀ row u,FocalInsertion.Threshold c (D.zeroFocalReceipt N H0 H1 p y row)
      (D.zeroFocal N H0 H1 ((p,y),row) u) (D.focalPrice1 N H0 H1 p y)) ∧
    (∀ row u,FocalInsertion.Threshold c (D.oneFocalReceipt N H0 H1 p y row)
      (D.oneFocal N H0 H1 ((p,y),row) u) (D.focalPrice0 N H0 H1 p y)) := by
  obtain ⟨hs,hg0,hg1,hp0,hp1⟩ := hp.2
  exact FocalInsertion.pair_sampler_threshold N H0.val H1.val c (regime p.1.1)
    (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) y
    (D.marksLaw H0) (D.marksLaw H1) D.xi_pos D.xi_lt_one.le D.E.one_le_U
    (fun i => (p.1.2 i).2) hy D.E.Rp_lt_one D.E.U_lt_H hs hg0 hg1 hp0 hp1

lemma focal_price_lower (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) (hp : D.FocalUse N H0 H1 p) :
    (1-D.ξ)*D.E.U≤ D.focalPrice0 N H0 H1 p y ∧
      (1-D.ξ)*D.E.U≤ D.focalPrice1 N H0 H1 p y := by
  obtain ⟨hs,hg0,hg1,hp0,hp1⟩ := hp.2
  obtain ⟨hOO,hIO,hcover,hc0,hc1,hI⟩ := hs
  have hW := mixedReciprocalSum_pos (mixed p.1.1) (publicBids p) hI
    (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (p.1.2 i).2.1)
  exact ⟨(FocalInsertion.meanPrice_bounds N H0.val c (regime p.1.1)
    (owner0 p.1.1) (mixed p.1.1) (publicBids p) _ (D.marksLaw H0) D.xi_pos.le
    (D.focalPair N H0 H1 p y).left_mem hW hc0 hg0).1,
    (FocalInsertion.meanPrice_bounds N H1.val c (regime p.1.1)
      (owner1 p.1.1) (mixed p.1.1) (publicBids p) _ (D.marksLaw H1) D.xi_pos.le
      (D.focalPair N H0 H1 p y).right_mem hW hc1 hg1).1⟩

lemma focalMean0_original (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) (i : Fin N) :
    (∫ z : Row H0.val D.E.R D.E.Rp D.E.H × unitInterval,
      if some (Sum.inl i)∈D.zeroFocal N H0 H1 ((p,y),z.1) z.2 then (1:ℝ) else 0
      ∂(D.originalPrivateRow H0 : Measure _).prod volume)=D.focalMean0 N H0 H1 p y i :=
  FocalInsertion.original_mean N H0.val c D.ξ (regime p.1.1) (owner0 p.1.1) (mixed p.1.1)
    D.E.R D.E.Rp D.E.H (publicBids p,y,(D.focalPair N H0 H1 p y).left)
    (D.originalPrivateRow H0) (some (Sum.inl i))

lemma focalMean1_original (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) (i : Fin N) :
    (∫ z : Row H1.val D.E.R D.E.Rp D.E.H × unitInterval,
      if some (Sum.inl i)∈D.oneFocal N H0 H1 ((p,y),z.1) z.2 then (1:ℝ) else 0
      ∂(D.originalPrivateRow H1 : Measure _).prod volume)=D.focalMean1 N H0 H1 p y i :=
  FocalInsertion.original_mean N H1.val c D.ξ (regime p.1.1) (owner1 p.1.1) (mixed p.1.1)
    D.E.R D.E.Rp D.E.H (publicBids p,y,(D.focalPair N H0 H1 p y).right)
    (D.originalPrivateRow H1) (some (Sum.inl i))

def focalReceiptAtKey (j : Fin 2) (K : FocalKey m) (L : LocalList m) : Fin m → ℝ :=
  if j=0 then
    FocalIdentity.receipt K.1 K.2.1.1 K.2.1.2 (bidVector L) (privateKey D.E L)
      (D.zeroFocalReceipt K.2.1.1.card (D.finiteCount K.2.1.2) K.2.2
        (D.parameter K.2.1.1 (D.finiteCount K.2.1.2) K.2.2 L) (entryBid (L K.1))
        (privateRow D.E K.2.1.2 L)) (fun k => entryBid (L k))
  else
    FocalIdentity.receipt K.1 K.2.1.1 K.2.1.2 (bidVector L) (privateKey D.E L)
      (D.oneFocalReceipt K.2.1.1.card K.2.2 (D.finiteCount K.2.1.2)
        (D.parameter K.2.1.1 K.2.2 (D.finiteCount K.2.1.2) L) (entryBid (L K.1))
        (privateRow D.E K.2.1.2 L)) (fun k => entryBid (L k))

def focalNumericalReceipt (j : Fin 2) (i : Fin m) (L : LocalList m) : Fin m → ℝ :=
  D.focalReceiptAtKey j (D.focalKey i L) L

lemma low_bid_bound (L : LocalList m) (k : Fin m)
    (h1 : D.E.localTag (L k)≠1) (h2 : D.E.localTag (L k)≠2) : entryBid (L k)≤ D.E.d := by
  cases he : L k with
  | none => simpa [he,entryBid] using D.E.d_nonneg
  | some b =>
    by_cases hl : b≤ D.E.d
    · simpa [he,entryBid] using hl
    · by_cases hp : b∈D.E.privateBids
      · exact (h2 (by simp [Observable.Regions.localTag,he,hl,hp])).elim
      · exact (h1 (by simp [Observable.Regions.localTag,he,hl,hp])).elim

lemma focal_outside_low (L : LocalList m) (i k : Fin m)
    (hk : k∉insert i ((ids D.E 1 L).erase i∪ids D.E 2 L)) : entryBid (L k)≤ D.E.d := by
  apply D.low_bid_bound L k
  · intro ht
    have hki : k≠i := fun he => hk (by simp [he])
    have ha : k∈ids D.E 1 L := by simp [ids,ht]
    exact hk (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hki,ha⟩)))
  · intro ht
    exact hk (Finset.mem_insert_of_mem (Finset.mem_union_right _ (by simp [ids,ht])))

theorem focalPolicy_numerical_optimal (hlow : D.E.d<1-D.ξ)
    (j : Fin 2) (i : Fin m) (L : LocalList m) (hL : NonnegativeList L)
    (hu : D.UseFocal j i L) (u : NativeLocalPolicy.Seed) :
    Finite.Optimal c (D.focalNumericalReceipt j i L) ((D.focalPolicy j i L u).val) := by
  let A := (ids D.E 1 L).erase i
  let P := ids D.E 2 L
  let K := D.focalKey i L
  have huse : D.FocalUseAtKey j (i,(((ids D.E 1 L).erase i,ids D.E 2 L),(key D.E L).2)) L := hu.2
  have hiA : i∈ids D.E 1 L := ((D.offCommon_mem L i).mp (by rw [hu.1];simp)).1
  have hd : Disjoint A P := (ids_disjoint D.E (by decide) L).mono_left (Finset.erase_subset i _)
  have hi : i∉A∪P := by
    have hnP : i∉P := fun hh => (Finset.disjoint_left.mp (ids_disjoint D.E (by decide) L)) hiA hh
    simp [A,hnP]
  have hτ : D.E.d≤(1-D.ξ)*D.E.U :=
    hlow.le.trans (by nlinarith [mul_le_mul_of_nonneg_left D.E.one_le_U (sub_nonneg.mpr D.xi_lt_one.le)])
  have hout : ∀ k,k∉insert i (A∪P) → entryBid (L k)≤ D.E.d := D.focal_outside_low L i
  by_cases hj : j=0
  · have hp : D.FocalUse A.card (D.finiteCount P) K.2.2 (D.parameter A (D.finiteCount P) K.2.2 L) := by
      simpa [FocalUseAtKey,K,A,P,focalKey,hj] using hu.2
    have hs := (D.focal_threshold A.card (D.finiteCount P) K.2.2
      (D.parameter A (D.finiteCount P) K.2.2 L) (entryBid (L i)) hp (hL i)).1
      (privateRow D.E P L) u.1
    have hl := (D.focal_price_lower A.card (D.finiteCount P) K.2.2
      (D.parameter A (D.finiteCount P) K.2.2 L) (entryBid (L i)) hp).2
    have hh := FocalIdentity.all_identity_optimal i A P hd hi (bidVector L) (privateKey D.E L)
      c _ (fun k => entryBid (L k)) _ _ hs (fun k hk => (hout k hk).trans (hτ.trans hl))
    simpa only [focalNumericalReceipt,focalReceiptAtKey,focalPolicy,focalSelection,if_pos hu,
      focalAtKey,dif_pos hd,dif_pos hi,if_pos hu.2,if_pos hj,K,A,P,focalKey,if_pos huse] using hh
  · have hp : D.FocalUse A.card K.2.2 (D.finiteCount P) (D.parameter A K.2.2 (D.finiteCount P) L) := by
      simpa [FocalUseAtKey,K,A,P,focalKey,hj] using hu.2
    have hs := (D.focal_threshold A.card K.2.2 (D.finiteCount P)
      (D.parameter A K.2.2 (D.finiteCount P) L) (entryBid (L i)) hp (hL i)).2
      (privateRow D.E P L) u.1
    have hl := (D.focal_price_lower A.card K.2.2 (D.finiteCount P)
      (D.parameter A K.2.2 (D.finiteCount P) L) (entryBid (L i)) hp).1
    have hh := FocalIdentity.all_identity_optimal i A P hd hi (bidVector L) (privateKey D.E L)
      c _ (fun k => entryBid (L k)) _ _ hs (fun k hk => (hout k hk).trans (hτ.trans hl))
    simpa only [focalNumericalReceipt,focalReceiptAtKey,focalPolicy,focalSelection,if_pos hu,
      focalAtKey,dif_pos hd,dif_pos hi,if_pos hu.2,if_neg hj,K,A,P,focalKey,if_pos huse] using hh

end FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
