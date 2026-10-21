import FCAppendix.Affine.Tail04.NativeLocalPolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon LocalCoordinates SortedCoordinates JoinedHighPolicy
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

def zeroMean (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) : ℝ :=
  LocalSamplerMean.mean (D.oneSampler N H0 H1) p (D.originalPrivateRow H1) (Sum.inl i)

def oneMean (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) : ℝ :=
  LocalSamplerMean.mean (D.zeroSampler N H0 H1) p (D.originalPrivateRow H0) (Sum.inl i)

lemma zeroMean_bounds (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) :
    D.zeroMean N H0 H1 p i∈Icc (0:ℝ) 1 :=
  LocalSamplerMean.bounds _ (D.oneSampler_measurable N H0 H1) p (D.originalPrivateRow H1) _

lemma oneMean_bounds (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) :
    D.oneMean N H0 H1 p i∈Icc (0:ℝ) 1 :=
  LocalSamplerMean.bounds _ (D.zeroSampler_measurable N H0 H1) p (D.originalPrivateRow H0) _

def highReceiptAtKey (j : Fin 2) (K : LocalCoordinates.Key m) (L : LocalList m) : Fin m → ℝ :=
  if j=0 then
    receiptTransport K.1.1 K.1.2 (bidVector L) (privateKey D.E L)
      (receipt (publicBids (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L))
        (D.zeroMean K.1.1.card (D.finiteCount K.1.2) K.2
          (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L)) D.ξ (privateRow D.E K.1.2 L))
  else
    receiptTransport K.1.1 K.1.2 (bidVector L) (privateKey D.E L)
      (receipt (publicBids (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L))
        (D.oneMean K.1.1.card K.2 (D.finiteCount K.1.2)
          (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L)) D.ξ (privateRow D.E K.1.2 L))

def highReceipt (j : Fin 2) (L : LocalList m) : Fin m → ℝ :=
  D.highReceiptAtKey j (LocalCoordinates.key D.E L) L

lemma highReceiptAtKey_zero (j : Fin 2) (K : LocalCoordinates.Key m) (L : LocalList m)
    (i : Fin m) (hi : i∉K.1.1∪K.1.2) : D.highReceiptAtKey j K L i=0 := by
  unfold highReceiptAtKey
  split_ifs <;> exact receiptTransport_zero _ _ _ _ _ i hi

lemma highReceiptAtKey_floor (j : Fin 2) (K : LocalCoordinates.Key m) (L : LocalList m)
    (i : Fin m) (hi : i∈K.1.1∪K.1.2) :
    min (1-D.ξ) D.E.R≤ D.highReceiptAtKey j K L i := by
  have hR : 0< D.E.R := D.E.d_nonneg.trans_lt D.E.d_lt_R
  have hRH : D.E.R≤ D.E.H := D.E.R_le_Rp.trans D.E.Rp_lt_H.le
  unfold highReceiptAtKey
  split_ifs with hj
  · apply receiptTransport_lower _ _ _ _ _ _ _ i hi
    intro k
    exact (LowResidualCompletion.receipt_lower _ _ _ D.xi_pos.le D.xi_lt_one
      (fun k => (LocalCoordinates.activeBids D.E K.1.1 L k).2.1)
      (fun k => (D.zeroMean_bounds _ _ _ _ k).2) hR hRH k).2
  · apply receiptTransport_lower _ _ _ _ _ _ _ i hi
    intro k
    exact (LowResidualCompletion.receipt_lower _ _ _ D.xi_pos.le D.xi_lt_one
      (fun k => (LocalCoordinates.activeBids D.E K.1.1 L k).2.1)
      (fun k => (D.oneMean_bounds _ _ _ _ k).2) hR hRH k).2

lemma highReceipt_zero (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∉ids D.E 1 L∪ids D.E 2 L) : D.highReceipt j L i=0 :=
  D.highReceiptAtKey_zero j _ L i hi

lemma highReceipt_floor (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 1 L∪ids D.E 2 L) : min (1-D.ξ) D.E.R≤ D.highReceipt j L i :=
  D.highReceiptAtKey_floor j _ L i hi

lemma highReceipt_nonneg (j : Fin 2) (L : LocalList m) : ∀ i,0≤ D.highReceipt j L i := by
  intro i
  by_cases hi : i∈ids D.E 1 L∪ids D.E 2 L
  · exact (le_min (by linarith [D.xi_lt_one])
      (D.E.d_nonneg.trans D.E.d_lt_R.le)).trans (D.highReceipt_floor j L i hi)
  · simp [D.highReceipt_zero j L i hi]

theorem high_numerical_optimal (j : Fin 2) (L : LocalList m) (u : unitInterval) :
    Finite.Optimal c (D.highReceipt j L) (D.high j L u) := by
  let K := LocalCoordinates.key D.E L
  have hd : Disjoint K.1.1 K.1.2 := ids_disjoint D.E (by decide) L
  change Finite.Optimal c (D.highReceiptAtKey j K L) (D.highAtKey j K L u)
  by_cases hj : j=0
  · simp only [highReceiptAtKey,highAtKey,dif_pos hd,if_pos hj]
    apply receiptTransport_optimal _ _ hd _ _ c _ _
    exact (D.original_high_optimal K.1.1.card (D.finiteCount K.1.2) K.2
      (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L) rfl).1 _ u
  · simp only [highReceiptAtKey,highAtKey,dif_pos hd,if_neg hj]
    apply receiptTransport_optimal _ _ hd _ _ c _ _
    exact (D.original_high_optimal K.1.1.card K.2 (D.finiteCount K.1.2)
      (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L) rfl).2 _ u

theorem high_card_exact (j : Fin 2) (L : LocalList m) (u : unitInterval) :
    (D.high j L u).card=min c (D.E.localCount L 1+D.E.localCount L 2) := by
  let H := ids D.E 1 L∪ids D.E 2 L
  have hH : H.card=D.E.localCount L 1+D.E.localCount L 2 := by
    rw [Finset.card_union_of_disjoint (ids_disjoint D.E (by decide) L),ids_card,ids_card]
  have hs := D.high_numerical_optimal j L u
  apply le_antisymm (le_min hs.1 (D.high_card_le_count j L u))
  by_cases he : D.high j L u=H
  · rw [he,hH]
    exact min_le_right _ _
  · have hlt : (D.high j L u).card< H.card := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨D.high_subset j L u,he⟩)
    obtain ⟨i,hi,hn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hr : 0< D.highReceipt j L i :=
      (lt_min (by linarith [D.xi_lt_one])
        (D.E.d_nonneg.trans_lt D.E.d_lt_R)).trans_le (D.highReceipt_floor j L i hi)
    rw [Finite.optimal_fills c _ _ hs i hn hr]
    exact min_le_left _ _

def oppositeActiveMean (j : Fin 2) (L : LocalList m) : Fin (ids D.E 1 L).card → ℝ :=
  let K := LocalCoordinates.key D.E L
  if j=0 then D.zeroMean K.1.1.card (D.finiteCount K.1.2) K.2
    (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L)
  else D.oneMean K.1.1.card K.2 (D.finiteCount K.1.2)
    (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L)

lemma highReceipt_active_clipped (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 1 L) :
    D.highReceipt j L i=LocalCoordinates.clamp 1 D.E.U (entryBid (L i))*
      (1-D.ξ*D.oppositeActiveMean j L (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)) := by
  by_cases hj : j=0 <;>
    simp only [highReceipt,highReceiptAtKey,LocalCoordinates.key,hj,if_true,if_false,
      receiptTransport,dif_pos hi,receipt,publicBids,parameter,TypicalGuard.bids,
      oppositeActiveMean,LocalCoordinates.activeBids,enumerate_rank]

lemma highReceipt_active (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 1 L) (hb : entryBid (L i)∈Icc (1:ℝ) D.E.U) :
    D.highReceipt j L i=entryBid (L i)*(1-D.ξ*D.oppositeActiveMean j L
      (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)) := by
  have ha : (LocalCoordinates.activeBids D.E (ids D.E 1 L) L
      (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)).val=entryBid (L i) := by
    simp only [LocalCoordinates.activeBids,enumerate_rank]
    exact LocalCoordinates.clamp_eq hb
  by_cases hj : j=0 <;>
    simp only [highReceipt,highReceiptAtKey,LocalCoordinates.key,hj,if_true,if_false,
      receiptTransport,dif_pos hi,receipt,publicBids,parameter,TypicalGuard.bids,
      oppositeActiveMean,ha]

lemma highReceipt_private (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 2 L) : D.highReceipt j L i=entryBid (L i) := by
  have hn : i∉ids D.E 1 L := fun ha =>
    (Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (1:Fin 4)≠2) L)) ha hi
  have hd := LocalCoordinates.numerical_decode D.E (private_ids_band D.E L i hi)
  by_cases hj : j=0 <;>
    simpa only [highReceipt,highReceiptAtKey,LocalCoordinates.key,hj,if_true,if_false,
      receiptTransport,dif_neg hn,dif_pos hi,receipt,privateRow,enumerate_rank] using hd

end FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
