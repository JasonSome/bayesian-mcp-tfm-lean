import FCAppendix.Affine.Tail04.NativeFocalFactor

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeFocalVector
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair NativeRawFactor NativeFocalFactor
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper

variable {m c : ℕ} (D : Data m c)

def focalOppositeIdentityMean (j : Fin 2) (f : Fin m) (L : LocalList m) (i : Fin m) : ℝ :=
  if i=f then (NativeFocalFactor.focalOppositeMean D) j f L none
  else if hi : i∈(ids D.E 1 L).erase f then
    (NativeFocalFactor.focalOppositeMean D) j f L (some (rankFin ((ids D.E 1 L).erase f) (bidVector L) ⟨i,hi⟩))
  else 0

lemma focalNumericalReceipt_all (j : Fin 2) (f : Fin m) (L : LocalList m)
    (hu : D.UseFocal j f L) (i : Fin m) :
    D.focalNumericalReceipt j f L i=
      entryBid (L i)*(1-D.ξ*(focalOppositeIdentityMean D) j f L i) := by
  have hf := (NativeFocalFactor.focal_active D) j f L hu
  have hnP : f∉ids D.E 2 L := fun hh =>
    Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (1:Fin 4)≠2) L) hf hh
  unfold Data.focalNumericalReceipt
  rw [NativeRawFactor.focalKey_self D f L]
  by_cases hif : i=f
  · subst i
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl <;> simp [Data.focalReceiptAtKey,Option.elim,
      FocalIdentity.receipt,Data.zeroFocalReceipt,Data.oneFocalReceipt,FocalInsertion.receipt,
      focalOppositeIdentityMean,focalOppositeMean,focalCommonMean0,focalCommonMean1]
  · by_cases hiA : i∈(ids D.E 1 L).erase f
    · have hb : entryBid (L i)∈Icc (1:ℝ) D.E.U := D.old_common_box L f hu.1 i hiA
      have hc : LocalCoordinates.clamp 1 D.E.U (entryBid (L i))=entryBid (L i) := clamp_eq hb
      have hj : j = 0 ∨ j = 1 := by omega
      rcases hj with rfl | rfl <;> simp [Data.focalReceiptAtKey,Option.elim,
        FocalIdentity.receipt,hif,hiA,receiptTransport,Data.zeroFocalReceipt,Data.oneFocalReceipt,
        FocalInsertion.receipt,EqualPrivateUpper.receipt,focalOppositeIdentityMean,
        focalOppositeMean,focalCommonMean0,focalCommonMean1,publicBids,Data.parameter,
        TypicalGuard.bids,activeBids,enumerate_rank,hc]
    · by_cases hiP : i∈ids D.E 2 L
      · have hd := numerical_decode D.E (private_ids_band D.E L i hiP)
        have hj : j = 0 ∨ j = 1 := by omega
        rcases hj with rfl | rfl <;> simp [Data.focalReceiptAtKey,Option.elim,
          FocalIdentity.receipt,hif,hiA,hiP,receiptTransport,Data.zeroFocalReceipt,Data.oneFocalReceipt,
          FocalInsertion.receipt,EqualPrivateUpper.receipt,focalOppositeIdentityMean,
          privateRow,enumerate_rank,hd]
      · have hj : j = 0 ∨ j = 1 := by omega
        rcases hj with rfl | rfl <;> simp [Data.focalReceiptAtKey,
          FocalIdentity.receipt,hif,hiA,hiP,focalOppositeIdentityMean]

lemma focalOppositeIdentityMean_private (j : Fin 2) (f : Fin m) (L : LocalList m)
    (hu : D.UseFocal j f L) (i : Fin m) (hi : D.E.localTag (L i)=2) :
    (focalOppositeIdentityMean D) j f L i=0 := by
  have hf := (Finset.mem_filter.mp ((NativeFocalFactor.focal_active D) j f L hu)).2
  have hif : i≠f := by intro he;subst i;simp_all
  have hA : i∉(ids D.E 1 L).erase f := by
    intro hh
    have h1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hh)).2
    simp_all
  simp [focalOppositeIdentityMean,hif,hA]

lemma focalOppositeIdentityMean_low (j : Fin 2) (f : Fin m) (L : LocalList m)
    (hu : D.UseFocal j f L) (i : Fin m) (hi : D.E.localTag (L i)=0) :
    (focalOppositeIdentityMean D) j f L i=0 := by
  have hf := (Finset.mem_filter.mp ((NativeFocalFactor.focal_active D) j f L hu)).2
  have hif : i≠f := by intro he;subst i;simp_all
  have hA : i∉(ids D.E 1 L).erase f := by
    intro hh
    have h1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hh)).2
    simp_all
  simp [focalOppositeIdentityMean,hif,hA]

end FCAppendix.Affine.Tail04.NativeFocalVector
