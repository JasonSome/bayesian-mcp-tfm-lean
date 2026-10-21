import FCAppendix.Affine.Tail04.NativeRawFactor

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeFocalFactor
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair NativePolicyFactor NativeRawFactor
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper Hybrid

variable {m c : ℕ} (D : Data m c)

def commonTarget {N H : ℕ} (x : Option (Fin N)) : FocalInsertion.Target N H := x.map Sum.inl

def commonIdentity (f : Fin m) (A : Finset (Fin m)) (b : Fin m → ℝ)
    (x : Option (Fin A.card)) : Fin m := x.elim f (fun a => (enumerate A b a).val)

lemma embedding_common (f : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hf : f∉A∪P) (b k : Fin m → ℝ) (x : Option (Fin A.card)) :
    FocalIdentity.embedding f A P hAP hf b k (commonTarget x)=commonIdentity f A b x := by
  cases x <;> rfl

lemma common_mem_transport (f : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hf : f∉A∪P) (b k : Fin m → ℝ) (S : Finset (FocalInsertion.Target A.card P.card))
    (x : Option (Fin A.card)) :
    commonIdentity f A b x∈FocalIdentity.transport f A P hAP hf b k S ↔ commonTarget x∈S := by
  rw [←embedding_common f A P hAP hf b k x]
  simp [FocalIdentity.transport]

lemma focal_active (j : Fin 2) (f : Fin m) (L : LocalList m) (h : D.UseFocal j f L) :
    f∈ids D.E 1 L := ((D.offCommon_mem L f).mp (by rw [h.1];simp)).1

lemma focal_not_missing (j : Fin 2) (f : Fin m) (L : LocalList m) (h : D.UseFocal j f L) :
    f∉(ids D.E 1 L).erase f∪ids D.E 3 L := by
  have hf := (focal_active D) j f L h
  have hn : f∉ids D.E 3 L := fun hh =>
    Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (1:Fin 4)≠3) L) hf hh
  simp [hn]

lemma focalKey_missing_disjoint (L : LocalList m) (f : Fin m) :
    Disjoint ((ids D.E 1 L).erase f) (ids D.E 3 L) :=
  (ids_disjoint D.E (by decide : (1:Fin 4)≠3) L).mono_left (Finset.erase_subset _ _)

lemma opposite_focal_one {L K : LocalList m} (h : D.E.Compatible L K) (f : Fin m)
    (hu : D.UseFocal 0 f L) (x : Option (Fin ((ids D.E 1 L).erase f).card)) (u : Seed) :
    commonIdentity f ((ids D.E 1 L).erase f) (bidVector L) x∈(D.focalPolicy 1 f K u).val ↔
      commonTarget x∈D.oneFocal ((ids D.E 1 L).erase f).card
        (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L))
        ((D.parameter ((ids D.E 1 L).erase f) (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)) L,entryBid (L f)),privateRow D.E (ids D.E 3 L) K) u.1 := by
  have huK : D.UseFocal 1 f K := by simpa [otherProposer] using ((NativeRawFactor.UseFocal_pair D) h 0 f).mp hu
  have hf := (focal_not_missing D) 0 f L hu
  have hd := (focalKey_missing_disjoint D) L f
  have hgu : D.FocalUseAtKey 1
      (f,(((ids D.E 1 L).erase f,ids D.E 3 L),D.finiteCount (ids D.E 2 L))) K := by
    simpa only [(NativeRawFactor.focalKey_pair D) h f] using huK.2
  change _∈D.focalSelection 1 f K u.1 ↔ _
  rw [Data.focalSelection,if_pos huK,(NativeRawFactor.focalKey_pair D) h f]
  simp only [Data.focalAtKey,dif_pos hd,dif_pos hf,if_pos hgu,if_neg (by decide : (1:Fin 2)≠0)]
  have hb := (NativeRawFactor.common_subset_bid_eq D) h ((ids D.E 1 L).erase f) (Finset.erase_subset _ _)
  have he := enumerate_congr ((ids D.E 1 L).erase f) (bidVector L) (bidVector K) hb
  have hid : commonIdentity f ((ids D.E 1 L).erase f) (bidVector L) x=
      commonIdentity f ((ids D.E 1 L).erase f) (bidVector K) x := by
    cases x <;> simp [commonIdentity,he]
  erw [hid,common_mem_transport f ((ids D.E 1 L).erase f) (ids D.E 3 L) hd hf
    (bidVector K) (privateKey D.E K) _ x]
  erw [←(NativeRawFactor.parameter_common_subset D) h ((ids D.E 1 L).erase f) (Finset.erase_subset _ _)
      (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L)),
    ←D.E.common_entries h (Or.inr rfl) f ((focal_active D) 0 f L hu)]
  rfl

lemma opposite_focal_zero {L K : LocalList m} (h : D.E.Compatible L K) (f : Fin m)
    (hu : D.UseFocal 1 f L) (x : Option (Fin ((ids D.E 1 L).erase f).card)) (u : Seed) :
    commonIdentity f ((ids D.E 1 L).erase f) (bidVector L) x∈(D.focalPolicy 0 f K u).val ↔
      commonTarget x∈D.zeroFocal ((ids D.E 1 L).erase f).card
        (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L))
        ((D.parameter ((ids D.E 1 L).erase f) (D.finiteCount (ids D.E 3 L))
          (D.finiteCount (ids D.E 2 L)) L,entryBid (L f)),privateRow D.E (ids D.E 3 L) K) u.1 := by
  have huK : D.UseFocal 0 f K := by simpa [otherProposer] using ((NativeRawFactor.UseFocal_pair D) h 1 f).mp hu
  have hf := (focal_not_missing D) 1 f L hu
  have hd := (focalKey_missing_disjoint D) L f
  have hgu : D.FocalUseAtKey 0
      (f,(((ids D.E 1 L).erase f,ids D.E 3 L),D.finiteCount (ids D.E 2 L))) K := by
    simpa only [(NativeRawFactor.focalKey_pair D) h f] using huK.2
  change _∈D.focalSelection 0 f K u.1 ↔ _
  rw [Data.focalSelection,if_pos huK,(NativeRawFactor.focalKey_pair D) h f]
  simp only [Data.focalAtKey,dif_pos hd,dif_pos hf,if_pos hgu,ite_true]
  have hb := (NativeRawFactor.common_subset_bid_eq D) h ((ids D.E 1 L).erase f) (Finset.erase_subset _ _)
  have he := enumerate_congr ((ids D.E 1 L).erase f) (bidVector L) (bidVector K) hb
  have hid : commonIdentity f ((ids D.E 1 L).erase f) (bidVector L) x=
      commonIdentity f ((ids D.E 1 L).erase f) (bidVector K) x := by
    cases x <;> simp [commonIdentity,he]
  erw [hid,common_mem_transport f ((ids D.E 1 L).erase f) (ids D.E 3 L) hd hf
    (bidVector K) (privateKey D.E K) _ x]
  erw [←(NativeRawFactor.parameter_common_subset D) h ((ids D.E 1 L).erase f) (Finset.erase_subset _ _)
      (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L)),
    ←D.E.common_entries h (Or.inr rfl) f ((focal_active D) 1 f L hu)]
  rfl

lemma focal_low_absent (j : Fin 2) (f : Fin m) (L : LocalList m) (hu : D.UseFocal j f L)
    (i : Fin m) (hi : D.E.localTag (L i)=0) (u : Seed) : i∉(D.focalPolicy j f L u).val := by
  intro hin
  change i∈D.focalSelection j f L u.1 at hin
  rw [Data.focalSelection,if_pos hu] at hin
  have hs := D.focalAtKey_subset j (D.focalKey f L) L u.1 hin
  change i ∈ insert f ((ids D.E 1 L).erase f ∪ ids D.E 2 L) at hs
  rcases Finset.mem_insert.mp hs with hf | hs
  · subst i
    have ht := (Finset.mem_filter.mp ((focal_active D) j f L hu)).2
    simp_all
  · rcases Finset.mem_union.mp hs with ha | hp
    · have ht := (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha)).2
      simp_all
    · have ht := (Finset.mem_filter.mp hp).2
      simp_all

def focalCommonMean0 (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) (x : Option (Fin N)) : ℝ :=
  x.elim (D.focalPair N H0 H1 p y).left (D.focalMean0 N H0 H1 p y)

def focalCommonMean1 (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) (x : Option (Fin N)) : ℝ :=
  x.elim (D.focalPair N H0 H1 p y).right (D.focalMean1 N H0 H1 p y)

lemma focalCommonMean0_original (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) (hp : D.FocalUse N H0 H1 p)
    (x : Option (Fin N)) :
    LocalSamplerMean.mean (D.zeroFocal N H0 H1) (p,y) (D.originalPrivateRow H0) (commonTarget x)=
      (focalCommonMean0 D) N H0 H1 p y x := by
  cases x with
  | none =>
    obtain ⟨hs,hg0,hg1,hp0,hp1⟩ := hp.2
    exact (FocalInsertion.original_focal_means N H0.val H1.val c (regime p.1.1)
      (owner0 p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) y
      (D.originalPrivateRow H0 : Measure (Row H0.val D.E.R D.E.Rp D.E.H)) (D.originalPrivateRow H1 : Measure (Row H1.val D.E.R D.E.Rp D.E.H)) D.xi_pos D.xi_lt_one.le
      (fun i => (p.1.2 i).2) hs hg0 hg1).1
  | some i => exact D.focalMean0_original N H0 H1 p y i

lemma focalCommonMean1_original (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) (hp : D.FocalUse N H0 H1 p)
    (x : Option (Fin N)) :
    LocalSamplerMean.mean (D.oneFocal N H0 H1) (p,y) (D.originalPrivateRow H1) (commonTarget x)=
      (focalCommonMean1 D) N H0 H1 p y x := by
  cases x with
  | none =>
    obtain ⟨hs,hg0,hg1,hp0,hp1⟩ := hp.2
    exact (FocalInsertion.original_focal_means N H0.val H1.val c (regime p.1.1)
      (owner0 p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) y
      (D.originalPrivateRow H0 : Measure (Row H0.val D.E.R D.E.Rp D.E.H)) (D.originalPrivateRow H1 : Measure (Row H1.val D.E.R D.E.Rp D.E.H)) D.xi_pos D.xi_lt_one.le
      (fun i => (p.1.2 i).2) hs hg0 hg1).2
  | some i => exact D.focalMean1_original N H0 H1 p y i

def focalOppositeMean (j : Fin 2) (f : Fin m) (L : LocalList m) :
    Option (Fin ((ids D.E 1 L).erase f).card) → ℝ :=
  if j=0 then
    (focalCommonMean1 D) ((ids D.E 1 L).erase f).card (D.finiteCount (ids D.E 2 L))
      (D.finiteCount (ids D.E 3 L))
      (D.parameter ((ids D.E 1 L).erase f) (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 3 L)) L) (entryBid (L f))
  else
    (focalCommonMean0 D) ((ids D.E 1 L).erase f).card (D.finiteCount (ids D.E 3 L))
      (D.finiteCount (ids D.E 2 L))
      (D.parameter ((ids D.E 1 L).erase f) (D.finiteCount (ids D.E 3 L))
        (D.finiteCount (ids D.E 2 L)) L) (entryBid (L f))

lemma FocalUse_zero (f : Fin m) (L : LocalList m) (h : D.UseFocal 0 f L) :
    D.FocalUse ((ids D.E 1 L).erase f).card (D.finiteCount (ids D.E 2 L))
      (D.finiteCount (ids D.E 3 L))
      (D.parameter ((ids D.E 1 L).erase f) (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 3 L)) L) := by
  have hh := h.2
  rw [NativeRawFactor.focalKey_self D f L] at hh
  simpa only [Data.FocalUseAtKey,ite_true] using hh

lemma FocalUse_one (f : Fin m) (L : LocalList m) (h : D.UseFocal 1 f L) :
    D.FocalUse ((ids D.E 1 L).erase f).card (D.finiteCount (ids D.E 3 L))
      (D.finiteCount (ids D.E 2 L))
      (D.parameter ((ids D.E 1 L).erase f) (D.finiteCount (ids D.E 3 L))
        (D.finiteCount (ids D.E 2 L)) L) := by
  have hh := h.2
  rw [NativeRawFactor.focalKey_self D f L] at hh
  simpa only [Data.FocalUseAtKey,if_neg (by decide : (1:Fin 2) ≠ 0)] using hh

end FCAppendix.Affine.Tail04.NativeFocalFactor
