import FCAppendix.Affine.Tail04.NativePolicyFactor

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeRawFactor
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair NativePolicyFactor
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper Hybrid

variable {m c : ℕ} (D : Data m c)

lemma common_subset_bid_eq {L K : LocalList m} (h : D.E.Compatible L K)
    (A : Finset (Fin m)) (hA : A⊆ids D.E 1 L) :
    ∀ i∈A,bidVector L i=bidVector K i :=
  fun i hi => congrArg entryBid (D.E.common_entries h (Or.inr rfl) i (hA hi))

lemma activeBids_common_subset {L K : LocalList m} (h : D.E.Compatible L K)
    (A : Finset (Fin m)) (hA : A⊆ids D.E 1 L) :
    activeBids D.E A L=activeBids D.E A K := by
  have hb := (common_subset_bid_eq D) h A hA
  have he := enumerate_congr A (bidVector L) (bidVector K) hb
  funext a
  apply Subtype.ext
  simp only [activeBids,he]
  congr 1
  exact hb _ (enumerate A (bidVector K) a).2

lemma parameter_common_subset {L K : LocalList m} (h : D.E.Compatible L K)
    (A : Finset (Fin m)) (hA : A⊆ids D.E 1 L) (H0 H1 : Fin (m+1)) :
    D.parameter A H0 H1 L=D.parameter A H0 H1 K := by
  simp only [Data.parameter,(activeBids_common_subset D) h A hA,
    NativeObservationPair.common_roleList D.E h (k:=0) (Or.inl rfl)]

lemma offCommon_pair {L K : LocalList m} (h : D.E.Compatible L K) :
    D.offCommon L=D.offCommon K := by
  ext i
  simp only [Data.offCommon,Finset.mem_filter,Finset.mem_univ,true_and]
  have ht := D.E.entry_common_tag (h i) (k:=1) (Or.inr rfl)
  constructor
  · rintro ⟨hi,hb⟩
    exact ⟨ht.mp hi,by rw [←D.E.entry_common (h i) (Or.inr rfl) hi];exact hb⟩
  · rintro ⟨hi,hb⟩
    exact ⟨ht.mpr hi,by rw [D.E.entry_common (h i) (Or.inr rfl) (ht.mpr hi)];exact hb⟩

lemma offCandidate_pair {L K : LocalList m} (h : D.E.Compatible L K) :
    D.offCandidate L=D.offCandidate K := by
  simp only [Data.offCandidate,(offCommon_pair D) h]

lemma focalKey_self (i : Fin m) (L : LocalList m) :
    D.focalKey i L=(i,(((ids D.E 1 L).erase i,ids D.E 2 L),D.finiteCount (ids D.E 3 L))) := by
  simp only [Data.focalKey,D.key_self L]

lemma focalKey_pair {L K : LocalList m} (h : D.E.Compatible L K) (i : Fin m) :
    D.focalKey i K=(i,(((ids D.E 1 L).erase i,ids D.E 3 L),D.finiteCount (ids D.E 2 L))) := by
  simp only [Data.focalKey,D.key_pair h,←D.E.common_ids h (k:=1) (Or.inr rfl),
    D.E.private_ids_missing h]

lemma UseFocal_pair {L K : LocalList m} (h : D.E.Compatible L K)
    (j : Fin 2) (i : Fin m) : D.UseFocal j i L ↔ D.UseFocal (otherProposer j) i K := by
  have hp0 := (parameter_common_subset D) h ((ids D.E 1 L).erase i)
    (Finset.erase_subset _ _) (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L))
  have hp1 := (parameter_common_subset D) h ((ids D.E 1 L).erase i)
    (Finset.erase_subset _ _) (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L))
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl | rfl
  · simp only [Data.UseFocal,(offCommon_pair D) h,otherProposer,ite_true]
    rw [focalKey_self, focalKey_pair D h]
    dsimp only [Data.FocalUseAtKey, Prod.fst, Prod.snd]
    simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    rw [hp0]
  · simp only [Data.UseFocal,(offCommon_pair D) h,otherProposer,
      show (1 : Fin 2) ≠ 0 by decide,ite_false]
    rw [focalKey_self, focalKey_pair D h]
    dsimp only [Data.FocalUseAtKey, Prod.fst, Prod.snd]
    simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    rw [hp1]

lemma fallback_pair {L K : LocalList m} (h : D.E.Compatible L K)
    (j : Fin 2) (hOff : D.offCommon L≠∅) (hf : ∀ i,¬D.UseFocal j i L)
    (u : Seed) : D.completedPolicy (otherProposer j) K u=D.rawFallback (otherProposer j) K u := by
  apply D.completed_fallback
  · rw [←(offCommon_pair D) h];exact hOff
  · intro i hi
    exact hf i (((UseFocal_pair D) h j i).mpr hi)

lemma rawCommon_pair {L K : LocalList m} (h : D.E.Compatible L K) :
    D.rawCommon L=D.rawCommon K := by
  simp only [Data.rawCommon,D.E.common_ids h (k:=0) (Or.inl rfl),
    D.E.common_ids h (k:=1) (Or.inr rfl)]

lemma rawCommon_entries {L K : LocalList m} (h : D.E.Compatible L K) :
    ∀ i∈D.rawCommon L,L i=K i := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact D.E.common_entries h (Or.inl rfl) i hi
  · exact D.E.common_entries h (Or.inr rfl) i hi

lemma rawBids_pair {L K : LocalList m} (h : D.E.Compatible L K) :
    D.rawBids (D.rawCommon L) L=D.rawBids (D.rawCommon L) K := by
  have hb : ∀ i∈D.rawCommon L,bidVector L i=bidVector K i :=
    fun i hi => congrArg entryBid ((rawCommon_entries D) h i hi)
  have he := enumerate_congr (D.rawCommon L) (bidVector L) (bidVector K) hb
  funext a
  simp only [Data.rawBids,he]
  exact hb _ (enumerate (D.rawCommon L) (bidVector K) a).2

lemma rawParameter_pair {L K : LocalList m} (h : D.E.Compatible L K) (H0 H1 : Fin (m+1)) :
    D.rawParameter (D.rawCommon L) H0 H1 L=D.rawParameter (D.rawCommon L) H0 H1 K := by
  simp only [Data.rawParameter,(rawBids_pair D) h]

lemma rawKey_self (L : LocalList m) :
    D.rawKey L=((D.rawCommon L,ids D.E 2 L),D.finiteCount (ids D.E 3 L)) := by
  apply Prod.ext
  · rfl
  apply Fin.ext
  exact D.E.otherPrivateCount_eq_missing L

lemma rawKey_pair {L K : LocalList m} (h : D.E.Compatible L K) :
    D.rawKey K=((D.rawCommon L,ids D.E 3 L),D.finiteCount (ids D.E 2 L)) := by
  apply Prod.ext (Prod.ext ((rawCommon_pair D) h).symm (D.E.private_ids_missing h))
  apply Fin.ext
  exact D.E.otherPrivateCount_pair (D.E.compatible_symm h)

lemma rawCommon_missing_disjoint (L : LocalList m) :
    Disjoint (D.rawCommon L) (ids D.E 3 L) := by
  apply Finset.disjoint_left.mpr
  intro i hi hm
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (0:Fin 4)≠3) L) hi hm
  · exact Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (1:Fin 4)≠3) L) hi hm

lemma opposite_raw_one {L K : LocalList m} (h : D.E.Compatible L K)
    (i : Fin m) (hi : i∈D.rawCommon L) (u : Seed) :
    i∈(D.rawFallback 1 K u).val ↔
      Sum.inl (rankFin (D.rawCommon L) (bidVector L) ⟨i,hi⟩)∈
        PairedRawPolicy.one (D.rawCommon L).card (ids D.E 2 L).card (ids D.E 3 L).card
          c D.E.R D.E.Rp D.E.H D.ξ
          (D.rawParameter (D.rawCommon L) (D.finiteCount (ids D.E 2 L))
            (D.finiteCount (ids D.E 3 L)) L,privateRow D.E (ids D.E 3 L) K) u.1 := by
  change i∈D.rawFallbackAtKey 1 (D.rawKey K) K u.1 ↔ _
  rw [(rawKey_pair D) h]
  have hd := (rawCommon_missing_disjoint D) L
  simp only [Data.rawFallbackAtKey,dif_pos hd,if_neg (by decide : (1:Fin 2)≠0)]
  rw [mem_transport_common _ _ hd _ _ _ i hi]
  have hb : ∀ k∈D.rawCommon L,bidVector L k=bidVector K k :=
    fun k hk => congrArg entryBid ((rawCommon_entries D) h k hk)
  rw [←rankFin_congr (D.rawCommon L) (bidVector L) (bidVector K) hb,
    ←(rawParameter_pair D) h (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L))]
  rfl

lemma opposite_raw_zero {L K : LocalList m} (h : D.E.Compatible L K)
    (i : Fin m) (hi : i∈D.rawCommon L) (u : Seed) :
    i∈(D.rawFallback 0 K u).val ↔
      Sum.inl (rankFin (D.rawCommon L) (bidVector L) ⟨i,hi⟩)∈
        PairedRawPolicy.zero (D.rawCommon L).card (ids D.E 3 L).card (ids D.E 2 L).card
          c D.E.R D.E.Rp D.E.H D.ξ
          (D.rawParameter (D.rawCommon L) (D.finiteCount (ids D.E 3 L))
            (D.finiteCount (ids D.E 2 L)) L,privateRow D.E (ids D.E 3 L) K) u.1 := by
  change i∈D.rawFallbackAtKey 0 (D.rawKey K) K u.1 ↔ _
  rw [(rawKey_pair D) h]
  have hd := (rawCommon_missing_disjoint D) L
  simp only [Data.rawFallbackAtKey,dif_pos hd,ite_true]
  rw [mem_transport_common _ _ hd _ _ _ i hi]
  have hb : ∀ k∈D.rawCommon L,bidVector L k=bidVector K k :=
    fun k hk => congrArg entryBid ((rawCommon_entries D) h k hk)
  rw [←rankFin_congr (D.rawCommon L) (bidVector L) (bidVector K) hb,
    ←(rawParameter_pair D) h (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L))]
  rfl

lemma rawOppositeMean_zero (L : LocalList m) :
    D.rawOppositeMean 0 L=PairedRawPolicy.mean1 (D.rawCommon L).card
      (ids D.E 2 L).card (ids D.E 3 L).card c D.E.R D.E.Rp D.ξ
      (D.rawParameter (D.rawCommon L) (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 3 L)) L) := by
  have hc : (D.rawKey L).2=D.finiteCount (ids D.E 3 L) :=
    congrArg Prod.snd (rawKey_self D L)
  simp only [Data.rawOppositeMean,ite_true]
  rw [hc]
  rfl

lemma rawOppositeMean_one (L : LocalList m) :
    D.rawOppositeMean 1 L=PairedRawPolicy.mean0 (D.rawCommon L).card
      (ids D.E 3 L).card (ids D.E 2 L).card c D.E.R D.E.Rp D.ξ
      (D.rawParameter (D.rawCommon L) (D.finiteCount (ids D.E 3 L))
        (D.finiteCount (ids D.E 2 L)) L) := by
  have hc : (D.rawKey L).2=D.finiteCount (ids D.E 3 L) :=
    congrArg Prod.snd (rawKey_self D L)
  simp only [Data.rawOppositeMean,if_neg (by decide : (1:Fin 2)≠0)]
  rw [hc]
  rfl

end FCAppendix.Affine.Tail04.NativeRawFactor
