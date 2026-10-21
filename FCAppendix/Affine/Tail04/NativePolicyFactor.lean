import FCAppendix.Affine.Tail04.NativeObservationPair

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePolicyFactor
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper Hybrid

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (D : Data m c)

lemma mem_transport_common (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (b k : Fin m → ℝ) (S : Finset (Target A.card P.card)) (i : Fin m) (hi : i∈A) :
    i∈transport A P hAP b k S ↔ Sum.inl (rankFin A b ⟨i,hi⟩)∈S := by
  simpa [targetEmbedding]
    using mem_transport A P hAP b k S (Sum.inl (rankFin A b ⟨i,hi⟩))

lemma opposite_one_factor {L K : LocalList m} (h : D.E.Compatible L K)
    (i : Fin m) (hi : i∈ids D.E 1 L) (u : Seed) :
    i∈(D.policy 1 K u).val ↔
      Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)∈
        D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L))
          (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
            (D.finiteCount (ids D.E 3 L)) L,privateRow D.E (ids D.E 3 L) K) u.1 := by
  have ht : D.E.localTag (K i)=1 :=
    (D.E.entry_common_tag (h i) (Or.inr rfl)).mp (Finset.mem_filter.mp hi).2
  rw [D.policy_high_iff 1 K u i (by simp [ht])]
  unfold Data.high
  rw [D.key_pair h]
  have hd : Disjoint (ids D.E 1 L) (ids D.E 3 L) := ids_disjoint D.E (by decide) L
  simp only [Data.highAtKey,dif_pos hd,if_neg (by decide : (1:Fin 2)≠0)]
  rw [mem_transport_common _ _ hd _ _ _ i hi]
  have hb : ∀ k∈ids D.E 1 L,bidVector L k=bidVector K k :=
    fun k hk => congrArg entryBid (D.E.common_entries h (Or.inr rfl) k hk)
  rw [←rankFin_congr (ids D.E 1 L) (bidVector L) (bidVector K) hb,
    ←D.parameter_pair h (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L))]
  rfl

lemma opposite_zero_factor {L K : LocalList m} (h : D.E.Compatible L K)
    (i : Fin m) (hi : i∈ids D.E 1 L) (u : Seed) :
    i∈(D.policy 0 K u).val ↔
      Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)∈
        D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 3 L))
          (D.finiteCount (ids D.E 2 L))
          (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 3 L))
            (D.finiteCount (ids D.E 2 L)) L,privateRow D.E (ids D.E 3 L) K) u.1 := by
  have ht : D.E.localTag (K i)=1 :=
    (D.E.entry_common_tag (h i) (Or.inr rfl)).mp (Finset.mem_filter.mp hi).2
  rw [D.policy_high_iff 0 K u i (by simp [ht])]
  unfold Data.high
  rw [D.key_pair h]
  have hd : Disjoint (ids D.E 1 L) (ids D.E 3 L) := ids_disjoint D.E (by decide) L
  simp only [Data.highAtKey,dif_pos hd,ite_true]
  rw [mem_transport_common _ _ hd _ _ _ i hi]
  have hb : ∀ k∈ids D.E 1 L,bidVector L k=bidVector K k :=
    fun k hk => congrArg entryBid (D.E.common_entries h (Or.inr rfl) k hk)
  rw [←rankFin_congr (ids D.E 1 L) (bidVector L) (bidVector K) hb,
    ←D.parameter_pair h (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L))]
  rfl

lemma opposite_low_factor {L K : LocalList m} (h : D.E.Compatible L K)
    (j : Fin 2) (i : Fin m) (hi : D.E.localTag (L i)=0) (u : Seed) :
    i∈(D.policy (otherProposer j) K u).val ↔
      i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)
        (Observable.Regions.lowContext D.E j L) u.2 := by
  have ht : D.E.localTag (K i)=0 :=
    (D.E.entry_common_tag (h i) (Or.inl rfl)).mp hi
  rw [D.policy_low_iff (otherProposer j) K u i ht]
  simp only [Observable.Regions.lowSelect,←D.E.lowContext_pair h j]

lemma opposite_private_absent {L K : LocalList m} (h : D.E.Compatible L K)
    (j : Fin 2) (i : Fin m) (hi : D.E.localTag (L i)=2) (u : Seed) :
    i∉(D.completedPolicy (otherProposer j) K u).val := by
  intro hin
  exact (D.completedPolicy (otherProposer j) K u).property.2 i hin
    ((D.E.entry_private_other_absent (h i)).mp hi)

lemma oppositeActiveMean_zero (L : LocalList m) :
    D.oppositeActiveMean 0 L=D.zeroMean (ids D.E 1 L).card
      (D.finiteCount (ids D.E 2 L)) (D.finiteCount (ids D.E 3 L))
      (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 3 L)) L) := by
  have hc : (key D.E L).2 = D.finiteCount (ids D.E 3 L) :=
    congrArg Prod.snd (D.key_self L)
  simp only [Data.oppositeActiveMean,hc,ite_true]
  rfl

lemma oppositeActiveMean_one (L : LocalList m) :
    D.oppositeActiveMean 1 L=D.oneMean (ids D.E 1 L).card
      (D.finiteCount (ids D.E 3 L)) (D.finiteCount (ids D.E 2 L))
      (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 3 L))
        (D.finiteCount (ids D.E 2 L)) L) := by
  have hc : (key D.E L).2 = D.finiteCount (ids D.E 3 L) :=
    congrArg Prod.snd (D.key_self L)
  simp only [Data.oppositeActiveMean,if_neg (by decide : (1:Fin 2)≠0)]
  rw [hc]
  rfl

end FCAppendix.Affine.Tail04.NativePolicyFactor
