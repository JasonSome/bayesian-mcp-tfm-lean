import FCAppendix.Affine.Tail04.NativePolicyFactor
import FCAppendix.Affine.Tail04.PrivateIdentitySort
import FCAppendix.Affine.Tail04.OriginalCountSampling
import FCAppendix.Affine.Tail04.SortedAllNoise

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeCountCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair
open NativePolicyFactor PrivateIdentitySort EqualPrivateSignal EqualPrivateUpper
open JoinedHighPolicy LocalHighCommon OriginalPopulation OriginalValues
open scoped BigOperators

local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤

variable {m c : ℕ} (D : Data m c)

lemma own_zero_common (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 1 L) (u : Seed) :
    i∈(D.policy 0 L u).val ↔
      Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)∈
        D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L))
          (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
            (D.finiteCount (ids D.E 3 L)) L,privateRow D.E (ids D.E 2 L) L) u.1 := by
  have ht := (Finset.mem_filter.mp hi).2
  rw [D.policy_high_iff 0 L u i (by simp [ht])]
  unfold Data.high
  rw [D.key_self L]
  have hd : Disjoint (ids D.E 1 L) (ids D.E 2 L) := ids_disjoint D.E (by decide) L
  simp only [Data.highAtKey,dif_pos hd,ite_true]
  exact mem_transport_common _ _ hd _ _ _ i hi

lemma own_one_common (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 1 L) (u : Seed) :
    i∈(D.policy 1 L u).val ↔
      Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)∈
        D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 3 L))
          (D.finiteCount (ids D.E 2 L))
          (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 3 L))
            (D.finiteCount (ids D.E 2 L)) L,privateRow D.E (ids D.E 2 L) L) u.1 := by
  have ht := (Finset.mem_filter.mp hi).2
  rw [D.policy_high_iff 1 L u i (by simp [ht])]
  unfold Data.high
  rw [D.key_self L]
  have hd : Disjoint (ids D.E 1 L) (ids D.E 2 L) := ids_disjoint D.E (by decide) L
  simp only [Data.highAtKey,dif_pos hd,if_neg (by decide : (1:Fin 2)≠0)]
  exact mem_transport_common _ _ hd _ _ _ i hi

lemma mem_transport_private (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (b k : Fin m → ℝ) (S : Finset (Target A.card P.card)) (i : Fin m) (hi : i∈P) :
    i∈transport A P hAP b k S ↔ Sum.inr (rankFin P k ⟨i,hi⟩)∈S := by
  simpa [targetEmbedding]
    using mem_transport A P hAP b k S (Sum.inr (rankFin P k ⟨i,hi⟩))

lemma own_zero_private (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 2 L) (u : Seed) :
    i∈(D.policy 0 L u).val ↔
      Sum.inr (rankFin (ids D.E 2 L) (privateKey D.E L) ⟨i,hi⟩)∈
        D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L))
          (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
            (D.finiteCount (ids D.E 3 L)) L,privateRow D.E (ids D.E 2 L) L) u.1 := by
  have ht := (Finset.mem_filter.mp hi).2
  rw [D.policy_high_iff 0 L u i (by simp [ht])]
  unfold Data.high
  rw [D.key_self L]
  have hd : Disjoint (ids D.E 1 L) (ids D.E 2 L) := ids_disjoint D.E (by decide) L
  simp only [Data.highAtKey,dif_pos hd,ite_true]
  exact mem_transport_private _ _ hd _ _ _ i hi

lemma own_one_private (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 2 L) (u : Seed) :
    i∈(D.policy 1 L u).val ↔
      Sum.inr (rankFin (ids D.E 2 L) (privateKey D.E L) ⟨i,hi⟩)∈
        D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 3 L))
          (D.finiteCount (ids D.E 2 L))
          (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 3 L))
            (D.finiteCount (ids D.E 2 L)) L,privateRow D.E (ids D.E 2 L) L) u.1 := by
  have ht := (Finset.mem_filter.mp hi).2
  rw [D.policy_high_iff 1 L u i (by simp [ht])]
  unfold Data.high
  rw [D.key_self L]
  have hd : Disjoint (ids D.E 1 L) (ids D.E 2 L) := ids_disjoint D.E (by decide) L
  simp only [Data.highAtKey,dif_pos hd,if_neg (by decide : (1:Fin 2)≠0)]
  exact mem_transport_private _ _ hd _ _ _ i hi

def listPairCount (L K : LocalList m) (i : Fin m) (u v : Seed) : Fin 3 :=
  boolPairCount (decide (i∈(D.completedPolicy 0 L u).val),
    decide (i∈(D.completedPolicy 1 K v).val))

theorem listPairCount_common {L K : LocalList m} (h : D.E.Compatible L K)
    (hL : D.offCommon L=∅) (hK : D.offCommon K=∅)
    (i : Fin m) (hi : i∈ids D.E 1 L) (u v : Seed) :
    (listPairCount D) L K i u v=
      originalPairCount
        (D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)) L)
        (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
        (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
        ((privateRow D.E (ids D.E 2 L) L,u.1),
          (privateRow D.E (ids D.E 3 L) K,v.1)) := by
  unfold listPairCount originalPairCount localAccept
  rw [D.completed_on_menu 0 L hL u,D.completed_on_menu 1 K hK v]
  simp only [own_zero_common D L i hi u,opposite_one_factor D h i hi v]

theorem boundedCount_eq_listPairCount (x : Realization m 2) (s : Fin 2 → Seed) (i : Fin m) :
    Game.boundedCount x D.completedPolicy s i=
      (listPairCount D) (observe x 0) (observe x 1) i (s 0) (s 1) := by
  apply Fin.ext
  simp only [Game.boundedCount,inclusionCount_eq_sum,Fin.sum_univ_two,
    allocation,listPairCount,boolPairCount,decide_eq_true_eq]
  rfl

theorem native_common_count (x : Realization m 2)
    (h : D.E.Compatible (observe x 0) (observe x 1))
    (hmenu : ∀ j,D.offCommon (observe x j)=∅)
    (s : Fin 2 → Seed) (i : Fin m) (hi : i∈ids D.E 1 (observe x 0)) :
    let L := observe x 0
    Game.boundedCount x D.completedPolicy s i=
      originalPairCount
        (D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)) L)
        (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
        (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
        ((privateRow D.E (ids D.E 2 L) L,(s 0).1),
          (privateRow D.E (ids D.E 3 L) (observe x 1),(s 1).1)) := by
  dsimp only
  rw [boundedCount_eq_listPairCount D]
  exact listPairCount_common D h (hmenu 0) (hmenu 1) i hi (s 0) (s 1)

theorem source_common_count (P : ValueParameters) (t : ℝ) (d : UserProfile m 2)
    (hd : ∀ i,sourceBands P D.E t (d i).1) (s : Fin 2 → Seed)
    (i : Fin m) (hi : i∈ids D.E 1 (observe (drawsRealization d) 0)) :
    let L := observe (drawsRealization d) 0
    Game.boundedCount (drawsRealization d) D.completedPolicy s i=
      originalPairCount
        (D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)) L)
        (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
        (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
        ((privateRow D.E (ids D.E 2 L) L,(s 0).1),
          (privateRow D.E (ids D.E 3 L) (observe (drawsRealization d) 1),(s 1).1)) := by
  exact native_common_count D (drawsRealization d)
    (by simpa only [Hybrid.otherProposer,ite_true,ite_false] using D.E.source_list_compatible P t d hd 0)
    (fun j => D.source_on_menu P t d hd j) s i hi

theorem listPairCount_private_zero {L K : LocalList m} (h : D.E.Compatible L K)
    (hL : D.offCommon L=∅) (i : Fin m) (hi : i∈ids D.E 2 L) (u v : Seed) :
    (listPairCount D) L K i u v=
      boolPairCount (localAccept
        (D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)) L)
        (Sum.inr (rankFin (ids D.E 2 L) (privateKey D.E L) ⟨i,hi⟩))
        (privateRow D.E (ids D.E 2 L) L,u.1),false) := by
  have ha := opposite_private_absent D h 0 i (Finset.mem_filter.mp hi).2 v
  have ha' : i∉(D.completedPolicy 1 K v).val := by
    simpa only [Hybrid.otherProposer,show (1 : Fin 2) ≠ 0 by decide,ite_true,ite_false] using ha
  unfold listPairCount localAccept
  rw [D.completed_on_menu 0 L hL u]
  simp only [own_zero_private D L i hi u,ha',decide_false]
  rfl

theorem listPairCount_private_one {L K : LocalList m} (h : D.E.Compatible L K)
    (hK : D.offCommon K=∅) (i : Fin m) (hi : i∈ids D.E 2 K) (u v : Seed) :
    (listPairCount D) L K i u v=
      boolPairCount (false,localAccept
        (D.oneSampler (ids D.E 1 K).card (D.finiteCount (ids D.E 3 K))
          (D.finiteCount (ids D.E 2 K)))
        (D.parameter (ids D.E 1 K) (D.finiteCount (ids D.E 3 K))
          (D.finiteCount (ids D.E 2 K)) K)
        (Sum.inr (rankFin (ids D.E 2 K) (privateKey D.E K) ⟨i,hi⟩))
        (privateRow D.E (ids D.E 2 K) K,v.1)) := by
  have ha := opposite_private_absent D (D.E.compatible_symm h) 1 i (Finset.mem_filter.mp hi).2 u
  have ha' : i∉(D.completedPolicy 0 L u).val := by
    simpa only [Hybrid.otherProposer,show (1 : Fin 2) ≠ 0 by decide,ite_true,ite_false] using ha
  unfold listPairCount localAccept
  rw [D.completed_on_menu 1 K hK v]
  simp only [own_one_private D K i hi v,ha',decide_false]
  rfl

section Baseline
variable (E : Observable.Regions)

def baselineCommon (A : Finset (Fin m)) (L : LocalList m)
    (hA : ∀ i∈A,entryBid (L i)∈Icc (1:ℝ) E.U) :
    Fin A.card → Icc (1:ℝ) E.U :=
  fun k => ⟨entryBid (L (baselineEmbedding A k)),hA _ (baseline A k).2⟩

theorem activeBids_eq_sorted_baseline (A : Finset (Fin m)) (L : LocalList m)
    (hA : ∀ i∈A,entryBid (L i)∈Icc (1:ℝ) E.U) :
    activeBids E A L=SortedAllNoise.sortedBox (baselineCommon E A L hA) := by
  funext k
  apply Subtype.ext
  rw [activeBids_exact E A L hA]
  have he := congrArg Subtype.val (baseline_position A (bidVector L) k)
  change entryBid (L (enumerate A (bidVector L) k))=
    entryBid (L (baselineEmbedding A
      (PrivateRowSorting.permutation (fun j => entryBid (L (baselineEmbedding A j))) k)))
  rw [←he]
  rfl

theorem common_rank_eq_focalRank (A : Finset (Fin m)) (L : LocalList m)
    (hA : ∀ i∈A,entryBid (L i)∈Icc (1:ℝ) E.U) (k : Fin A.card) :
    rankFin A (bidVector L) (baseline A k)=
      SortedAllNoise.focalRank (fun j => (baselineCommon E A L hA j:ℝ)) k :=
  baseline_rank A (bidVector L) k

theorem private_rank_eq_focalRank (P : Finset (Fin m)) (L : LocalList m)
    (k : Fin P.card) :
    rankFin P (privateKey E L) (baseline P k)=
      (PrivateRowSorting.permutation (fun j =>
        LocalCoordinates.signalKey E (signalEntry (LocalCoordinates.decode E (entryBid (L (baselineEmbedding P j))))))).symm k :=
  baseline_rank P (privateKey E L) k

end Baseline
end FCAppendix.Affine.Tail04.NativeCountCoordinates
