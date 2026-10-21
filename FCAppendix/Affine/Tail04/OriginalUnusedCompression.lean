import FCAppendix.Affine.Tail04.ZeroCommonMenuCount
import FCAppendix.Affine.Tail04.NativeWeightedFlagBound

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalUnusedCompression
open MeasureTheory ProbabilityTheory Set Classical
open FiniteTailNoisyGame OriginalActiveCompression ZeroCommonMenuCount
open OriginalFlagCompression OriginalActiveTwoPrefix Hybrid
open scoped BigOperators

variable (D : Data) {X : Type*} [MeasurableSpace X]
  (tag : X→ Fin 4) (decode : X→ Icc (1:ℝ) D.U) (N : ℕ)

def enumeration (r : Fin N→ X) :
    Fin (D.count (tags tag r) 1)≃Active (fun j=> tagFlag tag 1 (r j)) :=
  (OriginalActiveCompression.enumeration D (tags tag r) 1).trans
    (predicateEquiv (Equiv.refl _) (fun j=> tag (r j)=1)
      (fun j=> tagFlag tag 1 (r j)=true) (fun j=> by simp [tagFlag]))

def sortedEnumeration (r : Fin N→ X) :
    Fin (D.count (tags tag r) 1)≃Active (fun j=> tagFlag tag 1 (r j)) :=
  (PrivateRowSorting.permutation
    (fun j=>(baseCommonRow D decode (tags tag r) r j:ℝ))).trans
      (enumeration D tag N r)

omit [MeasurableSpace X] in
theorem compressed_sorted (r : Fin N→ X) :
    compressedBids _ (sortedEnumeration D tag decode N r)
      (fun j=>(decode (r j):ℝ))=
        TypicalGuard.bids (SortedAllNoise.sortedBox
          (baseCommonRow D decode (tags tag r) r)) := by
  funext j
  rfl

def bulk (E : Set X) (r : Fin N→ X) : Finset (Fin (D.count (tags tag r) 1)) :=
  Finset.univ.filter (fun j=> r (sortedEnumeration D tag decode N r j).val∈E)

omit [MeasurableSpace X] in
theorem bulk_card (E : Set X) (hE : ∀x∈E,tag x=1) (r : Fin N→ X) :
    (bulk D tag decode N E r).card=Probability.sampleCount E r := by
  unfold bulk
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  have hs:=sum_compression (fun j=> tagFlag tag 1 (r j))
    (sortedEnumeration D tag decode N r) (fun j=> if r j∈E then (1:ℕ) else 0)
  change (∑j,if r (sortedEnumeration D tag decode N r j).val∈E then (1:ℕ) else 0)=_
  rw [hs]
  unfold Probability.sampleCount
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : r j∈E
  · simp only [if_pos hj,tagFlag,hE (r j) hj,decide_true,if_true]
  · simp only [if_neg hj,ite_self]

omit [MeasurableSpace X] in
theorem bulk_nonempty (E : Set X) (hE : ∀x∈E,tag x=1)
    (r : Fin N→ X) {w : ℝ} (hw : 0< w) (hN : 0< N)
    (hr : w*(N:ℝ)/2≤(Probability.sampleCount E r:ℝ)) :
    (bulk D tag decode N E r).Nonempty := by
  apply Finset.card_pos.mp
  rw [bulk_card D tag decode N E hE r]
  have hpos : (0:ℝ)<(Probability.sampleCount E r:ℝ) :=
    (half_pos (mul_pos hw (Nat.cast_pos.mpr hN))).trans_le hr
  exact Nat.cast_pos.mp hpos

omit [MeasurableSpace X] in
theorem bulk_bid_bounds (E : Set X) {u : ℝ}
    (hE : ∀x∈E,(decode x:ℝ)≤1+u) (r : Fin N→ X)
    (j : Fin (D.count (tags tag r) 1)) (hj : j∈bulk D tag decode N E r) :
    TypicalGuard.bids (SortedAllNoise.sortedBox
      (baseCommonRow D decode (tags tag r) r)) j∈Icc (1:ℝ) (1+u) := by
  rw [←compressed_sorted D tag decode N r]
  exact ⟨(decode (r (sortedEnumeration D tag decode N r j).val)).2.1,
    hE _ (Finset.mem_filter.mp hj).2⟩

end FCAppendix.Affine.Tail04.OriginalUnusedCompression
