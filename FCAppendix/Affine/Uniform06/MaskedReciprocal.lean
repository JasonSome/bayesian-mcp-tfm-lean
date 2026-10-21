import FCAppendix.Affine.Uniform06.FixedPriceRawDerivative
import FCAppendix.Affine.Uniform06.RareSourceReciprocal

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.MaskedReciprocal

open Set MeasureTheory LowBody
open LiteralExperiment LiteralKernelIdentity FixedPriceRawDerivative
open ReciprocalSecantBounds RareEmpiricalReplacement
open scoped BigOperators

variable {N : ℕ}

def rivalBid (r : Fin N → RowRival) (j : Fin N) : ℝ :=
  if (r j).1=0 then (r j).2 else 0

lemma reciprocal_zero {z : ℝ} (hz : 0 < z) : reciprocalTerm 0 z=0 := by
  simp only [reciprocalTerm,if_neg (not_lt.mpr hz.le)]

lemma rival_reciprocal_eq (r : Fin N → RowRival) {z : ℝ} (hz : 0 < z) (j : Fin N) :
    reciprocalTerm (rivalBid r j) z=FullReciprocalMean.reciprocal z (r j) := by
  by_cases ht : (r j).1=0
  · simp only [rivalBid,FullReciprocalMean.reciprocal,FullReciprocalMean.lowerTest,if_pos ht]
  · simp only [rivalBid,FullReciprocalMean.reciprocal,FullReciprocalMean.lowerTest,
      if_neg ht,reciprocal_zero hz]

theorem masked_reciprocal_eq (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1))) {z : ℝ} (hz : 0 < z) (b : ℝ) :
    reciprocalSum (maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids b r) E) {0} z=
      reciprocalSum (rivalBid r) (rivalDeletion E) z := by
  unfold reciprocalSum
  rw [Fin.sum_univ_succ]
  simp only [Finset.mem_singleton,Fin.succ_ne_zero,if_false,if_true,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : j.succ ∈ E
  · simp [maskedBids,he,reciprocal_zero hz]
  · by_cases ht : (r j).1=0
    · simp [maskedBids,he,ht,succ_mem,rowBids,rivalBid]
    · simp [maskedBids,he,ht,succ_mem,rivalBid,reciprocal_zero hz]

theorem rivalDeletion_card_le (E : Finset (Fin (N+1))) :
    (rivalDeletion E).card ≤ E.card := by
  let e : Fin N ↪ Fin (N+1) := ⟨fun j => j.succ,by intro j k h; simpa using h⟩
  have hs : (rivalDeletion E).map e ⊆ E := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
    exact (mem_rivalDeletion E k).mp hk
  simpa only [Finset.card_map] using Finset.card_le_card hs

theorem masked_reciprocal_empirical_error (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1))) {lo z ν : ℝ} (hlo : 0 < lo) (hz : lo ≤ z)
    (hN : 0 < N) (b : ℝ) :
    |reciprocalSum (maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids b r) E) {0} z/
      (N:ℝ)-ν| ≤ |empirical (FullReciprocalMean.reciprocal z) N r-ν|+
        (E.card:ℝ)/(lo*(N:ℝ)) := by
  have hz0 := hlo.trans_le hz
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  rw [masked_reciprocal_eq C r E hz0 b]
  have he := EntryReciprocalLimit.reciprocal_deletion_bound (rivalBid r) (rivalDeletion E) hlo hz
  have he' := he.trans (div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (rivalDeletion_card_le E)) hlo.le)
  have hs : (∑ j,reciprocalTerm (rivalBid r j) z)=
      ∑ j,FullReciprocalMean.reciprocal z (r j) :=
    Finset.sum_congr rfl (fun j _ => rival_reciprocal_eq r hz0 j)
  rw [hs] at he'
  have hdiv : |reciprocalSum (rivalBid r) (rivalDeletion E) z/(N:ℝ)-
      empirical (FullReciprocalMean.reciprocal z) N r| ≤ (E.card:ℝ)/(lo*(N:ℝ)) := by
    unfold empirical
    rw [← sub_div,abs_div,abs_of_pos hNr]
    simpa only [div_div] using div_le_div_of_nonneg_right he' hNr.le
  exact ((abs_sub_le (reciprocalSum (rivalBid r) (rivalDeletion E) z/(N:ℝ))
    (empirical (FullReciprocalMean.reciprocal z) N r) ν).trans
      (add_le_add hdiv le_rfl)).trans_eq (add_comm _ _)

theorem masked_boundary_count_le (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1))) {a b : ℝ} (ha : 0 < a) (focal : ℝ) :
    (boundaryCount (maskedBids (patternTemplate C (fun j => (r j).1))
      (rowBids focal r) E) {0} a b:ℝ) ≤
        ∑ j,FullReciprocalMean.window a b (r j) := by
  let e : Fin N ↪ Fin (N+1) := ⟨fun j => j.succ,by intro j k h; simpa using h⟩
  let A := Finset.univ.filter (fun j : Fin N => j.succ ∉ E ∧ (r j).1=0 ∧ a<(r j).2 ∧ (r j).2≤ b)
  let A0 := Finset.univ.filter (fun j : Fin N => (r j).1=0 ∧ a<(r j).2 ∧ (r j).2≤ b)
  have he : Finset.univ.filter (fun j : Fin (N+1) => j ∉ ({0}:Finset (Fin (N+1))) ∧
      a< maskedBids (patternTemplate C (fun k => (r k).1)) (rowBids focal r) E j ∧
        maskedBids (patternTemplate C (fun k => (r k).1)) (rowBids focal r) E j≤ b)=A.map e := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [A,e]
    · by_cases hE : k.succ ∈ E
      · simp [A,e,maskedBids,hE,not_lt.mpr ha.le]
      · by_cases ht : (r k).1=0
        · simp [A,e,maskedBids,hE,ht,succ_mem,rowBids]
        · simp [A,e,maskedBids,hE,ht,succ_mem,rowBids,not_lt.mpr ha.le]
  have hAA : A ⊆ A0 := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.2⟩
  have hsum : (A0.card:ℝ)=∑ j,FullReciprocalMean.window a b (r j) := by
    calc
      (A0.card:ℝ) = ∑ _j ∈ A0,(1:ℝ) := by simp
      _ = ∑ j,FullReciprocalMean.window a b (r j) := by
        dsimp [A0]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases ht : (r j).1=0
        · simp [FullReciprocalMean.window,FullReciprocalMean.lowerTest,ht]
        · simp [FullReciprocalMean.window,FullReciprocalMean.lowerTest,ht]
  unfold boundaryCount
  rw [he,Finset.card_map,← hsum]
  exact Nat.cast_le.mpr (Finset.card_le_card hAA)

theorem masked_boundary_empirical_bound (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1))) {a b : ℝ} (ha : 0 < a) (_hN : 0 < N) (focal : ℝ) :
    (boundaryCount (maskedBids (patternTemplate C (fun j => (r j).1))
      (rowBids focal r) E) {0} a b:ℝ)/(a*(N:ℝ)) ≤
        empirical (FullReciprocalMean.window a b) N r/a := by
  have hh := div_le_div_of_nonneg_right (masked_boundary_count_le C r E (b := b) ha focal)
    (mul_nonneg ha.le (Nat.cast_nonneg N))
  convert! hh using 1
  unfold empirical
  ring

end FCAppendix.Affine.Uniform06.MaskedReciprocal
