import FCAppendix.Affine.Hybrid.Native02.FullContextPolicy
import FCAppendix.Affine.Hybrid.Native02.NativePhysicalRows

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
namespace FullContext

open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Classical
open scoped BigOperators

variable {N m : ℕ}

def sourceRowContext (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ) :
    ClassifiedContext (N+1) :=
  physicalRowContext b (fun j => physicalRowPoint (kind j, low j, active j))

@[simp] lemma sourceRowContext_zero (kind : Fin N → Fin 4)
    (low active : Fin N → ℝ) (b : ℝ) :
    (sourceRowContext kind low active b).1 0 = some b := rfl

lemma sourceRowContext_succ (kind : Fin N → Fin 4)
    (low active : Fin N → ℝ) (b : ℝ) (j : Fin N) :
    (sourceRowContext kind low active b).1 j.succ =
      if kind j = 0 then some (low j) else if kind j = 1 then some (active j) else none := by
  by_cases h₀ : kind j = 0 <;> by_cases h₁ : kind j = 1 <;>
    simp [sourceRowContext, physicalRowContext, physicalRowPoint, h₀, h₁]

lemma activeSet_sourceRow {d L U : ℝ} (hsep : d < L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) :
    activeSet d (sourceRowContext kind low active b).1 =
      Finset.univ.filter (activePatternPred kind) := by
  ext i
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sourceRowContext_zero, activePatternPred, entryBid, hsep.trans_le hb.1]
  · rw [show (sourceRowContext kind low active b).1 j.succ =
        if kind j = 0 then some (low j) else if kind j = 1 then some (active j) else none
      from sourceRowContext_succ kind low active b j]
    by_cases h₀ : kind j = 0
    · have h₁ : kind j ≠ 1 := by simpa only [h₀] using (show (0 : Fin 4) ≠ 1 by decide)
      simp [activePatternPred, h₀, entryBid, not_lt_of_ge (hlow j).2]
    · by_cases h₁ : kind j = 1
      · simp [activePatternPred, h₁, entryBid, hsep.trans_le (hactive j).1]
      · simp [activePatternPred, h₀, h₁, entryBid]

lemma activeSet_sourceRow_card {d L U : ℝ} (hsep : d < L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) :
    (activeSet d (sourceRowContext kind low active b).1).card =
      Fintype.card (ActivePatternIndex kind) := by
  rw [activeSet_sourceRow hsep kind low active b hlow hactive hb]
  exact (Fintype.card_subtype (activePatternPred kind)).symm

lemma sourceRow_active_box {d L U : ℝ} (hsep : d < L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) :
    ∀ i ∈ activeSet d (sourceRowContext kind low active b).1,
      entryBid ((sourceRowContext kind low active b).1 i) ∈ Icc L U := by
  intro i hi
  rw [activeSet_sourceRow hsep kind low active b hlow hactive hb] at hi
  have hp := (Finset.mem_filter.mp hi).2
  revert hp
  refine Fin.cases ?_ (fun j => ?_) i
  · intro _
    simpa only [sourceRowContext_zero, entryBid] using hb
  · intro hp
    change kind j = 1 at hp
    have h₀ : kind j ≠ 0 := by simpa only [hp] using (show (1 : Fin 4) ≠ 0 by decide)
    simpa only [sourceRowContext_succ, if_neg h₀, if_pos hp, entryBid] using hactive j

lemma lowOnlyList_sourceRow {d L U : ℝ} (hsep : d < L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) :
    lowOnlyList d (sourceRowContext kind low active b).1 =
      Fin.cons none (fun j => if kind j = 0 then some (low j) else none) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact lowOnlyList_above d _ 0 b (sourceRowContext_zero _ _ _ _) (hsep.trans_le hb.1)
  · by_cases h₀ : kind j = 0
    · have he : (sourceRowContext kind low active b).1 j.succ = some (low j) := by
        rw [sourceRowContext_succ, if_pos h₀]
      simpa only [Fin.cons_succ, if_pos h₀] using
        lowOnlyList_some d _ j.succ (low j) he (hlow j).2
    · by_cases h₁ : kind j = 1
      · have he : (sourceRowContext kind low active b).1 j.succ = some (active j) := by
          rw [sourceRowContext_succ, if_neg h₀, if_pos h₁]
        simpa only [Fin.cons_succ, if_neg h₀] using
          lowOnlyList_above d _ j.succ (active j) he (hsep.trans_le (hactive j).1)
      · have he : (sourceRowContext kind low active b).1 j.succ = none := by
          rw [sourceRowContext_succ, if_neg h₀, if_neg h₁]
        simp only [Fin.cons_succ, if_neg h₀, lowOnlyList, TaggedLocal.lowList, he,
          TaggedLocal.tag, show (3:Fin 4) ≠ 0 by decide, if_false]

lemma visibleLow_sourceRow {d L U : ℝ} (hsep : d < L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) :
    visibleCount (lowOnlyList d (sourceRowContext kind low active b).1) =
      classCount 0 (patternRow kind) := by
  rw [lowOnlyList_sourceRow hsep kind low active b hlow hactive hb]
  simp only [visibleCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ne_eq, not_true_eq_false,
    if_false, zero_add, classCount, patternRow]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : kind j = 0 <;> simp only [hj, if_pos, if_neg, reduceCtorEq, not_false_eq_true,
    not_true_eq_false]

lemma sourceRow_upper (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (j : Fin 2) :
    contextUpper j (sourceRowContext kind low active b) = activePatternUpper kind j := by
  fin_cases j <;> rfl

lemma activeSet_reindex (e : Equiv.Perm (Fin m)) (d : ℝ) (X : LocalList m) :
    activeSet d (X ∘ e) = (activeSet d X).map e.symm.toEmbedding := by
  ext i
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.toEmbedding_apply, Function.comp_apply]
  constructor
  · intro hi
    exact ⟨e i, hi, by simp⟩
  · rintro ⟨k, hk, rfl⟩
    simpa only [Equiv.apply_symm_apply] using hk

lemma visibleCount_reindex (e : Equiv.Perm (Fin m)) (X : LocalList m) :
    visibleCount (X ∘ e) = visibleCount X := by
  unfold visibleCount
  have he : Finset.univ.filter (fun i => (X ∘ e) i ≠ none) =
      (Finset.univ.filter (fun i => X i ≠ none)).map e.symm.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply, Function.comp_apply]
    constructor
    · intro hi
      exact ⟨e i, hi, by simp⟩
    · rintro ⟨k, hk, rfl⟩
      simpa only [Equiv.apply_symm_apply] using hk
  rw [he, Finset.card_map]

lemma lowOnlyList_reindex (e : Equiv.Perm (Fin m)) (d : ℝ) (X : LocalList m) :
    lowOnlyList d (X ∘ e) = lowOnlyList d X ∘ e := rfl

theorem useProposal_sourceRow_iff {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) (e : Equiv.Perm (Fin (N+1))) :
    useProposal xi d L U z c μ
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) ↔
      activePatternGuarded xi L U c z kind := by
  have hsep : d < L := hgap.trans (by nlinarith [mul_pos hxi hL])
  let X := sourceRowContext kind low active b
  apply useProposal_iff_activePatternGuarded_of_counts hxi hxi1 d L U z c μ hd hL hgap kind
  · change (activeSet d (X.1 ∘ e)).card = _
    rw [activeSet_reindex, Finset.card_map]
    exact activeSet_sourceRow_card hsep kind low active b hlow hactive hb
  · intro j
    exact sourceRow_upper kind low active b j
  · change visibleCount (lowOnlyList d (X.1 ∘ e)) = _
    rw [lowOnlyList_reindex, visibleCount_reindex]
    exact visibleLow_sourceRow hsep kind low active b hlow hactive hb
  · intro i hi
    change entryBid (X.1 (e i)) ∈ Icc L U
    apply sourceRow_active_box hsep kind low active b hlow hactive hb (e i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

theorem sourceRow_fallback {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) (e : Equiv.Perm (Fin (N+1)))
    (hguard : ¬ activePatternGuarded xi L U c z kind) (j : Fin 2) (s : unitInterval) :
    let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
    (contextPolicy hxi hxi1 d L U z c μ).select j X s =
      NativeContinuation.select xi hxi hxi1 c j X s := by
  have hn : ¬ useProposal xi d L U z c μ
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) :=
    fun h => hguard ((useProposal_sourceRow_iff hxi hxi1 z c μ hd hL hgap
      kind low active b hlow hactive hb e).mp h)
  exact if_neg hn

theorem tableIndex_sourceRow {d L U : ℝ} (hsep : d < L) (z : ℝ) (c : ℕ)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) (e : Equiv.Perm (Fin (N+1))) :
    let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
    tableIndex d L U z c X =
      (activeSet d X.1, activeSet d X.1, activePatternOwner c z kind 0,
        activePatternOwner c z kind 1, activePatternResidual c z kind) := by
  let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
  let A := activeSet d X.1
  have hcard : A.card = Fintype.card (ActivePatternIndex kind) := by
    change (activeSet d ((sourceRowContext kind low active b).1 ∘ e)).card = _
    rw [activeSet_reindex, Finset.card_map]
    exact activeSet_sourceRow_card hsep kind low active b hlow hactive hb
  have hbox : ∀ i ∈ A, entryBid (X.1 i) ∈ Icc L U := by
    intro i hi
    exact sourceRow_active_box hsep kind low active b hlow hactive hb (e i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
  have hBA : boxSet L U X.1 ∩ A = A := by
    apply Finset.inter_eq_right.mpr
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hi).2.1, hbox i hi⟩
  have hc₀ : capacity c A X.2.1 = activePatternCapacity c kind 0 := by
    unfold capacity activePatternCapacity
    rw [hcard]
    congr 1
  have hc₁ : capacity c A X.2.2 = activePatternCapacity c kind 1 := by
    unfold capacity activePatternCapacity
    rw [hcard]
    congr 1
  have ho (j : Fin 2) : ownerCount z A (activePatternCapacity c kind 0)
      (activePatternCapacity c kind 1) j = activePatternOwner c z kind j := by
    fin_cases j <;> simp only [ownerCount, activePatternOwner, activePatternQuota,
      activePatternGap, hcard] <;> norm_num
  change (A, boxSet L U X.1 ∩ A,
    ownerCount z A (capacity c A X.2.1) (capacity c A X.2.2) 0,
    ownerCount z A (capacity c A X.2.1) (capacity c A X.2.2) 1,
    min (capacity c A X.2.1) (capacity c A X.2.2)-exclusiveQuota z A.card) = _
  rw [hBA, hc₀, hc₁, ho 0, ho 1, hcard]
  rfl

end FullContext
end FCAppendix.Affine.Hybrid.Native02
