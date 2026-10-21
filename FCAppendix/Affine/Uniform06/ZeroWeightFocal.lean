import FCAppendix.Affine.Uniform06.FiniteSampledLaplace

noncomputable section
namespace FCAppendix.Affine.Uniform06.ZeroWeightFocal

open MeasureTheory Set
open scoped BigOperators
open FCAppendix.Affine.WeightedSampling PathNumerator

variable {N : ℕ} [Nonempty (Fin N)]

def liftWeights (w : Weights (Fin N)) : Weights (Fin (N+1)) :=
  ⟨Fin.cons 0 w.val,by
    intro j
    refine Fin.cases ?_ (fun q => ?_) j
    · norm_num
    · simpa using w.property q⟩

def liftSet (S : Finset (Fin N)) : Finset (Fin (N+1)) := S.image Fin.succ

def liftPath : (k : ℕ) → Path (Fin N) k → Path (Fin (N+1)) k
  | 0,_ => PUnit.unit
  | k+1,p => (p.1.succ,liftPath k p.2)

lemma zero_not_liftSet (S : Finset (Fin N)) : (0:Fin (N+1)) ∉ liftSet S := by
  simp [liftSet]

omit [Nonempty (Fin N)] in
lemma succ_mem_liftSet (S : Finset (Fin N)) (j : Fin N) :
    j.succ ∈ liftSet S ↔ j ∈ S := by
  simp [liftSet]

omit [Nonempty (Fin N)] in
lemma liftSet_insert (S : Finset (Fin N)) (j : Fin N) :
    liftSet (insert j S)=insert j.succ (liftSet S) := by simp [liftSet]

omit [Nonempty (Fin N)] in
lemma liftSet_card (S : Finset (Fin N)) : (liftSet S).card=S.card :=
  Finset.card_image_of_injective S (Fin.succ_injective N)

omit [Nonempty (Fin N)] in
lemma lift_total (w : Weights (Fin N)) : totalWeight (liftWeights w)=totalWeight w := by
  unfold totalWeight liftWeights
  rw [Fin.sum_univ_succ]
  simp

lemma lift_remaining (w : Weights (Fin N)) (S : Finset (Fin N)) :
    remainingWeight (liftWeights w) (liftSet S)=remainingWeight w S := by
  unfold remainingWeight
  rw [Fin.sum_univ_succ]
  simp only [zero_not_liftSet,if_false,liftWeights,Fin.cons_zero,zero_add,
    succ_mem_liftSet,Fin.cons_succ]

lemma lift_oneDraw_zero (w : Weights (Fin N)) (S : Finset (Fin N))
    (hW : 0 < remainingWeight w S) :
    (oneDraw (liftWeights w) (liftSet S)).mass 0=0 := by
  rw [oneDraw_mass _ _ (by simpa only [lift_remaining] using hW)]
  simp [zero_not_liftSet,liftWeights]

lemma lift_oneDraw_succ (w : Weights (Fin N)) (S : Finset (Fin N))
    (hW : 0 < remainingWeight w S) (j : Fin N) :
    (oneDraw (liftWeights w) (liftSet S)).mass j.succ=(oneDraw w S).mass j := by
  rw [oneDraw_mass _ _ (by simpa only [lift_remaining] using hW),oneDraw_mass _ _ hW]
  rw [lift_remaining]
  simp only [succ_mem_liftSet,liftWeights,Fin.cons_succ]

omit [Nonempty (Fin N)] in
theorem tuple_lift (k : ℕ) (p : Path (Fin N) k) :
    tuple k (liftPath k p)=fun j => (tuple k p j).succ := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext j
    refine Fin.cases ?_ (fun q => ?_) j
    · rfl
    · simp only [tuple,liftPath,Fin.cons_succ,ih]

omit [Nonempty (Fin N)] in
theorem finalSet_lift (k : ℕ) (S : Finset (Fin N)) (p : Path (Fin N) k) :
    finalSet k (liftSet S) (liftPath k p)=liftSet (finalSet k S p) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [finalSet,liftPath,← liftSet_insert,ih]

omit [Nonempty (Fin N)] in
theorem selectedSum_lift (h : Fin (N+1) → ℝ) (k : ℕ) (p : Path (Fin N) k) :
    selectedSum h k (liftPath k p)=selectedSum (fun j => h j.succ) k p := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [selectedSum,liftPath,ih]

theorem expect_lift (w : Weights (Fin N)) (k : ℕ) (S : Finset (Fin N))
    (hbudget : (S.card:ℝ)+(k:ℝ) < totalWeight w)
    (F : Path (Fin (N+1)) k → ℝ) :
    (pathLaw (liftWeights w) k (liftSet S)).expect F=
      (pathLaw w k S).expect (fun p => F (liftPath k p)) := by
  induction k generalizing S with
  | zero => simp [pathLaw,liftPath,FCAppendix.FiniteLaw.expect_dirac]
  | succ k ih =>
    have hrem : 0 < remainingWeight w S := by
      have hh := denominator_lower w S
      have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
      push_cast at hbudget
      linarith
    rw [expect_path_succ,expect_path_succ,expect_def,expect_def,Fin.sum_univ_succ,
      lift_oneDraw_zero w S hrem,zero_mul,zero_add]
    apply Finset.sum_congr rfl
    intro j _
    rw [lift_oneDraw_succ w S hrem j]
    congr 1
    have hnext : ((insert j S).card:ℝ)+(k:ℝ) < totalWeight w := by
      have hc : ((insert j S).card:ℝ) ≤ (S.card:ℝ)+1 := by
        exact_mod_cast Finset.card_insert_le j S
      push_cast at hbudget
      linarith
    have hh := ih (insert j S) hnext (fun p => F (j.succ,p))
    simpa only [liftSet_insert,liftPath] using! hh

omit [Nonempty (Fin N)] in
lemma numeratorSum_succ (w : Weights (Fin N)) (k : ℕ) (S : Finset (Fin N))
    (F : Path (Fin N) (k+1) → ℝ) :
    numeratorSum w (k+1) S F=
      ∑ j,(if j ∈ S then 0 else w.val j)*
        numeratorSum w k (insert j S) (fun p => F (j,p)) := by
  unfold numeratorSum
  change (∑ p : Fin N × Path (Fin N) k,
    ((if p.1 ∈ S then 0 else w.val p.1)*numerator w k (insert p.1 S) p.2)*F p) = _
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum,mul_assoc]

theorem numeratorSum_lift (w : Weights (Fin N)) (k : ℕ) (S : Finset (Fin N))
    (F : Path (Fin (N+1)) k → ℝ) :
    numeratorSum (liftWeights w) k (liftSet S) F=
      numeratorSum w k S (fun p => F (liftPath k p)) := by
  induction k generalizing S with
  | zero =>
    unfold numeratorSum
    change (∑ p : PUnit, (1:ℝ)*F p) = ∑ p : PUnit, (1:ℝ)*F (liftPath 0 p)
    simp [liftPath]
  | succ k ih =>
    rw [numeratorSum_succ,numeratorSum_succ,Fin.sum_univ_succ]
    simp only [zero_not_liftSet,if_false,liftWeights,Fin.cons_zero,zero_mul,zero_add,
      succ_mem_liftSet,Fin.cons_succ]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have hh := ih (insert j S) (fun p => F (j.succ,p))
    simpa only [liftSet_insert,liftPath] using! hh

theorem embedding_sum_lift (w : Weights (Fin N)) (k : ℕ)
    (F : (Fin k → Fin (N+1)) → ℝ) :
    (∑ f : Fin k ↪ Fin (N+1),(∏ j,(liftWeights w).val (f j))*F f)=
      ∑ f : Fin k ↪ Fin N,(∏ j,w.val (f j))*F (fun j => (f j).succ) := by
  have hh := numeratorSum_lift w k ∅ (fun p => F (tuple k p))
  simp only [liftSet,Finset.image_empty,tuple_lift] at hh
  rw [numeratorSum_eq_embeddings] at hh
  have he := numeratorSum_eq_embeddings w k (fun v => F (fun j => (v j).succ))
  exact hh.trans he

end FCAppendix.Affine.Uniform06.ZeroWeightFocal
