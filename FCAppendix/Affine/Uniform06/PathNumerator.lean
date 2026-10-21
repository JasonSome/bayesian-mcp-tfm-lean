import FCAppendix.Affine.Uniform06.RawMarkedLaplace

noncomputable section
namespace FCAppendix.Affine.Uniform06.PathNumerator

open MeasureTheory Set
open scoped BigOperators
open FCAppendix.Affine.WeightedSampling
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def tuple : (k : ℕ) → Path ι k → (Fin k → ι)
  | 0,_ => Fin.elim0
  | k+1,p => Fin.cons p.1 (tuple k p.2)

def ofTuple : (k : ℕ) → (Fin k → ι) → Path ι k
  | 0,_ => PUnit.unit
  | k+1,v => (v 0,ofTuple k (fun j => v j.succ))

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem tuple_ofTuple (k : ℕ) (v : Fin k → ι) : tuple k (ofTuple k v)=v := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    simp only [tuple,ofTuple,ih]
    exact Fin.cons_self_tail v

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem ofTuple_tuple (k : ℕ) (p : Path ι k) : ofTuple k (tuple k p)=p := by
  induction k with
  | zero => cases p; rfl
  | succ k ih =>
    simp only [tuple,ofTuple,Fin.cons_zero,Fin.cons_succ,ih]
    exact Prod.eta p

def tupleEquiv (k : ℕ) : Path ι k ≃ (Fin k → ι) where
  toFun := tuple k
  invFun := ofTuple k
  left_inv := ofTuple_tuple k
  right_inv := tuple_ofTuple k

def valid : (k : ℕ) → Finset ι → Path ι k → Prop
  | 0,_,_ => True
  | k+1,S,p => p.1 ∉ S ∧ valid k (insert p.1 S) p.2

def numerator (w : Weights ι) : (k : ℕ) → Finset ι → Path ι k → ℝ
  | 0,_,_ => 1
  | k+1,S,p => (if p.1 ∈ S then 0 else w.1 p.1)*numerator w k (insert p.1 S) p.2

omit [Fintype ι] [Nonempty ι] in
theorem numerator_nonneg (w : Weights ι) (k : ℕ) (S : Finset ι) (p : Path ι k) :
    0 ≤ numerator w k S p := by
  induction k generalizing S with
  | zero => simp [numerator]
  | succ k ih =>
    rw [numerator]
    exact mul_nonneg (by split_ifs; norm_num; exact (w.2 p.1).1) (ih _ p.2)

omit [Fintype ι] [Nonempty ι] in
theorem valid_iff (k : ℕ) (S : Finset ι) (p : Path ι k) :
    valid k S p ↔ Function.Injective (tuple k p) ∧ ∀ j,tuple k p j ∉ S := by
  induction k generalizing S with
  | zero => simp [valid,tuple,Function.Injective]
  | succ k ih =>
    rw [valid,ih]
    simp only [tuple,Fin.cons_injective_iff,Fin.forall_iff_succ,
      Fin.cons_zero,Fin.cons_succ,Finset.mem_insert,not_or,Set.mem_range,not_exists]
    constructor
    · rintro ⟨h0,hinj,ht⟩
      refine ⟨⟨?_,hinj⟩,h0,?_⟩
      · intro j he
        exact (ht j).1 he
      · intro j
        exact (ht j).2
    · rintro ⟨⟨h0,hinj⟩,hS,ht⟩
      exact ⟨hS,hinj,fun j => ⟨h0 j,ht j⟩⟩

omit [Fintype ι] [Nonempty ι] in
theorem numerator_eq (w : Weights ι) (k : ℕ) (S : Finset ι) (p : Path ι k) :
    numerator w k S p=if valid k S p then ∏ j,w.1 (tuple k p j) else 0 := by
  classical
  induction k generalizing S with
  | zero => simp [numerator,valid]
  | succ k ih =>
    rw [numerator,ih]
    simp only [valid,tuple,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    split_ifs <;> simp_all

omit [Fintype ι] [Nonempty ι] in

theorem numerator_empty_eq (w : Weights ι) (k : ℕ) (p : Path ι k) :
    numerator w k ∅ p=
      if Function.Injective (tuple k p) then ∏ j,w.1 (tuple k p j) else 0 := by
  rw [numerator_eq,valid_iff]
  simp

theorem actual_mass_bracket (w : Weights ι) (K k : ℕ) (S : Finset ι)
    (hbudget : S.card+k ≤ K) (hW : (K:ℝ) < totalWeight w) (p : Path ι k) :
    numerator w k S p/(totalWeight w)^k ≤ (pathLaw w k S).mass p ∧
      (pathLaw w k S).mass p ≤ numerator w k S p/(totalWeight w-(K:ℝ))^k := by
  have hW0 : 0 < totalWeight w := (Nat.cast_nonneg K).trans_lt hW
  have hWK : 0 < totalWeight w-(K:ℝ) := sub_pos.mpr hW
  induction k generalizing S with
  | zero =>
    cases p
    simp [numerator,pathLaw,FiniteLaw.dirac]
  | succ k ih =>
    have hcard : (S.card:ℝ) ≤ (K:ℝ) := by exact_mod_cast (show S.card ≤ K by omega)
    have hrem : totalWeight w-(K:ℝ) ≤ remainingWeight w S := by
      have hh := denominator_lower w S
      linarith
    have hrem0 : 0 < remainingWeight w S := hWK.trans_le hrem
    have hremW : remainingWeight w S ≤ totalWeight w := by
      rw [remaining_eq]
      linarith [removed_nonneg w S]
    have hb' : (insert p.1 S).card+k ≤ K := by
      have hh := Finset.card_insert_le p.1 S
      omega
    have ht := ih (insert p.1 S) hb' p.2
    rw [path_mass_succ,oneDraw_mass w S hrem0,numerator]
    let a := if p.1 ∈ S then (0:ℝ) else w.1 p.1
    have ha : 0 ≤ a := by dsimp [a]; split_ifs; norm_num; exact (w.2 p.1).1
    have hl : a/totalWeight w ≤ a/remainingWeight w S :=
      div_le_div_of_nonneg_left ha hrem0 hremW
    have hu : a/remainingWeight w S ≤ a/(totalWeight w-(K:ℝ)) :=
      div_le_div_of_nonneg_left ha hWK hrem
    have htn : 0 ≤ numerator w k (insert p.1 S) p.2/(totalWeight w)^k :=
      div_nonneg (numerator_nonneg _ _ _ _) (pow_pos hW0 k).le
    have htail := mass_nonneg (pathLaw w k (insert p.1 S)) p.2
    constructor
    · have hh := mul_le_mul hl ht.1 htn (div_nonneg ha hrem0.le)
      convert! hh using 1
      dsimp [a]
      rw [pow_succ]
      field_simp [hW0.ne',hrem0.ne']
    · have hh := mul_le_mul hu ht.2 htail (div_nonneg ha hWK.le)
      convert! hh using 1
      dsimp [a]
      rw [pow_succ]
      field_simp [hWK.ne',hrem0.ne']

def numeratorSum (w : Weights ι) (k : ℕ) (S : Finset ι) (F : Path ι k → ℝ) : ℝ :=
  ∑ p,numerator w k S p*F p

theorem actual_expectation_bracket (w : Weights ι) (K k : ℕ) (S : Finset ι)
    (hbudget : S.card+k ≤ K) (hW : (K:ℝ) < totalWeight w)
    (F : Path ι k → ℝ) (hF : ∀ p,0 ≤ F p) :
    numeratorSum w k S F/(totalWeight w)^k ≤ (pathLaw w k S).expect F ∧
      (pathLaw w k S).expect F ≤ numeratorSum w k S F/(totalWeight w-(K:ℝ))^k := by
  rw [expect_def,numeratorSum]
  constructor
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun p _ => by
      have hh := mul_le_mul_of_nonneg_right (actual_mass_bracket w K k S hbudget hW p).1 (hF p)
      convert! hh using 1
      ring
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun p _ => by
      have hh := mul_le_mul_of_nonneg_right (actual_mass_bracket w K k S hbudget hW p).2 (hF p)
      convert! hh using 1
      ring

omit [Nonempty ι] in

theorem numeratorSum_eq_embeddings (w : Weights ι) (k : ℕ)
    (F : (Fin k → ι) → ℝ) :
    numeratorSum w k ∅ (fun p => F (tuple k p))=
      ∑ f : Fin k ↪ ι,(∏ j,w.1 (f j))*F f := by
  classical
  rw [numeratorSum]
  simp_rw [numerator_empty_eq]
  have he := (tupleEquiv (ι := ι) k).sum_comp
    (fun v : Fin k → ι => (if Function.Injective v then ∏ j,w.1 (v j) else 0)*F v)
  change (∑ p,(if Function.Injective (tupleEquiv k p) then
    ∏ j,w.1 (tupleEquiv k p j) else 0)*F (tupleEquiv k p))=_
  rw [he]
  let hequiv : (Fin k ↪ ι) ≃ {v : Fin k → ι // Function.Injective v} :=
    { toFun := fun f => ⟨f,f.injective⟩
      invFun := fun f => ⟨f.val,f.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsum : (∑ f : Fin k ↪ ι,(∏ j,w.1 (f j))*F f)=
      ∑ v : {v : Fin k → ι // Function.Injective v},(∏ j,w.1 (v.val j))*F v.val := by
    simpa [hequiv] using
      hequiv.sum_comp (fun v => (∏ j,w.1 (v.val j))*F v.val)
  rw [hsum]
  have hsub := Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
    (p := Function.Injective) (fun v : Fin k → ι => (∏ j,w.1 (v j))*F v)
  rw [show (∑ v : Fin k → ι,(if Function.Injective v then ∏ j,w.1 (v j) else 0)*F v)=
      ∑ v : Fin k → ι,if Function.Injective v then (∏ j,w.1 (v j))*F v else 0 by
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp]
  rw [← Finset.sum_filter]
  simpa using hsub.symm

end FCAppendix.Affine.Uniform06.PathNumerator
