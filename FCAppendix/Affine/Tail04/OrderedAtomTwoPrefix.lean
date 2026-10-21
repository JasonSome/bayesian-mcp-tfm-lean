import FCAppendix.Affine.Tail04.OrderedAtomCountExceptions
import FCAppendix.Affine.Hybrid.NativeFocalReindex
import FCAppendix.Affine.Tail04.TwoFocalCompression

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomTwoPrefix
open MeasureTheory ProbabilityTheory Set Classical
open FiniteTailNoisyGame OrderedAtomActiveCompression OriginalActiveCrossingCarrier
open OrderedAtomCountExceptions OriginalFlagCompression
open scoped BigOperators

section Indices
variable {N : ℕ}

def liftPermutation (e : Equiv.Perm (Fin (N+1))) : Equiv.Perm (Fin (N+2)) where
  toFun := Fin.cases 0 (fun k => (e k).succ)
  invFun := Fin.cases 0 (fun k => (e.symm k).succ)
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · simp only [Fin.cases_succ,Equiv.symm_apply_apply]
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · simp only [Fin.cases_succ,Equiv.apply_symm_apply]

def prefixIndex (j : Fin (N+1)) : Equiv.Perm (Fin (N+2)) :=
  liftPermutation (Hybrid.NativeContinuation.focalIndex j)

@[simp] theorem prefixIndex_zero (j : Fin (N+1)) : prefixIndex j 0=0 := rfl

@[simp] theorem prefixIndex_one (j : Fin (N+1)) :
    prefixIndex j (0 : Fin (N+1)).succ=j.succ := by
  simp only [prefixIndex,liftPermutation,Equiv.coe_fn_mk,Fin.cases_succ,
    Hybrid.NativeContinuation.focalIndex_zero]

@[simp] theorem prefixIndex_suffix (j : Fin (N+1)) (k : Fin N) :
    prefixIndex j k.succ.succ=(j.succAbove k).succ := by
  simp only [prefixIndex,liftPermutation,Equiv.coe_fn_mk,Fin.cases_succ,
    Hybrid.NativeContinuation.focalIndex_succ]

theorem restore_prefix {X : Type*} [MeasurableSpace X]
    (j : Fin (N+1)) (x y : X) (row : Fin N→ X) :
    (Fin.cons x (restore j y row)) ∘ prefixIndex j=Fin.cons x (Fin.cons y row) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Function.comp_apply,prefixIndex_one,Fin.cons_succ,restore_self,Fin.cons_zero]
    · simp only [Function.comp_apply,prefixIndex_suffix,Fin.cons_succ,restore_succAbove]

def predicateEquiv {α β : Type*} (e : α≃β) (p : α→ Prop) (q : β→ Prop)
    (h : ∀ a,p a↔q (e a)) : {a // p a}≃{b // q b} where
  toFun a := ⟨e a,(h a).mp a.property⟩
  invFun b := ⟨e.symm b,(h (e.symm b)).mpr (by simpa only [Equiv.apply_symm_apply] using b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)

def consEnumeration {M A : ℕ} (active : Fin M→ Bool)
    (e : Fin A≃Active active) : Fin (A+1)≃Active (Fin.cons true active) where
  toFun := Fin.cases ⟨0,rfl⟩ (fun k => ⟨(e k).val.succ,(e k).property⟩)
  invFun i := Fin.cases (fun _ => 0)
    (fun k hk => (e.symm ⟨k,hk⟩).succ) i.val i.property
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · change (e.symm (e k)).succ=k.succ
      rw [e.symm_apply_apply]
  right_inv := by
    rintro ⟨i,hi⟩
    revert hi
    refine Fin.cases ?_ (fun k => ?_) i
    · intro hi
      rfl
    · intro hi
      apply Subtype.ext
      simp only [Fin.cases_succ,Equiv.apply_symm_apply]

@[simp] lemma consEnumeration_zero {M A : ℕ} (active : Fin M→ Bool)
    (e : Fin A≃Active active) : (consEnumeration active e 0).val=0 := rfl

@[simp] lemma consEnumeration_succ {M A : ℕ} (active : Fin M→ Bool)
    (e : Fin A≃Active active) (k : Fin A) :
    (consEnumeration active e k.succ).val=(e k).val.succ := rfl

end Indices

section Rows
variable {X : Type*} [MeasurableSpace X] {N : ℕ}
  (D : Data) (tag : X→ Fin 4) (decode : X→ Icc (1:ℝ) D.B)
  (j : Fin (N+1)) (y : X) (hy : tag y=1) (row : Fin N→ X)

def remainingActive : Fin N→ Bool := fun k => decide (tag (row k)=1)
def prefixActive : Fin (N+2)→ Bool := Fin.cons true (Fin.cons true (remainingActive tag row))

local notation "kind" => tags tag (restore j y row)
local notation "ar" => fun k : Fin (N+1) => decide (kind k=1)

def rivalEnumeration : Fin (D.count kind 1)≃Active ar :=
  (enumeration D kind 1).trans
    (predicateEquiv (Equiv.refl _) (fun k => kind k=1)
      (fun k => ar k=true) (fun k => by simp))

include hy in
lemma prefix_active_eq (i : Fin (N+2)) :
    (Fin.cons true (ar) : Fin (N+2)→Bool) (prefixIndex j i)=prefixActive tag row i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp only [prefixIndex_one,Fin.cons_succ,tags,Function.comp_apply,
        restore_self,hy,decide_true,prefixActive,Fin.cons_zero]
    · simp only [prefixIndex_suffix,Fin.cons_succ,tags,Function.comp_apply,
        restore_succAbove,prefixActive,remainingActive]

def activeEnumeration : Fin (D.count kind 1+1)≃Active (prefixActive tag row) :=
  (consEnumeration (ar) (rivalEnumeration D tag j y row)).trans
    (predicateEquiv (prefixIndex j).symm
      (fun i => (Fin.cons true (ar) : Fin (N+2)→Bool) i=true)
      (fun i => prefixActive tag row i=true) (fun i => by
        have h := prefix_active_eq tag j y hy row ((prefixIndex j).symm i)
        rw [Equiv.apply_symm_apply] at h
        rw [←h]))

lemma activeEnumeration_index (k : Fin (D.count kind 1+1)) :
    prefixIndex j (activeEnumeration D tag j y hy row k).val=
      (consEnumeration (ar) (rivalEnumeration D tag j y row) k).val :=
  (prefixIndex j).apply_symm_apply _

theorem compressed_focal_row (b0 : Icc (1:ℝ) D.B) :
    compressedBids (prefixActive tag row) (activeEnumeration D tag j y hy row)
      (Fin.cons (b0:ℝ) (Fin.cons (decode y:ℝ) (fun k => (decode (row k):ℝ))))=
        fun k => (focalRow D kind decode b0 (restore j y row) k:ℝ) := by
  let numeric : Fin (N+2)→ℝ := Fin.cons (b0:ℝ) (fun k => (decode (restore j y row k):ℝ))
  have hrow : numeric ∘ prefixIndex j=
      Fin.cons (b0:ℝ) (Fin.cons (decode y:ℝ) (fun k => (decode (row k):ℝ))) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Function.comp_apply,prefixIndex_one,numeric,Fin.cons_succ,
          restore_self,Fin.cons_zero]
      · simp only [Function.comp_apply,prefixIndex_suffix,numeric,Fin.cons_succ,
          restore_succAbove]
  rw [←hrow]
  funext k
  rw [compressedBids,Function.comp_apply,activeEnumeration_index]
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · rfl

include j y hy in
theorem private_count_unchanged (k : Fin 4) (hk : k≠1) :
    D.count kind k=D.count (tags tag row) k :=
  count_restore_active D tag j y hy row k hk

end Rows
end FCAppendix.Affine.Tail04.OrderedAtomTwoPrefix
