import FCAppendix.Affine.Tail04.OriginalFiberProduct
import FCAppendix.Affine.Tail04.PartialNativeCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.FiberCategoryEquiv
open Classical
open OriginalFiberProduct PartialNativeCoordinates

variable {I : Type*} (k : I→ Fin 4)

def common : Common k ≃ {i : I // k i=1} where
  toFun i := ⟨i.val.val,i.property⟩
  invFun i := ⟨⟨i.val,by rw [i.property];decide⟩,i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def zero : Zero k ≃ {i : I // k i=2} where
  toFun i := ⟨i.val.val.val,i.property⟩
  invFun i := ⟨⟨⟨i.val,by rw [i.property];decide⟩,by rw [i.property];decide⟩,i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def one : One k ≃ {i : I // k i=3} where
  toFun i := ⟨i.val.val.val,one_tag k i⟩
  invFun i := ⟨⟨⟨i.val,by rw [i.property];decide⟩,by rw [i.property];decide⟩,
    by rw [i.property];decide⟩
  left_inv _ := rfl
  right_inv _ := rfl

def commonLabels {N : ℕ} (i : Fin (N+1)) (kind : Fin N→ Fin 4) :
    Common kind ≃ {l : Fin (N+1) // l∈rivalSet i kind 1} :=
  (common kind).trans (rivalSetEquiv i kind 1)

def zeroLabels {N : ℕ} (i : Fin (N+1)) (kind : Fin N→ Fin 4) :
    Zero kind ≃ {l : Fin (N+1) // l∈rivalSet i kind 2} :=
  (zero kind).trans (rivalSetEquiv i kind 2)

def oneLabels {N : ℕ} (i : Fin (N+1)) (kind : Fin N→ Fin 4) :
    One kind ≃ {l : Fin (N+1) // l∈rivalSet i kind 3} :=
  (one kind).trans (rivalSetEquiv i kind 3)

@[simp] theorem commonLabels_val {N : ℕ} (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (r : Common kind) : (commonLabels i kind r).val=i.succAbove r.val.val := rfl

@[simp] theorem zeroLabels_val {N : ℕ} (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (r : Zero kind) : (zeroLabels i kind r).val=i.succAbove r.val.val.val := rfl

@[simp] theorem oneLabels_val {N : ℕ} (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (r : One kind) : (oneLabels i kind r).val=i.succAbove r.val.val.val := rfl

end FCAppendix.Affine.Tail04.FiberCategoryEquiv
