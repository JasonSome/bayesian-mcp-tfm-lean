import FCAppendix.Affine.LowBody.PureCopyMonotonicity
import FCAppendix.Affine.LowBody.ZeroClusterLoss

noncomputable section

namespace FCAppendix.Affine.Uniform06.PrefixMonotonicity

open Set MeasureTheory
open scoped BigOperators

def successOfCopies (k : Fin 3) : ℝ := if k=0 then 0 else 1
def duplicateOfCopies (k : Fin 3) : ℝ := if k=2 then 1 else 0

theorem successOfCopies_mono : Monotone successOfCopies := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [successOfCopies,Fin.ext_iff]

theorem duplicateOfCopies_mono : Monotone duplicateOfCopies := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [duplicateOfCopies,Fin.ext_iff]

section Pure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pureCopies (T : LowBody.PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (i : ι) (x : ℝ) : Fin 3 :=
  LowBody.focalCopy (T.selection κ (Function.update b i x)) i

theorem pureCopies_monotone
    (T : LowBody.PureTemplate ι) {κ : ℝ} (hκ : 0 < κ)
    (b : ι → ℝ) (i : ι) : Monotone (pureCopies T κ b i) := by
  intro x y hxy
  by_cases h : x=y
  · simp [h]
  have hlt : x < y := lt_of_le_of_ne hxy h
  have hm := T.focalCopy_selection_mono hκ (Function.update b i x) i y
    (by simpa only [Function.update_self] using hlt)
  simpa only [pureCopies,Function.update_idem] using hm

theorem actual_pure_success_duplicate_monotone
    (T : LowBody.PureTemplate ι) {κ : ℝ} (hκ : 0 < κ)
    (b : ι → ℝ) (i : ι) :
    Monotone (fun x => successOfCopies (pureCopies T κ b i x)) ∧
    Monotone (fun x => duplicateOfCopies (pureCopies T κ b i x)) :=
  ⟨successOfCopies_mono.comp (pureCopies_monotone T hκ b i),
    duplicateOfCopies_mono.comp (pureCopies_monotone T hκ b i)⟩

end Pure

section Clipped

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def clippedMarginal (ξ : ℝ) (c : ℕ) (b : ι → ℝ) (i : ι) (x : ℝ) : ℝ :=
  EqualCapacity.positiveMarginal ξ c (Function.update b i x) i

def clippedSuccess (ξ : ℝ) (c : ℕ) (b : ι → ℝ) (i : ι) (x : ℝ) : ℝ :=
  2*clippedMarginal ξ c b i x-(clippedMarginal ξ c b i x)^2

def clippedDuplicate (ξ : ℝ) (c : ℕ) (b : ι → ℝ) (i : ι) (x : ℝ) : ℝ :=
  (clippedMarginal ξ c b i x)^2

theorem actual_clipped_success_duplicate_monotone
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ι → ℝ) (i : ι)
    (hb : ∀ j, j ≠ i → 0 ≤ b j) :
    MonotoneOn (clippedSuccess ξ c b i) (Ici 0) ∧
    MonotoneOn (clippedDuplicate ξ c b i) (Ici 0) := by
  have hm {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      clippedMarginal ξ c b i x ≤ clippedMarginal ξ c b i y :=
    LowBody.positiveMarginal_update_mono hξ hξ1 c b i hb hx hxy
  have hp (x : ℝ) : clippedMarginal ξ c b i x ∈ Icc (0 : ℝ) 1 := by
    have h := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i x)
    exact ⟨h.1 i,h.2.1 i⟩
  constructor
  · intro x hx y hy hxy
    have h := hm hx hxy
    have hprod := mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ 2-clippedMarginal ξ c b i x-clippedMarginal ξ c b i y by
        linarith [(hp x).2,(hp y).2])
    unfold clippedSuccess
    nlinarith
  · intro x hx y hy hxy
    have h := hm hx hxy
    have hprod := mul_nonneg (sub_nonneg.mpr h)
      (add_nonneg (hp x).1 (hp y).1)
    unfold clippedDuplicate
    nlinarith

end Clipped

theorem guarded_mixture_eq_add
    {P C α : ℝ → ℝ} {I : Set ℝ}
    (hα : ∀ b ∈ I, 0 ≤ α b)
    (hreject : ∀ b ∈ I, 0 < α b → P b = 0) :
    ∀ b ∈ I, (1-α b)*P b+α b*C b = P b+α b*C b := by
  intro b hb
  by_cases hpos : 0 < α b
  · rw [hreject b hb hpos]
    ring
  · have hz : α b = 0 := le_antisymm (le_of_not_gt hpos) (hα b hb)
    rw [hz]
    ring

theorem guarded_mixture_monotone
    {P C α : ℝ → ℝ} {I : Set ℝ}
    (hP : MonotoneOn P I) (hC : MonotoneOn C I) (hαm : MonotoneOn α I)
    (hC0 : ∀ b ∈ I, 0 ≤ C b) (hα0 : ∀ b ∈ I, 0 ≤ α b)
    (hreject : ∀ b ∈ I, 0 < α b → P b = 0) :
    MonotoneOn (fun b => (1-α b)*P b+α b*C b) I := by
  intro a ha b hb hab
  dsimp only
  rw [guarded_mixture_eq_add hα0 hreject a ha,
    guarded_mixture_eq_add hα0 hreject b hb]
  exact add_le_add (hP ha hb hab)
    (mul_le_mul (hαm ha hb hab) (hC ha hb hab) (hC0 a ha) (hα0 b hb))

end FCAppendix.Affine.Uniform06.PrefixMonotonicity
