import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def splitMap (P : E →L[ℝ] E) (a e : ℝ) : E →L[ℝ] E :=
  a • (ContinuousLinearMap.id ℝ E-P)+e • P

theorem splitMap_apply (P : E →L[ℝ] E) (a e : ℝ) (x : E) :
    splitMap P a e x=a • (x-P x)+e • P x := rfl

theorem projection_splitMap (P : E →L[ℝ] E) (hP : ∀ x, P (P x)=P x) (a e : ℝ) (x : E) :
    P (splitMap P a e x)=e • P x := by
  rw [splitMap_apply,map_add,map_smul,map_sub,map_smul,hP,sub_self,smul_zero,zero_add]

theorem complement_splitMap (P : E →L[ℝ] E) (hP : ∀ x, P (P x)=P x) (a e : ℝ) (x : E) :
    splitMap P a e x-P (splitMap P a e x)=a • (x-P x) := by
  rw [projection_splitMap P hP,splitMap_apply,add_sub_cancel_right]

theorem splitMap_inverse_apply (P : E →L[ℝ] E) (hP : ∀ x, P (P x)=P x)
    {a e : ℝ} (ha : a≠0) (he : e≠0) (x : E) :
    splitMap P a⁻¹ e⁻¹ (splitMap P a e x)=x := by
  rw [splitMap_apply,complement_splitMap P hP,projection_splitMap P hP,
    smul_smul,smul_smul,inv_mul_cancel₀ ha,inv_mul_cancel₀ he,one_smul,one_smul,sub_add_cancel]

theorem splitMap_isInvertible (P : E →L[ℝ] E) (hP : ∀ x, P (P x)=P x)
    {a e : ℝ} (ha : a≠0) (he : e≠0) : (splitMap P a e).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g:=splitMap P a⁻¹ e⁻¹)
  · ext x
    simpa only [inv_inv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using splitMap_inverse_apply P hP (inv_ne_zero ha) (inv_ne_zero he) x
  · ext x
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using splitMap_inverse_apply P hP ha he x

def meanProjection (ι : Type*) [Fintype ι] : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun _ => (1/(Fintype.card ι:ℝ)) •
    ∑ i : ι, ContinuousLinearMap.proj i

theorem meanProjection_apply {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    meanProjection ι x i=(∑ j, x j)/(Fintype.card ι:ℝ) := by
  simp only [meanProjection,ContinuousLinearMap.pi_apply,smul_apply,
    sum_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,one_div_mul_eq_div]

theorem meanProjection_idempotent {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    meanProjection ι (meanProjection ι x)=meanProjection ι x := by
  ext i
  simp only [meanProjection_apply,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hN : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end FCAppendix.Existence.NarrowPayOnce
