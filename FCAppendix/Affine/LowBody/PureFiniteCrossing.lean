import FCAppendix.Affine.LowBody.PureZeroCompletion
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set
open scoped BigOperators

theorem finite_mixed_maxima {A : Type*} [Fintype A]
    (f : ℝ→A→ℝ) (hf : ∀a,Continuous (fun x=>f x a)) (tag : A→Prop)
    (x y : ℝ) (hxy : x≤y) (a₀ a₁ : A) (ha₀ : ¬tag a₀) (ha₁ : tag a₁)
    (hm₀ : ∀a,f x a≤f x a₀) (hm₁ : ∀a,f y a≤f y a₁) :
    ∃t∈Icc x y,∃p q : A,¬tag p ∧ tag q ∧
      (∀a,f t a≤f t p) ∧ (∀a,f t a≤f t q) := by
  classical
  let s₀:=Finset.univ.filter (fun a=>¬tag a)
  let s₁:=Finset.univ.filter tag
  have hs₀ : s₀.Nonempty:=⟨a₀,by simp [s₀,ha₀]⟩
  have hs₁ : s₁.Nonempty:=⟨a₁,by simp [s₁,ha₁]⟩
  let v₀ : ℝ→ℝ:=fun t=>s₀.sup' hs₀ (f t)
  let v₁ : ℝ→ℝ:=fun t=>s₁.sup' hs₁ (f t)
  have hc₀ : Continuous v₀:=Continuous.finset_sup'_apply hs₀ (fun a _=>hf a)
  have hc₁ : Continuous v₁:=Continuous.finset_sup'_apply hs₁ (fun a _=>hf a)
  have hx : v₁ x-v₀ x≤0 := by
    have hleft : v₁ x≤f x a₀:=Finset.sup'_le hs₁ _ (fun a _=>hm₀ a)
    have hright : f x a₀≤v₀ x:=Finset.le_sup' (f x) (by simp [s₀,ha₀])
    linarith
  have hy : 0≤v₁ y-v₀ y := by
    have hleft : v₀ y≤f y a₁:=Finset.sup'_le hs₀ _ (fun a _=>hm₁ a)
    have hright : f y a₁≤v₁ y:=Finset.le_sup' (f y) (by simp [s₁,ha₁])
    linarith
  obtain ⟨t,ht,heq⟩:=intermediate_value_Icc hxy (hc₁.sub hc₀).continuousOn ⟨hx,hy⟩
  have he : v₁ t=v₀ t:=sub_eq_zero.mp heq
  obtain ⟨p,hp,hpv⟩:=Finset.exists_mem_eq_sup' hs₀ (f t)
  obtain ⟨q,hq,hqv⟩:=Finset.exists_mem_eq_sup' hs₁ (f t)
  have hptag : ¬tag p:=(Finset.mem_filter.mp hp).2
  have hqtag : tag q:=(Finset.mem_filter.mp hq).2
  have hbound (a : A) : f t a≤v₀ t := by
    by_cases ha : tag a
    · rw [←he]
      exact Finset.le_sup' (f t) (by simp [s₁,ha])
    · exact Finset.le_sup' (f t) (by simp [s₀,ha])
  refine ⟨t,ht,p,q,hptag,hqtag,?_,?_⟩
  · intro a
    exact (hbound a).trans_eq hpv
  · intro a
    exact (hbound a).trans_eq (he.symm.trans hqv)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] in
lemma focalCopy_eq_two_iff (P : Finset ι × Finset ι) (i : ι) :
    focalCopy P i=2 ↔ i∈P.1∩P.2 := by
  unfold focalCopy
  split_ifs <;> simp_all [Fin.ext_iff]

namespace PureTemplate

theorem duplicate_acquisition_interval {L : ℕ} (T : PureTemplate (Fin L))
    {κ : ℝ} (hκ : 0<κ) (b : Fin L→ℝ) (hb : ∀j,0≤b j)
    (hz : ∀j,j∉T.support → b j=0) (i : Fin L) (hi : i∈T.support) (hbi : 0<b i)
    (y : ℝ) (hy : b i<y)
    (hnot : focalCopy (T.selection κ b) i≠2)
    (hdup : focalCopy (T.selection κ (Function.update b i y)) i=2) :
    0<T.residual₀ ∧ 0<T.residual₁ ∧
      ∃j : Fin L,j∈T.support ∧ j≠i ∧
        (b j∈Icc (b i) y ∨ b j∈Icc (κ*b i) (κ*y)) := by
  let f : ℝ→T.Candidate→ℝ:=fun t P=>
    CompleteInformation.potential κ (Function.update b i t) P.val.1 P.val.2
  have hf (P : T.Candidate) : Continuous (fun t=>f t P):=
    (continuous_potential κ P.val).comp (continuous_const.update i continuous_id)
  let P₀ : T.Candidate:=⟨T.selection κ b,T.selection_feasible κ b⟩
  let P₁ : T.Candidate:=⟨T.selection κ (Function.update b i y),
    T.selection_feasible κ (Function.update b i y)⟩
  have hn : ¬(i∈P₀.val.1∩P₀.val.2):=fun hh=>hnot ((focalCopy_eq_two_iff _ _).mpr hh)
  have hd : i∈P₁.val.1∩P₁.val.2:=(focalCopy_eq_two_iff _ _).mp hdup
  have hm₀ (P : T.Candidate) : f (b i) P≤f (b i) P₀ := by
    simpa only [f,P₀,Function.update_eq_self] using T.selection_max κ b P.val P.property
  have hm₁ (P : T.Candidate) : f y P≤f y P₁:=T.selection_max κ _ P.val P.property
  obtain ⟨t,ht,P,Q,hP,hQ,hmP,hmQ⟩:=finite_mixed_maxima f hf
    (fun A=>i∈A.val.1∩A.val.2) (b i) y hy.le P₀ P₁ hn hd hm₀ hm₁
  have hpos : 0<t:=hbi.trans_le ht.1
  have hres₀ : 0<T.residual₀ :=
    (Finset.card_pos.mpr ⟨i,(Finset.mem_inter.mp hQ).1⟩).trans_le Q.property.1
  have hres₁ : 0<T.residual₁ :=
    (Finset.card_pos.mpr ⟨i,(Finset.mem_inter.mp hQ).2⟩).trans_le Q.property.2.2.1
  refine ⟨hres₀,hres₁,?_⟩
  by_cases he : ∃j : Fin L,j∈T.support ∧ j≠i ∧ b j=t
  · obtain ⟨j,hj,hji,hjt⟩:=he
    exact ⟨j,hj,hji,Or.inl (hjt.symm ▸ ht)⟩
  · have hbt : ∀j,0≤Function.update b i t j := by
      intro j
      by_cases hj : j=i
      · subst j;simpa only [Function.update_self] using hpos.le
      · simpa only [Function.update_of_ne hj] using hb j
    have hzt (j : Fin L) (hj : j∉T.support) : Function.update b i t j=0 := by
      have hji : j≠i:=fun hh=>hj (hh.symm ▸ hi)
      rw [Function.update_of_ne hji,hz j hj]
    have huni (j : Fin L) (hji : j≠i) : Function.update b i t j≠Function.update b i t i := by
      rw [Function.update_self,Function.update_of_ne hji]
      by_cases hj : j∈T.support
      · exact fun hjt=>he ⟨j,hj,hji,hjt⟩
      · rw [hz j hj]
        exact ne_of_lt hpos
    obtain ⟨j,hj,hji,hjt⟩:=T.duplicate_change_nonnegative_scaled_tie hκ
      (Function.update b i t) hbt hzt i hi (by simpa only [Function.update_self] using hpos)
      huni P.val Q.val P.property Q.property
      (fun A hA=>hmP (⟨A,hA⟩ : T.Candidate))
      (fun A hA=>hmQ (⟨A,hA⟩ : T.Candidate)) hP hQ
    rw [Function.update_of_ne hji,Function.update_self] at hjt
    refine ⟨j,hj,hji,Or.inr ?_⟩
    rw [hjt]
    exact ⟨mul_le_mul_of_nonneg_left ht.1 hκ.le,mul_le_mul_of_nonneg_left ht.2 hκ.le⟩

end PureTemplate
end FCAppendix.Affine.LowBody
