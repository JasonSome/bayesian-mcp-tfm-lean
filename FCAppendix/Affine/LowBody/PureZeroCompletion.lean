import FCAppendix.Affine.LowBody.PureTemplateCrossing

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma extend_in_support (H S : Finset ι) (r : ℕ) (hS : S⊆H)
    (hSr : S.card≤r) (hr : r≤H.card) :
    ∃A : Finset ι,S⊆A ∧ A⊆H ∧ A.card=r := by
  have hd : r-S.card≤(H\S).card := by
    rw [Finset.card_sdiff_of_subset hS]
    omega
  obtain ⟨D,hD,hcard⟩:=Finset.exists_subset_card_eq hd
  have hdis : Disjoint S D := Finset.disjoint_left.mpr
    (fun i hiS hiD=>(Finset.mem_sdiff.mp (hD hiD)).2 hiS)
  refine ⟨S∪D,Finset.subset_union_left,?_,?_⟩
  · exact Finset.union_subset hS (Finset.Subset.trans hD Finset.sdiff_subset)
  · rw [Finset.card_union_of_disjoint hdis,hcard]
    omega

lemma potential_mono_pair (κ : ℝ) (hκ : 0≤κ) (b : ι→ℝ) (hb : ∀i,0≤b i)
    (S T A B : Finset ι) (hSA : S⊆A) (hTB : T⊆B) :
    CompleteInformation.potential κ b S T≤CompleteInformation.potential κ b A B := by
  calc
    _≤CompleteInformation.potential κ b A T := by
      rw [CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add]
      have hh:=CompleteInformation.revenue_mono_selection κ hκ b hb S A T hSA
      linarith
    _≤_ := by
      rw [CompleteInformation.potential_comm κ b A T,CompleteInformation.potential_comm κ b A B,
        CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add]
      have hh:=CompleteInformation.revenue_mono_selection κ hκ b hb T B A hTB
      linarith

omit [Fintype ι] in
private lemma omitted_positive_full (κ : ℝ) (hκ : 0<κ) (b : ι→ℝ)
    (H S Q : Finset ι) (r : ℕ) (hS : S⊆H) (hcard : S.card≤r)
    (i : ι) (hi : i∈H) (hbi : 0<b i) (hnot : i∉S)
    (hm : ∀A,A.card≤r → A⊆H →
      CompleteInformation.revenue κ b A Q≤CompleteInformation.revenue κ b S Q) : S.card=r := by
  apply le_antisymm hcard
  by_contra hn
  have hc : (insert i S).card≤r := by rw [Finset.card_insert_of_notMem hnot];omega
  have hh:=hm (insert i S) hc (Finset.insert_subset hi hS)
  unfold CompleteInformation.revenue at hh
  rw [Finset.sum_insert hnot] at hh
  have hp : 0<(if i∈Q then κ*b i else b i) := by
    split
    · exact mul_pos hκ hbi
    · exact hbi
  linarith

namespace PureTemplate

theorem exists_full_completion (T : PureTemplate ι) {κ : ℝ} (hκ : 0<κ)
    (b : ι→ℝ) (hb : ∀i,0≤b i) (P : Finset ι × Finset ι) (hP : T.Feasible P)
    (hm : ∀Q,T.Feasible Q →
      CompleteInformation.potential κ b Q.1 Q.2≤CompleteInformation.potential κ b P.1 P.2)
    (i : ι) (hi : i∈T.support) (hbi : 0<b i) :
    ∃Q : Finset ι × Finset ι,T.Feasible Q ∧
      Q.1.card=min T.residual₀ T.support.card ∧ Q.2.card=min T.residual₁ T.support.card ∧
      (i∈Q.1 ↔ i∈P.1) ∧ (i∈Q.2 ↔ i∈P.2) ∧
      ∀A,T.Feasible A →
        CompleteInformation.potential κ b A.1 A.2≤CompleteInformation.potential κ b Q.1 Q.2 := by
  have hN0 (A : Finset ι) (hc : A.card≤T.residual₀) (hs : A⊆T.support) :
      CompleteInformation.revenue κ b A P.2≤CompleteInformation.revenue κ b P.1 P.2 := by
    have hh:=hm (A,P.2) ⟨hc,hs,hP.2.2.1,hP.2.2.2⟩
    rw [CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh
  have hN1 (A : Finset ι) (hc : A.card≤T.residual₁) (hs : A⊆T.support) :
      CompleteInformation.revenue κ b A P.1≤CompleteInformation.revenue κ b P.2 P.1 := by
    have hh:=hm (P.1,A) ⟨hP.1,hP.2.1,hc,hs⟩
    rw [CompleteInformation.potential_comm κ b P.1 A,CompleteInformation.potential_comm κ b P.1 P.2,
      CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh
  obtain ⟨A,hPA,hA,hAc⟩:=extend_in_support T.support P.1
    (min T.residual₀ T.support.card) hP.2.1
    (le_min hP.1 (Finset.card_le_card hP.2.1)) (min_le_right _ _)
  obtain ⟨B,hPB,hB,hBc⟩:=extend_in_support T.support P.2
    (min T.residual₁ T.support.card) hP.2.2.2
    (le_min hP.2.2.1 (Finset.card_le_card hP.2.2.2)) (min_le_right _ _)
  have hf : T.Feasible (A,B):=
    ⟨hAc.le.trans (min_le_left _ _),hA,hBc.le.trans (min_le_left _ _),hB⟩
  have heq : CompleteInformation.potential κ b A B=CompleteInformation.potential κ b P.1 P.2 :=
    le_antisymm (hm (A,B) hf) (potential_mono_pair κ hκ.le b hb P.1 P.2 A B hPA hPB)
  refine ⟨(A,B),hf,hAc,hBc,?_,?_,?_⟩
  · constructor
    · intro hiA
      by_contra hn
      have hc:=omitted_positive_full κ hκ b T.support P.1 P.2 T.residual₀
        hP.2.1 hP.1 i hi hbi hn hN0
      have hEq : P.1=A := Finset.eq_of_subset_of_card_le hPA (by rw [hAc,hc];exact min_le_left _ _)
      exact hn (hEq.symm ▸ hiA)
    · exact fun h=>hPA h
  · constructor
    · intro hiB
      by_contra hn
      have hc:=omitted_positive_full κ hκ b T.support P.2 P.1 T.residual₁
        hP.2.2.2 hP.2.2.1 i hi hbi hn hN1
      have hEq : P.2=B := Finset.eq_of_subset_of_card_le hPB (by rw [hBc,hc];exact min_le_left _ _)
      exact hn (hEq.symm ▸ hiB)
    · exact fun h=>hPB h
  · intro C hC
    rw [heq]
    exact hm C hC

theorem duplicate_change_nonnegative_scaled_tie {L : ℕ} (T : PureTemplate (Fin L))
    {κ : ℝ} (hκ : 0<κ) (b : Fin L→ℝ) (hb : ∀i,0≤b i)
    (hz : ∀i,i∉T.support → b i=0) (t : Fin L) (ht : t∈T.support) (hbt : 0<b t)
    (hunique : ∀i,i≠t → b i≠b t)
    (P Q : Finset (Fin L) × Finset (Fin L)) (hP : T.Feasible P) (hQ : T.Feasible Q)
    (hmP : ∀A,T.Feasible A →
      CompleteInformation.potential κ b A.1 A.2≤CompleteInformation.potential κ b P.1 P.2)
    (hmQ : ∀A,T.Feasible A →
      CompleteInformation.potential κ b A.1 A.2≤CompleteInformation.potential κ b Q.1 Q.2)
    (hnot : t∉P.1∩P.2) (hmem : t∈Q.1∩Q.2) :
    ∃j : Fin L,j∈T.support ∧ j≠t ∧ b j=κ*b t := by
  obtain ⟨P',hP',hP0,hP1,hPm0,hPm1,hmP'⟩:=T.exists_full_completion hκ b hb P hP hmP t ht hbt
  obtain ⟨Q',hQ',hQ0,hQ1,hQm0,hQm1,hmQ'⟩:=T.exists_full_completion hκ b hb Q hQ hmQ t ht hbt
  have hsL : T.support.card≤L := by simpa only [Fintype.card_fin] using Finset.card_le_univ T.support
  have hr0 : min T.residual₀ T.support.card≤L := (min_le_right _ _).trans hsL
  have hr1 : min T.residual₁ T.support.card≤L := (min_le_right _ _).trans hsL
  have hPglobal:=T.maximizer_global_full κ b hz P' hP' hmP'
  have hQglobal:=T.maximizer_global_full κ b hz Q' hQ' hmQ'
  have hn : t∉P'.1∩P'.2 := by simpa only [Finset.mem_inter,hPm0,hPm1] using hnot
  have hy : t∈Q'.1∩Q'.2 := by simpa only [Finset.mem_inter,hQm0,hQm1] using hmem
  obtain ⟨j,hjt,hbj⟩:=SortedPotential.duplicate_change_scaled_tie_unsorted hr0 hr1 κ hκ b hb
    t hunique P'.1 P'.2 Q'.1 Q'.2 hP0 hP1 hQ0 hQ1
    (fun A B hA hB=>hPglobal A B (hA.trans hP0.symm) (hB.trans hP1.symm))
    (fun A B hA hB=>hQglobal A B (hA.trans hQ0.symm) (hB.trans hQ1.symm)) hn hy
  refine ⟨j,?_,hjt,hbj⟩
  by_contra hj
  have hp : 0<κ*b t:=mul_pos hκ hbt
  rw [hz j hj] at hbj
  linarith

end PureTemplate
end FCAppendix.Affine.LowBody
