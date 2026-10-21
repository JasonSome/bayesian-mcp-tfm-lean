import FCAppendix.Affine.LowBody.PureLimitMaximizers

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set
open scoped BigOperators

lemma potential_inter_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ℝ) (b : ι→ℝ) (H S T : Finset ι) (hz : ∀i,i∉H → b i=0) :
    CompleteInformation.potential κ b (S∩H) (T∩H)=CompleteInformation.potential κ b S T := by
  rw [potential_eq_copyCoefficient κ b (S∩H,T∩H),potential_eq_copyCoefficient κ b (S,T)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i∈H
  · simp only [copyCoefficient,Finset.mem_union,Finset.mem_inter,hi,and_true]
  · simp only [hz i hi,mul_zero]

namespace PureTemplate
variable {L : ℕ} (T : PureTemplate (Fin L))

lemma maximizer_global_full (κ : ℝ) (b : Fin L→ℝ)
    (hz : ∀i,i∉T.support → b i=0) (P : Finset (Fin L) × Finset (Fin L))
    (hP : T.Feasible P)
    (hm : ∀Q,T.Feasible Q →
      CompleteInformation.potential κ b Q.1 Q.2≤CompleteInformation.potential κ b P.1 P.2) :
    ∀A B,A.card=P.1.card → B.card=P.2.card →
      CompleteInformation.potential κ b A B≤CompleteInformation.potential κ b P.1 P.2 := by
  intro A B hA hB
  have hf : T.Feasible (A∩T.support,B∩T.support) :=
    ⟨((Finset.card_le_card Finset.inter_subset_left).trans_eq hA).trans hP.1,
      Finset.inter_subset_right,
      ((Finset.card_le_card Finset.inter_subset_left).trans_eq hB).trans hP.2.2.1,
      Finset.inter_subset_right⟩
  simpa only [potential_inter_support κ b T.support A B hz] using hm _ hf

theorem duplicate_change_low_scaled_tie {κ : ℝ} (hκ : 0<κ) (b : Fin L→ℝ)
    (hb : ∀i∈T.support,0<b i) (hz : ∀i,i∉T.support → b i=0)
    (t : Fin L) (ht : t∈T.support) (hunique : ∀i,i≠t → b i≠b t)
    (P Q : Finset (Fin L) × Finset (Fin L)) (hP : T.Feasible P) (hQ : T.Feasible Q)
    (hmP : ∀A,T.Feasible A →
      CompleteInformation.potential κ b A.1 A.2≤CompleteInformation.potential κ b P.1 P.2)
    (hmQ : ∀A,T.Feasible A →
      CompleteInformation.potential κ b A.1 A.2≤CompleteInformation.potential κ b Q.1 Q.2)
    (hnot : t∉P.1∩P.2) (hmem : t∈Q.1∩Q.2) :
    ∃j : Fin L,j∈T.support ∧ j≠t ∧ b j=κ*b t := by
  have hcardP:=T.maximizer_card hκ b hb P hP hmP
  have hcardQ:=T.maximizer_card hκ b hb Q hQ hmQ
  have hsL : T.support.card≤L := by simpa only [Fintype.card_fin] using Finset.card_le_univ T.support
  have hr0 : min T.residual₀ T.support.card≤L := (min_le_right _ _).trans hsL
  have hr1 : min T.residual₁ T.support.card≤L := (min_le_right _ _).trans hsL
  have hb0 (i : Fin L) : 0≤b i := by
    by_cases hi : i∈T.support
    · exact (hb i hi).le
    · rw [hz i hi]
  have hPglobal:=T.maximizer_global_full κ b hz P hP hmP
  have hQglobal:=T.maximizer_global_full κ b hz Q hQ hmQ
  obtain ⟨j,hjt,hbj⟩:=SortedPotential.duplicate_change_scaled_tie_unsorted hr0 hr1 κ hκ b hb0
    t hunique P.1 P.2 Q.1 Q.2 hcardP.1 hcardP.2 hcardQ.1 hcardQ.2
    (fun A B hA hB=>hPglobal A B (hA.trans hcardP.1.symm) (hB.trans hcardP.2.symm))
    (fun A B hA hB=>hQglobal A B (hA.trans hcardQ.1.symm) (hB.trans hcardQ.2.symm)) hnot hmem
  refine ⟨j,?_,hjt,hbj⟩
  by_contra hj
  have hp : 0<κ*b t := mul_pos hκ (hb t ht)
  rw [hz j hj] at hbj
  linarith

end PureTemplate
end FCAppendix.Affine.LowBody
