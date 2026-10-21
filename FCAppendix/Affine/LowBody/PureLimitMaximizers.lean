import FCAppendix.Affine.LowBody.PureCopyMonotonicity

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology
open scoped BigOperators

theorem selected_max_at_limit_eventually {X A : Type*} [TopologicalSpace X]
    [Fintype A] [Nonempty A] (f : X → A → ℝ) (hf : ∀a,Continuous (fun x=>f x a))
    (x0 : X) :
    ∀ᶠx in 𝓝 x0,∀a,f x0 a ≤ f x0 (FiniteSelector.select (f x)) := by
  classical
  let a0:=FiniteSelector.select (f x0)
  let label : A → Prop:=fun a=>f x0 a0 ≤ f x0 a
  have hg (a b : A) (h : f x0 a=f x0 b) : label a=label b :=
    congrArg (fun y : ℝ=>f x0 a0 ≤ y) h
  have he:=selected_label_eventually_eq f hf label x0 hg
  filter_upwards [he] with x hx a
  have hh : label (FiniteSelector.select (f x)) := hx.mpr le_rfl
  exact (FiniteSelector.select_max (f x0) a).trans hh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace PureTemplate

theorem selection_max_at_limit_eventually (T : PureTemplate ι) (κ : ℝ) (b0 : ι → ℝ) :
    ∀ᶠb in 𝓝 b0,∀P : Finset ι × Finset ι,T.Feasible P  →
      CompleteInformation.potential κ b0 P.1 P.2 ≤
        CompleteInformation.potential κ b0 (T.selection κ b).1 (T.selection κ b).2 := by
  have he:=selected_max_at_limit_eventually
    (fun (b : ι → ℝ) (P : T.Candidate)=>CompleteInformation.potential κ b P.val.1 P.val.2)
    (fun P=>continuous_potential κ P.val) b0
  filter_upwards [he] with b hb P hP
  exact hb (⟨P,hP⟩ : T.Candidate)

omit [Fintype ι] in
private lemma nash_card (κ : ℝ) (hκ : 0 < κ) (b : ι → ℝ)
    (H : Finset ι) (r : ℕ) (S Q : Finset ι) (hcard : S.card ≤ r) (hsub : S⊆H)
    (hb : ∀i∈H,0 < b i)
    (hm : ∀A : Finset ι,A.card ≤ r  →  A⊆H  →
      CompleteInformation.revenue κ b A Q ≤ CompleteInformation.revenue κ b S Q) :
    S.card=min r H.card := by
  have hbound : S.card ≤ min r H.card := le_min hcard (Finset.card_le_card hsub)
  apply le_antisymm hbound
  by_contra hn
  have hlt : S.card < min r H.card := lt_of_not_ge hn
  obtain ⟨i,hiH,hiS⟩:=Finset.exists_mem_notMem_of_card_lt_card
    (hlt.trans_le (min_le_right _ _))
  have hA : (insert i S).card ≤ r := by
    rw [Finset.card_insert_of_notMem hiS]
    have hh:=hlt.trans_le (min_le_left _ _)
    omega
  have hh:=hm (insert i S) hA (Finset.insert_subset hiH hsub)
  unfold CompleteInformation.revenue at hh
  rw [Finset.sum_insert hiS] at hh
  have hp : 0 < (if i∈Q then κ*b i else b i) := by
    split
    · exact mul_pos hκ (hb i hiH)
    · exact hb i hiH
  linarith

theorem maximizer_card (T : PureTemplate ι) {κ : ℝ} (hκ : 0 < κ)
    (b : ι → ℝ) (hb : ∀i∈T.support,0 < b i) (P : Finset ι × Finset ι)
    (hP : T.Feasible P)
    (hmax : ∀Q,T.Feasible Q →
      CompleteInformation.potential κ b Q.1 Q.2 ≤ CompleteInformation.potential κ b P.1 P.2) :
    P.1.card=min T.residual₀ T.support.card ∧ P.2.card=min T.residual₁ T.support.card := by
  have hm0 (S : Finset ι) (hc : S.card ≤ T.residual₀) (hs : S⊆T.support) :
      CompleteInformation.revenue κ b S P.2 ≤ CompleteInformation.revenue κ b P.1 P.2 := by
    have hh:=hmax (S,P.2) ⟨hc,hs,hP.2.2.1,hP.2.2.2⟩
    rw [CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh
  have hm1 (S : Finset ι) (hc : S.card ≤ T.residual₁) (hs : S⊆T.support) :
      CompleteInformation.revenue κ b S P.1 ≤ CompleteInformation.revenue κ b P.2 P.1 := by
    have hh:=hmax (P.1,S) ⟨hP.1,hP.2.1,hc,hs⟩
    rw [CompleteInformation.potential_comm κ b P.1 S,
      CompleteInformation.potential_comm κ b P.1 P.2,
      CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh
  exact ⟨nash_card κ hκ b T.support T.residual₀ P.1 P.2 hP.1 hP.2.1 hb hm0,
    nash_card κ hκ b T.support T.residual₁ P.2 P.1 hP.2.2.1 hP.2.2.2 hb hm1⟩

theorem selection_card (T : PureTemplate ι) {κ : ℝ} (hκ : 0 < κ)
    (b : ι → ℝ) (hb : ∀i∈T.support,0 < b i) :
    (T.selection κ b).1.card=min T.residual₀ T.support.card ∧
      (T.selection κ b).2.card=min T.residual₁ T.support.card := by
  have hf:=T.selection_feasible κ b
  have hn:=T.selection_nash κ b
  exact ⟨nash_card κ hκ b T.support T.residual₀ _ _ hf.1 hf.2.1 hb hn.1,
    nash_card κ hκ b T.support T.residual₁ _ _ hf.2.2.1 hf.2.2.2 hb hn.2⟩

end PureTemplate
end FCAppendix.Affine.LowBody
