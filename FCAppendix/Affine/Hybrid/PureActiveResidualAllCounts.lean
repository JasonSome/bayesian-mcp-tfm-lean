import FCAppendix.Affine.Hybrid.PureActiveResidual

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open Game Set Classical Bayes LowBody
open scoped BigOperators
variable {m : ℕ}

def ActivePriority (r : ℕ) (A S : Finset (Fin m)) : Prop:=
  (A.card ≤ r ∧ A⊆S) ∨ (r ≤ A.card ∧ S⊆A)

lemma feasible_erase_priority (L : LocalList m) (r : ℕ) (A S : Finset (Fin m))
    (hS:LocallyFeasible L r S) (hp:ActivePriority r A S) :
    LocallyFeasible (eraseActiveList A L) (r-A.card) (S\A):=by
  rcases hp with ⟨_,hAS⟩|⟨_,hSA⟩
  · exact feasible_erase_active L r A S hS hAS
  · rw [Finset.sdiff_eq_empty_iff_subset.mpr hSA]
    simp [LocallyFeasible]

lemma feasible_restore_priority (L : LocalList m) (r : ℕ) (A S Q : Finset (Fin m))
    (hS:LocallyFeasible L r S) (hp:ActivePriority r A S)
    (hQ:LocallyFeasible (eraseActiveList A L) (r-A.card) Q) :
    LocallyFeasible L r ((S∩A)∪Q):=by
  rcases hp with ⟨hfit,hAS⟩|⟨hover,hSA⟩
  · rw [Finset.inter_eq_right.mpr hAS]
    exact feasible_add_active L r A Q (fun i hi=>hS.2 i (hAS hi)) hfit hQ
  · have hQ0:Q=∅:=Finset.card_eq_zero.mp (by have hh:=hQ.1;omega)
    rw [hQ0,Finset.union_empty,Finset.inter_eq_left.mpr hSA]
    exact hS

lemma potential_partition_active (κ : ℝ) (b : Fin m → ℝ) (A S T : Finset (Fin m)) :
    CompleteInformation.potential κ b S T=
      CompleteInformation.potential κ b (S∩A) (T∩A)+
      CompleteInformation.potential κ (eraseActiveBids A b) (S\A) (T\A):=by
  have hsum (D : Finset (Fin m)) (f : Fin m → ℝ) : (∑i∈D,f i)=∑i,if i∈D then f i else 0:=by simp
  unfold CompleteInformation.potential
  rw [hsum (S∪T),hsum (S∩T),hsum ((S∩A)∪(T∩A)),hsum ((S∩A)∩(T∩A)),
    hsum ((S\A)∪(T\A)),hsum ((S\A)∩(T\A))]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi:i∈A <;> by_cases hs:i∈S <;> by_cases ht:i∈T <;> simp [hi,hs,ht,eraseActiveBids]

lemma restored_active_parts (A H Q : Finset (Fin m)) (hH:H⊆A) (hQ:Disjoint A Q) :
    ((H∪Q)∩A=H) ∧ ((H∪Q)\A=Q):=by
  have hn (i : Fin m) (hi:i∈Q) : i∉A:=fun h=>Finset.disjoint_left.mp hQ h hi
  constructor
  · ext i
    simp only [Finset.mem_inter,Finset.mem_union]
    constructor
    · rintro ⟨hiH|hiQ,hiA⟩
      · exact hiH
      · exact False.elim (hn i hiQ hiA)
    · intro hiH
      exact ⟨Or.inl hiH,hH hiH⟩
  · ext i
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨hiH|hiQ,hiA⟩
      · exact False.elim (hiA (hH hiH))
      · exact hiQ
    · intro hiQ
      exact ⟨Or.inr hiQ,hn i hiQ⟩

theorem selected_pure_low_maximum_all_counts (κ : ℝ) (hκ:0 ≤ κ) (L : LocalList m)
    (r₀ r₁ : ℕ) (A : Finset (Fin m))
    (hp₀:ActivePriority r₀ A (ResidualPotential.selection κ L r₀ r₁).1)
    (hp₁:ActivePriority r₁ A (ResidualPotential.selection κ L r₀ r₁).2) :
    let P:=ResidualPotential.selection κ L r₀ r₁
    let low:=eraseActiveList A L
    ResidualPotential.Feasible low (r₀-A.card) (r₁-A.card) (P.1\A,P.2\A) ∧
      ∀Q : ResidualPotential.Pair m,ResidualPotential.Feasible low (r₀-A.card) (r₁-A.card) Q →
        CompleteInformation.potential κ (ResidualPotential.bid low) Q.1 Q.2 ≤
          CompleteInformation.potential κ (ResidualPotential.bid low) (P.1\A) (P.2\A):=by
  let P:=ResidualPotential.selection κ L r₀ r₁
  have hf:=ResidualPotential.selection_feasible κ hκ L r₀ r₁
  have hfP:ResidualPotential.Feasible L r₀ r₁ P:=hf
  refine ⟨⟨feasible_erase_priority L r₀ A P.1 hf.1 hp₀,feasible_erase_priority L r₁ A P.2 hf.2 hp₁⟩,?_⟩
  intro Q hQ
  let R:ResidualPotential.Pair m:=((P.1∩A)∪Q.1,(P.2∩A)∪Q.2)
  have hR:ResidualPotential.Feasible L r₀ r₁ R:=
    ⟨feasible_restore_priority L r₀ A P.1 Q.1 hf.1 hp₀ hQ.1,
      feasible_restore_priority L r₁ A P.2 Q.2 hf.2 hp₁ hQ.2⟩
  have hm:=FiniteSelector.select_max (ResidualPotential.objective κ L r₀ r₁) R
  change ResidualPotential.objective κ L r₀ r₁ R ≤ ResidualPotential.objective κ L r₀ r₁ P at hm
  simp only [ResidualPotential.objective,if_pos hR,if_pos hfP] at hm
  rw [potential_partition_active κ (ResidualPotential.bid L) A R.1 R.2,
    potential_partition_active κ (ResidualPotential.bid L) A P.1 P.2] at hm
  have hparts₀:=restored_active_parts A (P.1∩A) Q.1 Finset.inter_subset_right
    (disjoint_active_of_feasible L _ A Q.1 hQ.1)
  have hparts₁:=restored_active_parts A (P.2∩A) Q.2 Finset.inter_subset_right
    (disjoint_active_of_feasible L _ A Q.2 hQ.2)
  change _+CompleteInformation.potential κ (eraseActiveBids A (ResidualPotential.bid L)) _ _ ≤ _ at hm
  dsimp only [R] at hm
  rw [hparts₀.1,hparts₁.1,hparts₀.2,hparts₁.2] at hm
  rw [bid_eraseActiveList]
  exact le_of_add_le_add_left hm

theorem native_pure_low_maximum_all_counts (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX:NonnegativeList X.1)
    (he:residual c 0 X≠residual c 1 X) (d : ℝ) (hd:0 ≤ d) (A : Finset (Fin m))
    (hA:∀i∈A,d<(1-ξ)*entryBid (X.1 i)) (hlow:∀i∉A,entryBid (X.1 i) ≤ d) :
    let P:=purePair ξ c X
    let low:=eraseActiveList A X.1
    ResidualPotential.Feasible low (residual c 0 X-A.card) (residual c 1 X-A.card) (P.1\A,P.2\A) ∧
      ∀Q : ResidualPotential.Pair m,
        ResidualPotential.Feasible low (residual c 0 X-A.card) (residual c 1 X-A.card) Q →
        CompleteInformation.potential (1-ξ) (ResidualPotential.bid low) Q.1 Q.2 ≤
          CompleteInformation.potential (1-ξ) (ResidualPotential.bid low) (P.1\A) (P.2\A):=by
  have hp (j : Fin 2) : ActivePriority (residual c j X) A (select ξ hξ hξ1 c j X (0:unitInterval)):=by
    rcases le_total A.card (residual c j X) with hfit|hover
    · exact Or.inl ⟨hfit,active_included_when_fit ξ hξ hξ1 c X hX j _ d hd A hA hlow hfit⟩
    · exact Or.inr ⟨hover,low_excluded_under_active_overload ξ hξ hξ1 c X hX j _ d A hA hlow hover⟩
  have h0:=hp 0
  have h1:=hp 1
  rw [select,if_neg he,if_pos rfl] at h0
  rw [select,if_neg he,if_neg (by decide : (1:Fin 2)≠0)] at h1
  exact selected_pure_low_maximum_all_counts (1-ξ) (by linarith) X.1
    (residual c 0 X) (residual c 1 X) A h0 h1

end FCAppendix.Affine.Hybrid.NativeContinuation
