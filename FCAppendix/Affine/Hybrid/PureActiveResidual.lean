import FCAppendix.Affine.Hybrid.EqualActiveResidual

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes
open scoped BigOperators
variable {m : ℕ}

def eraseActiveList (A : Finset (Fin m)) (L : LocalList m) : LocalList m:=
  fun i=>if i∈A then none else L i

lemma bid_eraseActiveList (A : Finset (Fin m)) (L : LocalList m) :
    ResidualPotential.bid (eraseActiveList A L)=eraseActiveBids A (ResidualPotential.bid L):=by
  funext i
  by_cases hi:i∈A <;> simp [eraseActiveList,eraseActiveBids,ResidualPotential.bid,hi,entryBid]

lemma potential_erase_active (κ : ℝ) (b : Fin m→ℝ) (A S T : Finset (Fin m))
    (hAS : A⊆S) (hAT : A⊆T) :
    LowBody.CompleteInformation.potential κ b S T=(1+κ)*(∑i∈A,b i)+
      LowBody.CompleteInformation.potential κ (eraseActiveBids A b) (S\A) (T\A):=by
  have hsum (D : Finset (Fin m)) (f : Fin m→ℝ) : (∑i∈D,f i)=∑i,if i∈D then f i else 0:=by simp
  unfold LowBody.CompleteInformation.potential
  rw [hsum (S∪T),hsum (S∩T),hsum A,hsum ((S\A)∪(T\A)),hsum ((S\A)∩(T\A))]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi:i∈A
  · have hs:=hAS hi
    have ht:=hAT hi
    simp [hi,hs,ht]
    ring
  · by_cases hs:i∈S <;> by_cases ht:i∈T <;> simp [hi,hs,ht,eraseActiveBids]

lemma feasible_erase_active (L : LocalList m) (r : ℕ) (A S : Finset (Fin m))
    (hS : LocallyFeasible L r S) (hAS : A⊆S) :
    LocallyFeasible (eraseActiveList A L) (r-A.card) (S\A):=by
  refine ⟨?_,?_⟩
  · rw [Finset.card_sdiff_of_subset hAS]
    exact Nat.sub_le_sub_right hS.1 A.card
  · intro i hi
    obtain ⟨hiS,hiA⟩:=Finset.mem_sdiff.mp hi
    simpa only [eraseActiveList,if_neg hiA] using hS.2 i hiS

lemma feasible_add_active (L : LocalList m) (r : ℕ) (A S : Finset (Fin m))
    (hA : ∀i∈A,L i≠none) (hfit : A.card ≤ r)
    (hS : LocallyFeasible (eraseActiveList A L) (r-A.card) S) :
    LocallyFeasible L r (A∪S):=by
  refine ⟨(Finset.card_union_le _ _).trans ?_,?_⟩
  · have hh:=hS.1
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hiA|hiS
    · exact hA i hiA
    · have hh:=hS.2 i hiS
      by_cases hiA:i∈A
      · simp only [eraseActiveList,if_pos hiA] at hh
        exact False.elim (hh rfl)
      · simpa only [eraseActiveList,if_neg hiA] using hh

lemma disjoint_active_of_feasible (L : LocalList m) (r : ℕ) (A S : Finset (Fin m))
    (hS : LocallyFeasible (eraseActiveList A L) r S) : Disjoint A S:=by
  apply Finset.disjoint_left.mpr
  intro i hiA hiS
  have hh:=hS.2 i hiS
  simp only [eraseActiveList,if_pos hiA] at hh
  exact hh rfl

theorem selected_pure_low_maximum (κ : ℝ) (hκ : 0 ≤ κ) (L : LocalList m)
    (r₀ r₁ : ℕ) (A : Finset (Fin m))
    (hA₀ : A⊆(ResidualPotential.selection κ L r₀ r₁).1)
    (hA₁ : A⊆(ResidualPotential.selection κ L r₀ r₁).2) :
    let P:=ResidualPotential.selection κ L r₀ r₁
    let low:=eraseActiveList A L
    ResidualPotential.Feasible low (r₀-A.card) (r₁-A.card) (P.1\A,P.2\A) ∧
      ∀Q : ResidualPotential.Pair m,ResidualPotential.Feasible low (r₀-A.card) (r₁-A.card) Q→
        LowBody.CompleteInformation.potential κ (ResidualPotential.bid low) Q.1 Q.2 ≤
          LowBody.CompleteInformation.potential κ (ResidualPotential.bid low) (P.1\A) (P.2\A):=by
  let P:=ResidualPotential.selection κ L r₀ r₁
  have hf:=ResidualPotential.selection_feasible κ hκ L r₀ r₁
  have hfP : ResidualPotential.Feasible L r₀ r₁ P:=hf
  have hfit₀ : A.card ≤ r₀:=(Finset.card_le_card hA₀).trans hf.1.1
  have hfit₁ : A.card ≤ r₁:=(Finset.card_le_card hA₁).trans hf.2.1
  have hAv : ∀i∈A,L i≠none:=fun i hi=>hf.1.2 i (hA₀ hi)
  refine ⟨⟨feasible_erase_active L r₀ A P.1 hf.1 hA₀,feasible_erase_active L r₁ A P.2 hf.2 hA₁⟩,?_⟩
  intro Q hQ
  have hQfull : ResidualPotential.Feasible L r₀ r₁ (A∪Q.1,A∪Q.2):=
    ⟨feasible_add_active L r₀ A Q.1 hAv hfit₀ hQ.1,
      feasible_add_active L r₁ A Q.2 hAv hfit₁ hQ.2⟩
  have hm:=FiniteSelector.select_max (ResidualPotential.objective κ L r₀ r₁) (A∪Q.1,A∪Q.2)
  change ResidualPotential.objective κ L r₀ r₁ (A∪Q.1,A∪Q.2) ≤
    ResidualPotential.objective κ L r₀ r₁ P at hm
  simp only [ResidualPotential.objective,if_pos hQfull,if_pos hfP] at hm
  rw [potential_erase_active κ (ResidualPotential.bid L) A (A∪Q.1) (A∪Q.2)
      Finset.subset_union_left Finset.subset_union_left,
    potential_erase_active κ (ResidualPotential.bid L) A P.1 P.2 hA₀ hA₁] at hm
  rw [Finset.union_sdiff_cancel_left (disjoint_active_of_feasible L _ A Q.1 hQ.1),
    Finset.union_sdiff_cancel_left (disjoint_active_of_feasible L _ A Q.2 hQ.2)] at hm
  rw [bid_eraseActiveList]
  exact le_of_add_le_add_left hm

theorem native_pure_low_maximum (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (he:residual c 0 X≠residual c 1 X) (d : ℝ) (hd : 0 ≤ d) (A : Finset (Fin m))
    (hA : ∀i∈A,d<(1-ξ)*entryBid (X.1 i)) (hlow : ∀i∉A,entryBid (X.1 i) ≤ d)
    (hfit₀ : A.card ≤ residual c 0 X) (hfit₁ : A.card ≤ residual c 1 X) :
    let P:=purePair ξ c X
    let low:=eraseActiveList A X.1
    ResidualPotential.Feasible low (residual c 0 X-A.card) (residual c 1 X-A.card) (P.1\A,P.2\A) ∧
      ∀Q : ResidualPotential.Pair m,
        ResidualPotential.Feasible low (residual c 0 X-A.card) (residual c 1 X-A.card) Q→
        LowBody.CompleteInformation.potential (1-ξ) (ResidualPotential.bid low) Q.1 Q.2 ≤
          LowBody.CompleteInformation.potential (1-ξ) (ResidualPotential.bid low) (P.1\A) (P.2\A):=by
  have hA₀:=active_included_when_fit ξ hξ hξ1 c X hX 0 (0:unitInterval) d hd A hA hlow hfit₀
  have hA₁:=active_included_when_fit ξ hξ hξ1 c X hX 1 (0:unitInterval) d hd A hA hlow hfit₁
  rw [select,if_neg he,if_pos rfl] at hA₀
  rw [select,if_neg he,if_neg (by decide : (1:Fin 2)≠0)] at hA₁
  exact selected_pure_low_maximum (1-ξ) (by linarith) X.1 (residual c 0 X) (residual c 1 X) A hA₀ hA₁

end FCAppendix.Affine.Hybrid.NativeContinuation
