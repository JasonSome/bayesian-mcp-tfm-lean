import FCAppendix.Affine.CompleteInformationPotential
import FCAppendix.Existence.HighestBidPolicy

noncomputable section
namespace FCAppendix.Affine.ResidualPotential
open MeasureTheory Set Game Classical
open scoped BigOperators

abbrev Pair (m : ℕ) := Finset (Fin m) × Finset (Fin m)

def bid {m : ℕ} (L : LocalList m) (i : Fin m) : ℝ := max (Bayes.entryBid (L i)) 0

def Feasible {m : ℕ} (L : LocalList m) (r₀ r₁ : ℕ) (P : Pair m) : Prop :=
  LocallyFeasible L r₀ P.1 ∧ LocallyFeasible L r₁ P.2

def objective {m : ℕ} (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ) (P : Pair m) : ℝ :=
  if Feasible L r₀ r₁ P then LowBody.CompleteInformation.potential κ (bid L) P.1 P.2 else -1

def selection {m : ℕ} (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ) : Pair m :=
  FiniteSelector.select (objective κ L r₀ r₁)

lemma potential_nonneg {m : ℕ} (κ : ℝ) (hκ : 0≤κ) (L : LocalList m) (P : Pair m) :
    0≤LowBody.CompleteInformation.potential κ (bid L) P.1 P.2 := by
  unfold LowBody.CompleteInformation.potential
  exact add_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _)
    (mul_nonneg hκ (Finset.sum_nonneg fun i _ => le_max_right _ _))

theorem selection_feasible {m : ℕ} (κ : ℝ) (_hκ : 0≤κ)
    (L : LocalList m) (r₀ r₁ : ℕ) : Feasible L r₀ r₁ (selection κ L r₀ r₁) := by
  have hm := FiniteSelector.select_max (objective κ L r₀ r₁) ((∅,∅) : Pair m)
  have he : objective κ L r₀ r₁ ((∅,∅) : Pair m)=0 := by
    simp [objective,Feasible,LocallyFeasible,LowBody.CompleteInformation.potential]
  rw [he] at hm
  change 0≤objective κ L r₀ r₁ (selection κ L r₀ r₁) at hm
  by_contra hn
  simp only [objective,if_neg hn] at hm
  norm_num at hm

theorem selection_nash {m : ℕ} (κ : ℝ) (hκ : 0≤κ)
    (L : LocalList m) (r₀ r₁ : ℕ) :
    (∀ S, LocallyFeasible L r₀ S →
      LowBody.CompleteInformation.revenue κ (bid L) S (selection κ L r₀ r₁).2 ≤
        LowBody.CompleteInformation.revenue κ (bid L) (selection κ L r₀ r₁).1 (selection κ L r₀ r₁).2) ∧
    (∀ T, LocallyFeasible L r₁ T →
      LowBody.CompleteInformation.revenue κ (bid L) T (selection κ L r₀ r₁).1 ≤
        LowBody.CompleteInformation.revenue κ (bid L) (selection κ L r₀ r₁).2 (selection κ L r₀ r₁).1) := by
  have hf := selection_feasible κ hκ L r₀ r₁
  have hm (P : Pair m) (hP : Feasible L r₀ r₁ P) :
      LowBody.CompleteInformation.potential κ (bid L) P.1 P.2 ≤
        LowBody.CompleteInformation.potential κ (bid L) (selection κ L r₀ r₁).1 (selection κ L r₀ r₁).2 := by
    have hh := FiniteSelector.select_max (objective κ L r₀ r₁) P
    change objective κ L r₀ r₁ P≤objective κ L r₀ r₁ (selection κ L r₀ r₁) at hh
    simpa [objective,hP,hf] using hh
  constructor
  · intro S hS
    have hh := hm (S,(selection κ L r₀ r₁).2) ⟨hS,hf.2⟩
    rw [LowBody.CompleteInformation.potential_eq_revenue_add,LowBody.CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh
  · intro T hT
    have hh := hm ((selection κ L r₀ r₁).1,T) ⟨hf.1,hT⟩
    change LowBody.CompleteInformation.potential κ (bid L) (selection κ L r₀ r₁).1 T ≤
      LowBody.CompleteInformation.potential κ (bid L) (selection κ L r₀ r₁).1 (selection κ L r₀ r₁).2 at hh
    rw [LowBody.CompleteInformation.potential_comm κ (bid L) (selection κ L r₀ r₁).1 T,
      LowBody.CompleteInformation.potential_comm κ (bid L) (selection κ L r₀ r₁).1 (selection κ L r₀ r₁).2,
      LowBody.CompleteInformation.potential_eq_revenue_add,LowBody.CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh

private theorem nash_card {m : ℕ} (κ : ℝ) (hκ : 0<κ) (L : LocalList m)
    (r : ℕ) (S T : Finset (Fin m)) (hS : LocallyFeasible L r S)
    (hpos : ∀ i, L i≠none → 0<bid L i)
    (hm : ∀ D, LocallyFeasible L r D →
      LowBody.CompleteInformation.revenue κ (bid L) D T ≤
        LowBody.CompleteInformation.revenue κ (bid L) S T) :
    S.card=min r (Finset.univ.filter (fun i => L i≠none)).card := by
  let A := Finset.univ.filter (fun i => L i≠none)
  have hSA : S⊆A := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i,hS.2 i hi⟩
  have hbound : S.card≤ min r A.card := le_min hS.1 (Finset.card_le_card hSA)
  apply le_antisymm hbound
  by_contra hn
  have hlt : S.card< min r A.card := lt_of_not_ge hn
  obtain ⟨i,hiA,hiS⟩ := Finset.exists_mem_notMem_of_card_lt_card (hlt.trans_le (min_le_right _ _))
  have hiL : L i≠none := (Finset.mem_filter.mp hiA).2
  have hD : LocallyFeasible L r (insert i S) := by
    refine ⟨?_,?_⟩
    · rw [Finset.card_insert_of_notMem hiS]
      exact Nat.succ_le_of_lt (hlt.trans_le (min_le_left _ _))
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji|hjS
      · exact hji ▸ hiL
      · exact hS.2 j hjS
  have h := hm (insert i S) hD
  have hp : 0<(if i∈T then κ*bid L i else bid L i) := by
    split
    · exact mul_pos hκ (hpos i hiL)
    · exact hpos i hiL
  unfold LowBody.CompleteInformation.revenue at h
  rw [Finset.sum_insert hiS] at h
  linarith

theorem selection_card {m : ℕ} (κ : ℝ) (hκ : 0<κ) (L : LocalList m)
    (r₀ r₁ : ℕ) (hpos : ∀ i, L i≠none → 0<bid L i) :
    (selection κ L r₀ r₁).1.card=min r₀ (Finset.univ.filter (fun i => L i≠none)).card ∧
    (selection κ L r₀ r₁).2.card=min r₁ (Finset.univ.filter (fun i => L i≠none)).card := by
  have hf := selection_feasible κ hκ.le L r₀ r₁
  have hm := selection_nash κ hκ.le L r₀ r₁
  exact ⟨nash_card κ hκ L r₀ _ _ hf.1 hpos hm.1,
    nash_card κ hκ L r₁ _ _ hf.2 hpos hm.2⟩

lemma measurableSet_feasible {m : ℕ} {X : Type*} [MeasurableSpace X]
    {L : X→LocalList m} {r₀ r₁ : X→ℕ} (hL : Measurable L)
    (hr₀ : Measurable r₀) (hr₁ : Measurable r₁) (P : Pair m) :
    MeasurableSet {x | Feasible (L x) (r₀ x) (r₁ x) P} := by
  have hf (S : Finset (Fin m)) (r : X→ℕ) (hr : Measurable r) :
      MeasurableSet {x | LocallyFeasible (L x) (r x) S} := by
    simp only [LocallyFeasible,setOf_and,setOf_forall]
    apply (measurableSet_le measurable_const hr).inter
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun ((measurable_pi_apply i).comp hL) measurable_const).compl
  exact (hf P.1 r₀ hr₀).inter (hf P.2 r₁ hr₁)

theorem measurable_selection {m : ℕ} {X : Type*} [MeasurableSpace X]
    {κ : X→ℝ} {L : X→LocalList m} {r₀ r₁ : X→ℕ}
    (hκ : Measurable κ) (hL : Measurable L)
    (hr₀ : Measurable r₀) (hr₁ : Measurable r₁) :
    Measurable (fun x => selection (κ x) (L x) (r₀ x) (r₁ x)) := by
  apply FiniteSelector.measurable_select
  intro P
  unfold objective
  apply Measurable.ite (measurableSet_feasible hL hr₀ hr₁ P) _ measurable_const
  unfold LowBody.CompleteInformation.potential bid
  have hb (i : Fin m) : Measurable (fun x => max (Bayes.entryBid (L x i)) 0) :=
    ((Bayes.measurable_entryBid.comp ((measurable_pi_apply i).comp hL)).max measurable_const)
  exact (Finset.measurable_sum _ fun i _ => hb i).add
    (hκ.mul (Finset.measurable_sum _ fun i _ => hb i))
end FCAppendix.Affine.ResidualPotential
