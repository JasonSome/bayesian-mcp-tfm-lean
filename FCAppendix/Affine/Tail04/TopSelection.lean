import FCAppendix.Affine.CompleteInformationPotential
import FCAppendix.Affine.Hybrid.ClassifiedPolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.AtypicalUnequal
open MeasureTheory Set Filter Topology Classical
open scoped BigOperators

section Selector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def TopFeasible (A : Finset ι) (c : ℕ) (S : Finset ι) : Prop :=
  S.card ≤ c ∧ S ⊆ A

def topObjective (A : Finset ι) (c : ℕ) (b : ι → ℝ) (S : Finset ι) : ℝ :=
  if TopFeasible A c S then ∑ i ∈ S, max (b i) 0 else -1

def topSelection (A : Finset ι) (c : ℕ) (b : ι → ℝ) : Finset ι :=
  FiniteSelector.select (topObjective A c b)

def topValue (A : Finset ι) (b : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ A then max (b i) 0 else 0

omit [DecidableEq ι] in
theorem topSelection_feasible (A : Finset ι) (c : ℕ) (b : ι → ℝ) :
    TopFeasible A c (topSelection A c b) := by
  have hm := FiniteSelector.select_max (topObjective A c b) ∅
  have he : topObjective A c b ∅ = 0 := by
    simp [topObjective, TopFeasible]
  rw [he] at hm
  change 0 ≤ topObjective A c b (topSelection A c b) at hm
  by_contra hn
  simp [topObjective, hn] at hm
  linarith

omit [DecidableEq ι] in
theorem topSelection_max (A : Finset ι) (c : ℕ) (b : ι → ℝ)
    (S : Finset ι) (hS : TopFeasible A c S) :
    (∑ i ∈ S, max (b i) 0) ≤ ∑ i ∈ topSelection A c b, max (b i) 0 := by
  have h := FiniteSelector.select_max (topObjective A c b) S
  change topObjective A c b S ≤ topObjective A c b (topSelection A c b) at h
  simpa only [topObjective, if_pos hS, if_pos (topSelection_feasible A c b)] using h

theorem topSelection_optimal (A : Finset ι) (c : ℕ) (b : ι → ℝ) :
    Finite.Optimal c (topValue A b) (topSelection A c b) := by
  have hs := topSelection_feasible A c b
  refine ⟨hs.1, ?_⟩
  intro T hT
  let U := T ∩ A
  have hU : TopFeasible A c U :=
    ⟨(Finset.card_le_card Finset.inter_subset_left).trans hT, Finset.inter_subset_right⟩
  have heT : (∑ i ∈ T, topValue A b i) = ∑ i ∈ U, max (b i) 0 := by
    dsimp only [U, topValue]
    rw [← Finset.filter_mem_eq_inter, Finset.sum_filter]
  have heS : (∑ i ∈ topSelection A c b, topValue A b i) =
      ∑ i ∈ topSelection A c b, max (b i) 0 := by
    exact Finset.sum_congr rfl (fun i hi => by simp [topValue, hs.2 hi])
  rw [heT, heS]
  exact topSelection_max A c b U hU

theorem topSelection_card (A : Finset ι) (c : ℕ) (b : ι → ℝ)
    (hb : ∀ i ∈ A, 0 < b i) :
    (topSelection A c b).card = min c A.card := by
  have hs := topSelection_feasible A c b
  have hbound := le_min hs.1 (Finset.card_le_card hs.2)
  apply le_antisymm hbound
  by_contra hn
  have hlt : (topSelection A c b).card < min c A.card := lt_of_not_ge hn
  obtain ⟨i, hiA, hiS⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (hlt.trans_le (min_le_right _ _))
  have hi : 0 < topValue A b i := by
    simpa [topValue, hiA, max_eq_left (hb i hiA).le] using hb i hiA
  have hfill := Finite.optimal_fills c _ _ (topSelection_optimal A c b) i hiS hi
  omega

theorem topSelection_order (A : Finset ι) (c : ℕ) (b : ι → ℝ)
    (hb : ∀ i ∈ A, 0 ≤ b i) (i j : ι)
    (hi : i ∈ topSelection A c b) (hjA : j ∈ A)
    (hj : j ∉ topSelection A c b) : b j ≤ b i := by
  have hiA := (topSelection_feasible A c b).2 hi
  simpa only [topValue, if_pos hiA, if_pos hjA,
    max_eq_left (hb i hiA), max_eq_left (hb j hjA)] using
    Finite.optimal_swap c _ _ (topSelection_optimal A c b) i j hi hj

theorem topSelection_higher_first (A : Finset ι) (c : ℕ) (b : ι → ℝ)
    (hb : ∀ i ∈ A, 0 ≤ b i) (i j : ι)
    (hiA : i ∈ A) (hj : j ∈ topSelection A c b) (hij : b j < b i) :
    i ∈ topSelection A c b := by
  by_contra hi
  exact (not_le_of_gt hij) (topSelection_order A c b hb j i hj hiA hi)

theorem topSelection_iff_strict_rank (A : Finset ι) (c : ℕ) (b : ι → ℝ)
    (hb : ∀ j ∈ A, 0 ≤ b j) (i : ι) (hiA : i ∈ A) (hbi : 0 < b i)
    (hno : ∀ j ∈ A, j ≠ i → b j ≠ b i) :
    i ∈ topSelection A c b ↔ (A.filter (fun j => b i < b j)).card < c := by
  have hri : topValue A b i = b i := by
    simp only [topValue, if_pos hiA, max_eq_left hbi.le]
  have hbetter : (Finset.univ.filter (fun j => topValue A b i < topValue A b j)) =
      A.filter (fun j => b i < b j) := by
    ext j
    by_cases hjA : j ∈ A
    · simp [topValue, hiA, hjA, max_eq_left (hb i hiA), max_eq_left (hb j hjA)]
    · simp [topValue, hiA, hjA, max_eq_left hbi.le, not_lt.mpr hbi.le]
  have hcomp : (Finset.univ.filter (fun j => j ≠ i ∧
      topValue A b i ≤ topValue A b j)) = A.filter (fun j => b i < b j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hjA : j ∈ A
    · rw [hri, show topValue A b j = b j by simp [topValue, hjA, max_eq_left (hb j hjA)]]
      constructor
      · intro hj
        exact ⟨hjA, lt_of_le_of_ne hj.2 (hno j hjA hj.1).symm⟩
      · intro hj
        exact ⟨fun he => by subst j; exact (lt_irrefl _ hj.2), hj.2.le⟩
    · rw [hri, show topValue A b j = 0 by simp [topValue, hjA]]
      simp [hjA, not_le.mpr hbi]
  constructor
  · intro hi
    by_contra hn
    have hh := Finite.excluded_of_many_better c _ _ (topSelection_optimal A c b) i
      (by rw [hbetter]; exact le_of_not_gt hn)
    exact hh hi
  · intro hrank
    exact Finite.included_of_few_competitors c _ _ (topSelection_optimal A c b) i
      (by simpa only [hri] using hbi) (by simpa only [hcomp] using hrank)

theorem topSelection_contains_priority (A O : Finset ι) (c : ℕ) (b : ι → ℝ)
    (hOA : O ⊆ A) (hOc : O.card ≤ c)
    (hO : ∀ i ∈ O, 0 < b i)
    (hsep : ∀ i ∈ O, ∀ j ∈ A, j ∉ O → b j < b i) :
    O ⊆ topSelection A c b := by
  intro i hi
  have hbi : 0 < topValue A b i := by
    simp only [topValue, if_pos (hOA hi), max_eq_left (hO i hi).le]
    exact hO i hi
  apply Finite.included_of_few_competitors c _ _ (topSelection_optimal A c b) i hbi
  have hsub : (Finset.univ.filter (fun j => j ≠ i ∧
      topValue A b i ≤ topValue A b j)) ⊆ O.erase i := by
    intro j hj
    obtain ⟨hji, hscore⟩ := (Finset.mem_filter.mp hj).2
    apply Finset.mem_erase.mpr
    refine ⟨hji, ?_⟩
    by_contra hjO
    by_cases hjA : j ∈ A
    · have hbji := hsep i hi j hjA hjO
      have hmax : max (b j) 0 < b i := max_lt hbji (hO i hi)
      simp only [topValue, if_pos (hOA hi), if_pos hjA,
        max_eq_left (hO i hi).le] at hscore
      linarith
    · rw [show topValue A b j = 0 by simp [topValue, hjA]] at hscore
      linarith
  have hh := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hi] at hh
  have hp : 0 < O.card := Finset.card_pos.mpr ⟨i, hi⟩
  omega

theorem topSelection_receipt_optimal (A : Finset ι) (c : ℕ) (b rho : ι → ℝ)
    (hAc : c ≤ A.card) (hb : ∀ i ∈ A, 0 < b i)
    (hrho0 : ∀ i, 0 ≤ rho i) (hrho : ∀ i ∈ A, rho i = b i)
    (houtside : ∀ i ∈ A, ∀ j ∉ A, rho j ≤ b i) :
    Finite.Optimal c rho (topSelection A c b) := by
  have hs := topSelection_feasible A c b
  have hc : (topSelection A c b).card = c := by
    rw [topSelection_card A c b hb, min_eq_left hAc]
  have he : topValue A b = fun i => if i ∈ A then rho i else 0 := by
    funext i
    by_cases hi : i ∈ A
    · simp [topValue, hi, hrho i hi, max_eq_left (hb i hi).le]
    · simp [topValue, hi]
  apply Hybrid.priority_full_optimal c rho A _ hs.2 hc hrho0
  · intro i hi j hj
    simpa only [hrho i hi] using houtside i hi j hj
  · rw [← he]
    exact topSelection_optimal A c b

theorem measurable_topSelection
    {X : Type*} [MeasurableSpace X]
    [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
    (c : ℕ) (A : X → Finset ι) (b : X → ι → ℝ)
    (hA : Measurable A) (hb : ∀ i, Measurable (fun x => b x i)) :
    Measurable (fun x => topSelection (A x) c (b x)) := by
  apply FiniteSelector.measurable_select
  intro S
  have hsub : MeasurableSet {x | S ⊆ A x} := by
    change MeasurableSet {x | ∀ i, i ∈ S → i ∈ A x}
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _hi
    exact (Set.to_countable {T : Finset ι | i ∈ T}).measurableSet.preimage hA
  have hf : MeasurableSet {x | TopFeasible (A x) c S} := by
    by_cases hSc : S.card ≤ c
    · simpa only [TopFeasible, hSc, true_and] using hsub
    · simp [TopFeasible, hSc]
  exact Measurable.ite hf
    (Finset.measurable_sum _ (fun i _ => (hb i).max measurable_const)) measurable_const

def topLaw (A : Finset ι) (c : ℕ) (b : ι → ℝ) : FiniteLaw (Finset ι) :=
  FiniteLaw.dirac (topSelection A c b)

theorem topLaw_support (A : Finset ι) (c : ℕ) (b : ι → ℝ)
    (S : Finset ι) (hS : (topLaw A c b).mass S ≠ 0) :
    TopFeasible A c S := by
  have he : S = topSelection A c b := by
    by_contra hn
    exact hS (by simp [topLaw, FiniteLaw.dirac, hn])
  rw [he]
  exact topSelection_feasible A c b

end Selector

end FCAppendix.Affine.Tail04.AtypicalUnequal
