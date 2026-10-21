import FCAppendix.Affine.Hybrid.NativeContinuation
import FCAppendix.Affine.LowBody.PureTemplate

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.AppendixRepair.GeneralLow.ExactLow
open MeasureTheory ProbabilityTheory Set Game Bayes Affine Affine.LowBody
open Existence.PayOnceBounded (listBids measurable_listBids)
open scoped BigOperators

attribute [local irreducible] Hybrid.NativeEqual.sample

variable {m : ℕ}

def visible (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => L i ≠ none)

theorem mem_visible (L : LocalList m) (i : Fin m) :
    i ∈ visible L ↔ L i ≠ none := by
  classical
  simp [visible]

theorem measurable_visible : Measurable (visible (m := m)) := by
  classical
  let mask : LocalList m → Fin m → Fin 2 :=
    fun L i => if L i = none then 0 else 1
  have hm : Measurable mask := by
    apply measurable_pi_iff.mpr
    intro i
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
      measurable_const measurable_const
  have he : visible (m := m) =
      (fun k : Fin m → Fin 2 => Finset.univ.filter (fun i => k i = 1)) ∘ mask := by
    funext L
    ext i
    simp [visible, mask]
  rw [he]
  exact (measurable_of_countable _).comp hm

def template (L : LocalList m) (r₀ r₁ : ℕ) : PureTemplate (Fin m) where
  support := visible L
  residual₀ := r₀
  residual₁ := r₁

theorem listBids_eq_residualBid (L : LocalList m) (hL : NonnegativeList L) :
    listBids L = ResidualPotential.bid L := by
  funext i
  have hb : listBids L i = entryBid (L i) := by
    cases h : L i <;> simp [listBids, entryBid, h]
  rw [hb]
  exact (max_eq_left (hL i)).symm

theorem template_feasible (L : LocalList m) (r₀ r₁ : ℕ)
    (P : Finset (Fin m) × Finset (Fin m)) :
    (template L r₀ r₁).Feasible P ↔
      LocallyFeasible L r₀ P.1 ∧ LocallyFeasible L r₁ P.2 := by
  classical
  have hs (S : Finset (Fin m)) :
      S ⊆ visible L ↔ ∀ i ∈ S, L i ≠ none := by
    simp only [Finset.subset_iff, mem_visible]
  simp only [PureTemplate.Feasible, template, LocallyFeasible, hs]
  tauto

def purePair (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ) :
    Finset (Fin m) × Finset (Fin m) :=
  if r₀ < r₁ then ((template L r₁ r₀).selection κ (listBids L)).swap
  else (template L r₀ r₁).selection κ (listBids L)

theorem purePair_of_ge (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ)
    (hge : r₁ ≤ r₀) :
    purePair κ L r₀ r₁ = (template L r₀ r₁).selection κ (listBids L) := by
  exact if_neg (not_lt_of_ge hge)

theorem purePair_of_lt (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ)
    (hlt : r₀ < r₁) :
    purePair κ L r₀ r₁ = ((template L r₁ r₀).selection κ (listBids L)).swap := by
  exact if_pos hlt

theorem purePair_feasible (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ) :
    LocallyFeasible L r₀ (purePair κ L r₀ r₁).1 ∧
      LocallyFeasible L r₁ (purePair κ L r₀ r₁).2 := by
  unfold purePair
  split
  · have hf := (template_feasible L r₁ r₀ _).mp
      ((template L r₁ r₀).selection_feasible κ (listBids L))
    exact ⟨hf.2, hf.1⟩
  · exact (template_feasible L r₀ r₁ _).mp
      ((template L r₀ r₁).selection_feasible κ (listBids L))

theorem purePair_swap (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ)
    (hne : r₀ ≠ r₁) :
    purePair κ L r₁ r₀ = (purePair κ L r₀ r₁).swap := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simp only [purePair, if_pos hlt, if_neg (not_lt_of_ge hlt.le), Prod.swap_swap]
  · simp only [purePair, if_pos hgt, if_neg (not_lt_of_ge hgt.le)]

theorem purePair_max (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ)
    (Q : Finset (Fin m) × Finset (Fin m))
    (hQ : (template L r₀ r₁).Feasible Q) :
    CompleteInformation.potential κ (listBids L) Q.1 Q.2 ≤
      CompleteInformation.potential κ (listBids L)
        (purePair κ L r₀ r₁).1 (purePair κ L r₀ r₁).2 := by
  unfold purePair
  split
  · have hs : (template L r₁ r₀).Feasible Q.swap :=
      ⟨hQ.2.2.1, hQ.2.2.2, hQ.1, hQ.2.1⟩
    have hh := (template L r₁ r₀).selection_max κ (listBids L) Q.swap hs
    simpa only [Prod.fst_swap, Prod.snd_swap,
      CompleteInformation.potential_comm κ (listBids L) Q.2 Q.1,
      CompleteInformation.potential_comm κ (listBids L)
        ((template L r₁ r₀).selection κ (listBids L)).2
        ((template L r₁ r₀).selection κ (listBids L)).1] using hh
  · exact (template L r₀ r₁).selection_max κ (listBids L) Q hQ

theorem purePair_nash (κ : ℝ) (L : LocalList m) (r₀ r₁ : ℕ) :
    (∀ S, LocallyFeasible L r₀ S →
      CompleteInformation.revenue κ (listBids L) S (purePair κ L r₀ r₁).2 ≤
        CompleteInformation.revenue κ (listBids L)
          (purePair κ L r₀ r₁).1 (purePair κ L r₀ r₁).2) ∧
    (∀ S, LocallyFeasible L r₁ S →
      CompleteInformation.revenue κ (listBids L) S (purePair κ L r₀ r₁).1 ≤
        CompleteInformation.revenue κ (listBids L)
          (purePair κ L r₀ r₁).2 (purePair κ L r₀ r₁).1) := by
  have hf := purePair_feasible κ L r₀ r₁
  constructor
  · intro S hS
    have hh := purePair_max κ L r₀ r₁ (S, (purePair κ L r₀ r₁).2)
      ((template_feasible L r₀ r₁ _).mpr ⟨hS, hf.2⟩)
    rw [CompleteInformation.potential_eq_revenue_add,
      CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh
  · intro S hS
    have hh := purePair_max κ L r₀ r₁ ((purePair κ L r₀ r₁).1, S)
      ((template_feasible L r₀ r₁ _).mpr ⟨hf.1, hS⟩)
    rw [CompleteInformation.potential_comm κ (listBids L) (purePair κ L r₀ r₁).1 S,
      CompleteInformation.potential_comm κ (listBids L)
        (purePair κ L r₀ r₁).1 (purePair κ L r₀ r₁).2,
      CompleteInformation.potential_eq_revenue_add,
      CompleteInformation.potential_eq_revenue_add] at hh
    exact le_of_add_le_add_right hh

private theorem measurable_fixedSelection (T : PureTemplate (Fin m)) (κ : ℝ) :
    Measurable (T.selection κ) := by
  have hm := FiniteSelector.measurable_select
    (fun (b : Fin m → ℝ) (P : T.Candidate) =>
      CompleteInformation.potential κ b P.val.1 P.val.2)
    (fun P => (continuous_potential κ P.val).measurable)
  exact measurable_subtype_coe.comp hm

theorem measurable_purePair {X : Type*} [MeasurableSpace X]
    (κ : ℝ) (L : X → LocalList m) (hL : Measurable L)
    (r₀ r₁ : X → ℕ) (h₀ : Measurable r₀) (h₁ : Measurable r₁) :
    Measurable (fun x => purePair κ (L x) (r₀ x) (r₁ x)) := by
  let T : (Finset (Fin m) × (ℕ × ℕ)) → PureTemplate (Fin m) :=
    fun k => ⟨k.1, k.2.1, k.2.2⟩
  have hsel (a b : X → ℕ) (ha : Measurable a) (hb : Measurable b) :
      Measurable (fun x => (template (L x) (a x) (b x)).selection κ (listBids (L x))) := by
    have hm : Measurable (fun q : (Finset (Fin m) × (ℕ × ℕ)) × (Fin m → ℝ) =>
        (T q.1).selection κ q.2) :=
      measurable_from_prod_countable_right (fun k => measurable_fixedSelection (T k) κ)
    exact hm.comp (((measurable_visible.comp hL).prodMk (ha.prodMk hb)).prodMk
      (measurable_listBids.comp hL))
  exact Measurable.ite (measurableSet_lt h₀ h₁)
    ((measurable_of_countable Prod.swap).comp (hsel r₁ r₀ h₁ h₀))
    (hsel r₀ r₁ h₀ h₁)

def select (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (own other : ℕ) (s : unitInterval) : Finset (Fin m) :=
  if own = other then Hybrid.NativeEqual.sample m ξ hξ hξ1 own L s
  else (purePair (1 - ξ) L own other).1

theorem select_feasible (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (own other : ℕ) (s : unitInterval) :
    LocallyFeasible L own (select ξ hξ hξ1 L own other s) := by
  unfold select
  split
  · exact Hybrid.NativeEqual.sample_feasible m ξ hξ hξ1 own L s
  · exact (purePair_feasible (1 - ξ) L own other).1

theorem measurable_select {X : Type*} [MeasurableSpace X]
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : X → LocalList m) (hL : Measurable L)
    (own other : X → ℕ) (ho : Measurable own) (ht : Measurable other)
    (s : X → unitInterval) (hs : Measurable s) :
    Measurable (fun x => select ξ hξ hξ1 (L x) (own x) (other x) (s x)) := by
  unfold select
  refine Measurable.ite (measurableSet_eq_fun ho ht) ?_ ?_
  · exact (Hybrid.NativeEqual.measurable_sample_capacity m ξ hξ hξ1).comp
      (ho.prodMk (hL.prodMk hs))
  · exact (measurable_purePair (1 - ξ) L hL own other ho ht).fst

theorem select_pure_pair (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (r₀ r₁ : ℕ) (hne : r₀ ≠ r₁)
    (s₀ s₁ : unitInterval) :
    (select ξ hξ hξ1 L r₀ r₁ s₀, select ξ hξ hξ1 L r₁ r₀ s₁) =
      purePair (1 - ξ) L r₀ r₁ := by
  simp only [select, if_neg hne, if_neg (Ne.symm hne),
    purePair_swap (1 - ξ) L r₀ r₁ hne, Prod.fst_swap]

def acceptance (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (own other : ℕ) (i : Fin m) : ℝ :=
  ∫ s : unitInterval, if i ∈ select ξ hξ hξ1 L own other s then (1 : ℝ) else 0

def receipt (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (own other : ℕ) (i : Fin m) : ℝ :=
  listBids L i * (1 - ξ * acceptance ξ hξ hξ1 L other own i)

theorem acceptance_equal (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (r : ℕ) (i : Fin m) :
    acceptance ξ hξ hξ1 L r r i =
      EqualCapacity.positiveMarginal ξ r (listBids L) i := by
  simp only [acceptance, select, if_true]
  exact Hybrid.NativeEqual.sample_acceptance m ξ hξ hξ1 r L i

theorem acceptance_pure (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (own other : ℕ) (hne : own ≠ other) (i : Fin m) :
    acceptance ξ hξ hξ1 L own other i =
      if i ∈ (purePair (1 - ξ) L own other).1 then (1 : ℝ) else 0 := by
  simp only [acceptance, select, if_neg hne, integral_const,
    probReal_univ, smul_eq_mul, one_mul]

theorem select_optimal (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (own other : ℕ) (s : unitInterval) :
    Finite.Optimal own (receipt ξ hξ hξ1 L own other)
      (select ξ hξ hξ1 L own other s) := by
  classical
  by_cases he : own = other
  · subst other
    have hr : receipt ξ hξ hξ1 L own own =
        fun i => listBids L i * (1 - ξ * EqualCapacity.positiveMarginal ξ own (listBids L) i) := by
      funext i
      rw [receipt, acceptance_equal]
    rw [hr, select, if_pos rfl]
    exact Hybrid.NativeEqual.sample_optimal m ξ hξ hξ1 own L s
  · let P := purePair (1 - ξ) L own other
    have hf := (purePair_feasible (1 - ξ) L own other).1
    have hn := (purePair_nash (1 - ξ) L own other).1
    have hr : receipt ξ hξ hξ1 L own other =
        fun i => listBids L i * (1 - ξ * (if i ∈ P.2 then (1 : ℝ) else 0)) := by
      funext i
      rw [receipt, acceptance_pure ξ hξ hξ1 L other own (Ne.symm he),
        purePair_swap (1 - ξ) L own other he]
      rfl
    rw [hr, select, if_neg he]
    refine ⟨hf.1, ?_⟩
    intro S hS
    have hh := hn (S ∩ visible L)
      ⟨(Finset.card_le_card Finset.inter_subset_left).trans hS,
        fun i hi => (mem_visible L i).mp (Finset.mem_inter.mp hi).2⟩
    have hrev (U : Finset (Fin m)) :
        CompleteInformation.revenue (1 - ξ) (listBids L) U P.2 =
          ∑ i ∈ U, listBids L i * (1 - ξ * (if i ∈ P.2 then (1 : ℝ) else 0)) := by
      unfold CompleteInformation.revenue
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    have hzero (i : Fin m) (hi : i ∉ visible L) : listBids L i = 0 := by
      have hi' : L i = none := by simpa only [mem_visible, not_not] using hi
      simp [listBids, hi']
    have hsum :
        (∑ i ∈ S ∩ visible L,
          listBids L i * (1 - ξ * (if i ∈ P.2 then (1 : ℝ) else 0))) =
        ∑ i ∈ S, listBids L i * (1 - ξ * (if i ∈ P.2 then (1 : ℝ) else 0)) := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro i hi hni
      have hnot : i ∉ visible L := fun hv => hni (Finset.mem_inter.mpr ⟨hi, hv⟩)
      rw [hzero i hnot, zero_mul]
    change CompleteInformation.revenue (1 - ξ) (listBids L) (S ∩ visible L) P.2 ≤
      CompleteInformation.revenue (1 - ξ) (listBids L) P.1 P.2 at hh
    rw [hrev, hrev, hsum] at hh
    exact hh

theorem optimal_extend_capacity (V : Finset (Fin m)) (cap : ℕ)
    (r : Fin m → ℝ) (S : Finset (Fin m))
    (hz : ∀ i, i ∉ V → r i = 0)
    (hopt : Finite.Optimal (min V.card cap) r S) :
    Finite.Optimal cap r S := by
  classical
  refine ⟨hopt.1.trans (Nat.min_le_right _ _), ?_⟩
  intro T hT
  have hcard : (T ∩ V).card ≤ min V.card cap :=
    le_min (Finset.card_le_card Finset.inter_subset_right)
      ((Finset.card_le_card Finset.inter_subset_left).trans hT)
  have hh := hopt.2 (T ∩ V) hcard
  have he : (∑ i ∈ T ∩ V, r i) = ∑ i ∈ T, r i := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hni
    exact hz i (fun hv => hni (Finset.mem_inter.mpr ⟨hi, hv⟩))
  rwa [he] at hh

theorem select_optimal_clipped (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (own other : ℕ) (s : unitInterval) :
    Finite.Optimal own
      (receipt ξ hξ hξ1 L (min (visible L).card own) other)
      (select ξ hξ hξ1 L (min (visible L).card own) other s) := by
  apply optimal_extend_capacity (visible L) own _ _
  · intro i hi
    have hnone : L i = none := by simpa only [mem_visible, not_not] using hi
    simp [receipt, listBids, hnone]
  · exact select_optimal ξ hξ hξ1 L (min (visible L).card own) other s

theorem select_copy (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L L' : LocalList m) (own other own' other' : ℕ)
    (hL : L = L') (ho : own = own') (ht : other = other') (s : unitInterval) :
    select ξ hξ hξ1 L own other s = select ξ hξ hξ1 L' own' other' s := by
  subst L'
  subst own'
  subst other'
  rfl

end FCAppendix.AppendixRepair.GeneralLow.ExactLow
