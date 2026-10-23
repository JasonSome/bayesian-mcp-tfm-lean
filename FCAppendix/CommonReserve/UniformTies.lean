import FCAppendix.CommonReserve.Bayesian

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def eligible (L : LocalList m) (r : ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => L i ≠ none ∧ r ≤ Bayes.entryBid (L i))

def positiveEligible (L : LocalList m) (r : ℝ) : Finset (Fin m) := by
  classical
  exact (eligible L r).filter (fun i => 0 < Bayes.entryBid (L i))

def positiveList (L : LocalList m) (r : ℝ) : LocalList m := by
  classical
  exact fun i => if i ∈ positiveEligible L r then L i else none

def positiveSelection (L : LocalList m) (S : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact S.filter (fun i => 0 < Bayes.entryBid (L i))

def TopChoice (L : LocalList m) (r : ℝ) (c : ℕ) (S : Finset (Fin m)) : Prop :=
  S ⊆ positiveEligible L r ∧
    Finite.Optimal c (fun i => Bayes.entryBid (positiveList L r i)) S

def topChoices (L : LocalList m) (r : ℝ) (c : ℕ) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (TopChoice L r c)

structure UniformReserveRule (ν : Measure Seed) (policy : LocalPolicy m c Seed)
    (r : ℝ) : Prop where
  eligible : ∀ L : LocalList m, ∀ᵐ s ∂ν, (policy L s).val ⊆ eligible L r
  positive_law : ∀ (L : LocalList m) (S : Finset (Fin m)),
    (ν {s | positiveSelection L (policy L s).val = S}).toReal =
      if S ∈ topChoices L r c then 1 / ((topChoices L r c).card : ℝ) else 0
  zero_marginal_eq : ∀ (L : LocalList m) (i j : Fin m), L i = some 0 → L j = some 0 →
    ν.real {s | i ∈ (policy L s).val} = ν.real {s | j ∈ (policy L s).val}

@[simp] theorem mem_eligible_iff (L : LocalList m) (r : ℝ) (i : Fin m) :
    i ∈ eligible L r ↔ L i ≠ none ∧ r ≤ Bayes.entryBid (L i) := by
  classical
  simp [eligible]

@[simp] theorem mem_positiveEligible_iff (L : LocalList m) (r : ℝ) (i : Fin m) :
    i ∈ positiveEligible L r ↔
      L i ≠ none ∧ r ≤ Bayes.entryBid (L i) ∧ 0 < Bayes.entryBid (L i) := by
  classical
  simp [positiveEligible, and_assoc]

theorem positiveList_entry_of_mem (L : LocalList m) (r : ℝ) (i : Fin m)
    (hi : i ∈ positiveEligible L r) : positiveList L r i = L i := by
  simp [positiveList, hi]

theorem positiveList_entry_nonneg (L : LocalList m) (r : ℝ) (i : Fin m) :
    0 ≤ Bayes.entryBid (positiveList L r i) := by
  classical
  by_cases hi : i ∈ positiveEligible L r
  · rw [positiveList_entry_of_mem L r i hi]
    exact ((mem_positiveEligible_iff L r i).mp hi).2.2.le
  · simp [positiveList, hi, Bayes.entryBid]

theorem topChoices_nonempty (L : LocalList m) (r : ℝ) (c : ℕ) :
    (topChoices L r c).Nonempty := by
  classical
  refine ⟨HighestBid.selection (positiveList L r) c, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ?_⟩⟩
  refine ⟨?_, HighestBid.selection_optimal _ _⟩
  intro i hi
  have hp := (HighestBid.selection_best (positiveList L r) c).1.2 i hi
  by_contra h
  exact hp (by simp [positiveList, h])

theorem measurable_positiveSelection_joint :
    Measurable (fun p : LocalList m × Finset (Fin m) => positiveSelection p.1 p.2) := by
  classical
  apply measurable_to_countable'
  intro T
  have hm (i : Fin m) : MeasurableSet {p : LocalList m × Finset (Fin m) |
      i ∈ p.2 ∧ 0 < Bayes.entryBid (p.1 i)} :=
    (measurable_snd (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})).inter
      (measurableSet_lt measurable_const
        (Bayes.measurable_entryBid.comp ((measurable_pi_apply i).comp measurable_fst)))
  have he : (fun p : LocalList m × Finset (Fin m) => positiveSelection p.1 p.2) ⁻¹' {T} =
      ⋂ i : Fin m, if i ∈ T then {p | i ∈ p.2 ∧ 0 < Bayes.entryBid (p.1 i)}
        else {p | i ∈ p.2 ∧ 0 < Bayes.entryBid (p.1 i)}ᶜ := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, Finset.ext_iff, positiveSelection,
      Finset.mem_filter, mem_iInter]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ T <;> simp [hi]
  rw [he]
  exact MeasurableSet.iInter fun i => by
    by_cases hi : i ∈ T
    · simpa only [if_pos hi] using hm i
    · simpa only [if_neg hi] using (hm i).compl

theorem measurable_positiveSelection_policy (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val)) :
    Measurable (fun p : LocalList m × Seed => positiveSelection p.1 (policy p.1 p.2).val) :=
  measurable_positiveSelection_joint.comp (measurable_fst.prodMk hp)

theorem UniformReserveRule.ae_topChoice {ν : Measure Seed} [IsProbabilityMeasure ν]
    {policy : LocalPolicy m c Seed} {r : ℝ} (h : UniformReserveRule ν policy r)
    (L : LocalList m) : ∀ᵐ s ∂ν, TopChoice L r c (positiveSelection L (policy L s).val) := by
  classical
  have ha (S : Finset (Fin m)) : ∀ᵐ s ∂ν,
      positiveSelection L (policy L s).val = S → TopChoice L r c S := by
    by_cases hs : S ∈ topChoices L r c
    · exact Filter.Eventually.of_forall fun _ _ => (Finset.mem_filter.mp hs).2
    · have hz : ν {s | positiveSelection L (policy L s).val = S} = 0 := by
        have hr := h.positive_law L S
        rw [if_neg hs] at hr
        exact ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right (measure_ne_top _ _)
      have hh : ∀ᵐ s ∂ν, positiveSelection L (policy L s).val ≠ S := by
        rw [ae_iff]
        simpa using hz
      exact hh.mono fun _ ht he => (ht he).elim
  filter_upwards [ae_all_iff.mpr ha] with s hs
  exact hs _ rfl

theorem TopChoice.included_of_few_competitors {L : LocalList m} {r : ℝ}
    {S : Finset (Fin m)} (hS : TopChoice L r c S) (i : Fin m)
    (hi : i ∈ positiveEligible L r)
    (hc : (Finset.univ.filter (fun j => j ≠ i ∧
      Bayes.entryBid (positiveList L r i) ≤ Bayes.entryBid (positiveList L r j))).card < c) :
    i ∈ S := by
  apply Finite.included_of_few_competitors c _ S hS.2 i _ hc
  rw [positiveList_entry_of_mem L r i hi]
  exact ((mem_positiveEligible_iff L r i).mp hi).2.2

theorem positiveList_entry_eq {L : LocalList m} {r : ℝ} (hr : 0 ≤ r)
    (hL : ∀ i b, L i = some b → r ≤ b) (i : Fin m) :
    Bayes.entryBid (positiveList L r i) = Bayes.entryBid (L i) := by
  classical
  cases he : L i with
  | none => simp [positiveList, positiveEligible, eligible, he, Bayes.entryBid]
  | some b =>
    have hb := hL i b he
    by_cases hp : 0 < b
    · simp [positiveList, positiveEligible, eligible, he, Bayes.entryBid, hb, hp]
    · have hz : b = 0 := le_antisymm (le_of_not_gt hp) (hr.trans hb)
      simp [positiveList, positiveEligible, eligible, he, Bayes.entryBid, hz]

theorem optimal_of_positiveChoice {L : LocalList m} {r : ℝ} {S : Finset (Fin m)}
    (hr : 0 ≤ r) (hL : ∀ i b, L i = some b → r ≤ b)
    (hcap : S.card ≤ c) (hS : TopChoice L r c (positiveSelection L S)) :
    Finite.Optimal c (fun i => Bayes.entryBid (L i)) S := by
  classical
  have he : (∑ i ∈ positiveSelection L S, Bayes.entryBid (L i)) =
      ∑ i ∈ S, Bayes.entryBid (L i) := by
    simp only [positiveSelection, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : 0 < Bayes.entryBid (L i)
    · simp [hp]
    · have hz : Bayes.entryBid (L i) = 0 := by
        have hnon := positiveList_entry_nonneg L r i
        rw [positiveList_entry_eq hr hL i] at hnon
        exact le_antisymm (le_of_not_gt hp) hnon
      simp [hz]
  refine ⟨hcap, fun T hT => ?_⟩
  have hh := hS.2.2 T hT
  simpa only [positiveList_entry_eq hr hL, he] using hh

theorem UniformReserveRule.ae_optimal {ν : Measure Seed} [IsProbabilityMeasure ν]
    {policy : LocalPolicy m c Seed} {r : ℝ} (h : UniformReserveRule ν policy r)
    (hr : 0 ≤ r) (L : LocalList m) (hL : ∀ i b, L i = some b → r ≤ b) :
    ∀ᵐ s ∂ν, Finite.Optimal c (fun i => Bayes.entryBid (L i)) (policy L s).val :=
  (h.ae_topChoice L).mono fun s hs =>
    optimal_of_positiveChoice hr hL (policy L s).property.1 hs

end FCAppendix.CommonReserve
