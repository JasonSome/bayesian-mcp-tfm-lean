import FCAppendix.Affine.FiniteSelector

noncomputable section
namespace FCAppendix.Affine.LowBody.CompleteInformation
open MeasureTheory Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def revenue (κ : ℝ) (b : ι → ℝ) (own other : Finset ι) : ℝ :=
  ∑ i ∈ own, (if i ∈ other then κ * b i else b i)

def potential (κ : ℝ) (b : ι → ℝ) (S T : Finset ι) : ℝ :=
  (∑ i ∈ S ∪ T, b i) + κ * ∑ i ∈ S ∩ T, b i

omit [Fintype ι] in
theorem potential_comm (κ : ℝ) (b : ι → ℝ) (S T : Finset ι) :
    potential κ b S T = potential κ b T S := by
  simp [potential, Finset.union_comm, Finset.inter_comm]

theorem potential_eq_revenue_add (κ : ℝ) (b : ι → ℝ) (S T : Finset ι) :
    potential κ b S T = revenue κ b S T + ∑ i ∈ T, b i := by
  classical
  have hs : ∀ (U : Finset ι) (f : ι → ℝ),
      (∑ i ∈ U, f i) = ∑ i : ι, if i ∈ U then f i else 0 := by
    intro U f
    simp
  dsimp [potential, revenue]
  rw [hs (S ∪ T), hs (S ∩ T), hs S, hs T]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]
  ring

theorem unilateral_difference (κ : ℝ) (b : ι → ℝ) (S S' T : Finset ι) :
    potential κ b S T - potential κ b S' T =
      revenue κ b S T - revenue κ b S' T := by
  rw [potential_eq_revenue_add, potential_eq_revenue_add]
  ring

abbrev Choice (r : ℕ) := {S : Finset ι // S.card = r}

omit [DecidableEq ι] in
theorem choice_nonempty (r : ℕ) (hr : r ≤ Fintype.card ι) :
    Nonempty (Choice (ι := ι) r) := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (by simpa using hr)
  exact ⟨⟨S, hS⟩⟩

def selector (r₁ r₂ : ℕ) (hr₁ : r₁ ≤ Fintype.card ι) (hr₂ : r₂ ≤ Fintype.card ι)
    (κ : ℝ) (b : ι → ℝ) : Choice (ι := ι) r₁ × Choice (ι := ι) r₂ := by
  letI : Nonempty (Choice (ι := ι) r₁) := choice_nonempty r₁ hr₁
  letI : Nonempty (Choice (ι := ι) r₂) := choice_nonempty r₂ hr₂
  exact FCAppendix.Affine.FiniteSelector.select (fun p => potential κ b p.1.1 p.2.1)

theorem selector_nash (r₁ r₂ : ℕ)
    (hr₁ : r₁ ≤ Fintype.card ι) (hr₂ : r₂ ≤ Fintype.card ι)
    (κ : ℝ) (b : ι → ℝ) :
    (∀ S : Choice (ι := ι) r₁, revenue κ b S.1 (selector r₁ r₂ hr₁ hr₂ κ b).2.1 ≤
      revenue κ b (selector r₁ r₂ hr₁ hr₂ κ b).1.1 (selector r₁ r₂ hr₁ hr₂ κ b).2.1) ∧
    (∀ T : Choice (ι := ι) r₂, revenue κ b T.1 (selector r₁ r₂ hr₁ hr₂ κ b).1.1 ≤
      revenue κ b (selector r₁ r₂ hr₁ hr₂ κ b).2.1 (selector r₁ r₂ hr₁ hr₂ κ b).1.1) := by
  letI : Nonempty (Choice (ι := ι) r₁) := choice_nonempty r₁ hr₁
  letI : Nonempty (Choice (ι := ι) r₂) := choice_nonempty r₂ hr₂
  let p := selector r₁ r₂ hr₁ hr₂ κ b
  have hmax : ∀ q : Choice (ι := ι) r₁ × Choice (ι := ι) r₂,
      potential κ b q.1.1 q.2.1 ≤ potential κ b p.1.1 p.2.1 := by
    intro q
    exact FCAppendix.Affine.FiniteSelector.select_max
      (fun q : Choice (ι := ι) r₁ × Choice (ι := ι) r₂ => potential κ b q.1.1 q.2.1) q
  constructor
  · intro S
    have h := hmax (S, p.2)
    rw [potential_eq_revenue_add, potential_eq_revenue_add] at h
    exact le_of_add_le_add_right h
  · intro T
    have h := hmax (p.1, T)
    rw [potential_comm κ b p.1.1 T.1, potential_comm κ b p.1.1 p.2.1,
      potential_eq_revenue_add, potential_eq_revenue_add] at h
    exact le_of_add_le_add_right h

theorem extend_selection (S : Finset ι) (r : ℕ)
    (hSr : S.card ≤ r) (hr : r ≤ Fintype.card ι) :
    ∃ T : Choice (ι := ι) r, S ⊆ T.1 := by
  classical
  have hd : r - S.card ≤ ((Finset.univ : Finset ι) \ S).card := by
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ]
    simp only [Finset.card_univ]
    omega
  obtain ⟨U, hU, hcard⟩ := Finset.exists_subset_card_eq hd
  have hdis : Disjoint S U := Finset.disjoint_left.mpr fun i hiS hiU =>
    (Finset.mem_sdiff.mp (hU hiU)).2 hiS
  refine ⟨⟨S ∪ U, ?_⟩, Finset.subset_union_left⟩
  rw [Finset.card_union_of_disjoint hdis, hcard]
  omega

omit [Fintype ι] in

theorem revenue_mono_selection (κ : ℝ) (hκ : 0 ≤ κ) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (S S' T : Finset ι) (hSS' : S ⊆ S') :
    revenue κ b S T ≤ revenue κ b S' T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hSS'
  intro i _ _
  split
  · exact mul_nonneg hκ (hb i)
  · exact hb i

theorem selector_nash_all_feasible (r₁ r₂ : ℕ)
    (hr₁ : r₁ ≤ Fintype.card ι) (hr₂ : r₂ ≤ Fintype.card ι)
    (κ : ℝ) (hκ : 0 ≤ κ) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    (∀ S : Finset ι, S.card ≤ r₁ →
      revenue κ b S (selector r₁ r₂ hr₁ hr₂ κ b).2.1 ≤
        revenue κ b (selector r₁ r₂ hr₁ hr₂ κ b).1.1
          (selector r₁ r₂ hr₁ hr₂ κ b).2.1) ∧
    (∀ T : Finset ι, T.card ≤ r₂ →
      revenue κ b T (selector r₁ r₂ hr₁ hr₂ κ b).1.1 ≤
        revenue κ b (selector r₁ r₂ hr₁ hr₂ κ b).2.1
          (selector r₁ r₂ hr₁ hr₂ κ b).1.1) := by
  obtain ⟨h₁, h₂⟩ := selector_nash r₁ r₂ hr₁ hr₂ κ b
  constructor
  · intro S hS
    obtain ⟨S', hSS'⟩ := extend_selection S r₁ hS hr₁
    exact (revenue_mono_selection κ hκ b hb S S'.1 _ hSS').trans (h₁ S')
  · intro T hT
    obtain ⟨T', hTT'⟩ := extend_selection T r₂ hT hr₂
    exact (revenue_mono_selection κ hκ b hb T T'.1 _ hTT').trans (h₂ T')

theorem measurable_selector [MeasurableSpace (Finset ι)]
    [MeasurableSingletonClass (Finset ι)] (r₁ r₂ : ℕ)
    (hr₁ : r₁ ≤ Fintype.card ι) (hr₂ : r₂ ≤ Fintype.card ι) :
    Measurable (fun p : ℝ × (ι → ℝ) => selector r₁ r₂ hr₁ hr₂ p.1 p.2) := by
  letI : Nonempty (Choice (ι := ι) r₁) := choice_nonempty r₁ hr₁
  letI : Nonempty (Choice (ι := ι) r₂) := choice_nonempty r₂ hr₂
  apply FCAppendix.Affine.FiniteSelector.measurable_select
  intro q
  dsimp [potential]
  exact ((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd)).add
    (measurable_fst.mul
      (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd))

theorem potential_prefix_formula (L R z : ℕ) (κ : ℝ) (b : Fin L → ℝ)
    (S T : Finset (Fin L))
    (hu : S ∪ T = Finset.univ.filter (fun i => i.val < R - z))
    (hi : S ∩ T = Finset.univ.filter (fun i => i.val < z)) :
    potential κ b S T =
      (∑ i : Fin L, if i.val < R - z then b i else 0) +
        κ * ∑ i : Fin L, if i.val < z then b i else 0 := by
  simp only [potential, hu, hi, Finset.sum_filter]
end FCAppendix.Affine.LowBody.CompleteInformation
