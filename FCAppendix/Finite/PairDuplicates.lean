import FCAppendix.Finite.NonrareRanks

noncomputable section

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma permLaw_real_singleton (τ : Equiv.Perm (Fin n)) :
    (permLaw n).real {τ} = 1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  classical
  have h := permLaw_real_filter n (fun s => s = τ)
  have he : {s : Equiv.Perm (Fin n) | s = τ} = {τ} := by ext s; simp
  rw [he] at h
  simpa only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.card_singleton, Nat.cast_one] using h

lemma permLaw_real_singleton_pos (τ : Equiv.Perm (Fin n)) : 0 < (permLaw n).real {τ} := by
  rw [permLaw_real_singleton]
  positivity

lemma two_le_focalCount_of_pair (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n)
    (ω : Sample m n Seed) (j l : Fin n) (hjl : j ≠ l)
    (hj : j ∈ firstK ω.2 a.routeCount) (hl : l ∈ firstK ω.2 a.routeCount)
    (ha : Accepts Γ i a.bid j ω.1) (hb : Accepts Γ i a.bid l ω.1) :
    2 ≤ (focalCount Γ i a ω).val := by
  classical
  have haj := (mem_allocation_deviated_iff Γ i a ω j).mpr ⟨hj, ha⟩
  have hal := (mem_allocation_deviated_iff Γ i a ω l).mpr ⟨hl, hb⟩
  have hsub : {j, l} ⊆ accepted (deviated i a ω) Γ.policy ω.1.2 i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [accepted, haj, hal]
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_pair hjl] at hc
  exact hc

theorem pair_acceptance_mul_routing_le_duplicates (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) (j l : Fin n) (hjl : j ≠ l)
    (τ : Equiv.Perm (Fin n)) (hj : j ∈ firstK τ a.routeCount)
    (hl : l ∈ firstK τ a.routeCount) :
    (backgroundLaw Γ).real {ω | Accepts Γ i a.bid j ω ∧ Accepts Γ i a.bid l ω} *
        (permLaw n).real {τ} ≤ ((problem Γ i).outcome a).duplicates := by
  classical
  let E : Set (Background m n Seed) := {ω | Accepts Γ i a.bid j ω ∧ Accepts Γ i a.bid l ω}
  have hE : MeasurableSet E := (measurableSet_accepts Γ i a.bid j).inter
    (measurableSet_accepts Γ i a.bid l)
  have hprod : MeasurableSet (E ×ˢ {τ}) := hE.prod (MeasurableSet.of_discrete)
  rw [← measureReal_prod_prod E {τ}]
  change (sampleLaw Γ).real (E ×ˢ {τ}) ≤ _
  rw [← integral_indicator_one hprod, problem_outcome, CountLaw.duplicates_eq_expect,
    CountLaw.expect_ofMeasure]
  have hI := CountLaw.integrable_comp (sampleLaw Γ) (focalCount Γ i a)
    (measurable_focalCount Γ i a) (fun r : Fin (n + 1) => (r.val : ℝ) - successIndicator r.val)
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hprod) hI
  intro ω
  by_cases hω : ω ∈ E ×ˢ {τ}
  · rw [Set.indicator_of_mem hω]
    have hτ : ω.2 = τ := hω.2
    have hc := two_le_focalCount_of_pair Γ i a ω j l hjl
      (by rwa [hτ]) (by rwa [hτ]) hω.1.1 hω.1.2
    have hcr : (2 : ℝ) ≤ (focalCount Γ i a ω).val := by exact_mod_cast hc
    have hs := successIndicator_le_one (focalCount Γ i a ω).val
    linarith
  · rw [Set.indicator_of_notMem hω]
    exact sub_nonneg.mpr (successIndicator_le_count _)

theorem first_pair_acceptance_div_card_le_duplicates (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) (hk : 2 ≤ a.routeCount) :
    (backgroundLaw Γ).real {ω |
      Accepts Γ i a.bid (⟨0, by have := a.routeCount_le; omega⟩ : Fin n) ω ∧
      Accepts Γ i a.bid (⟨1, by have := a.routeCount_le; omega⟩ : Fin n) ω} /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ ((problem Γ i).outcome a).duplicates := by
  have hn := a.routeCount_le
  have h := pair_acceptance_mul_routing_le_duplicates Γ i a
    (⟨0, by have := a.routeCount_le; omega⟩ : Fin n) (⟨1, by have := a.routeCount_le; omega⟩ : Fin n) (by intro he; have := congrArg Fin.val he; norm_num at this)
    (Equiv.refl (Fin n)) (by simp [mem_firstK]; omega) (by simp [mem_firstK]; omega)
  simpa only [permLaw_real_singleton, div_eq_mul_inv, one_mul] using h

theorem eventually_nonrare_ppi_duplicates_pos
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (a : ℕ → JointAction n) (σ : ℕ → ℝ)
    (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hb : ∀ r, 0 < (a r).bid) (hk : ∀ r, 2 ≤ (a r).routeCount) (hσ : ∀ r, 0 < σ r)
    (hvar : ∀ r, (M r : ℝ) * alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) (a r).bid *
      (1 - alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) (a r).bid) = σ r ^ 2)
    (hσlim : Tendsto σ atTop atTop) {ρ : ℝ}
    (hp : Tendsto (fun r => alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) (a r).bid) atTop (𝓝 ρ))
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (ε : ℝ) (hε : 0 < ε)
    (hq : ∀ᶠ r in atTop, ε ≤ binomBelow (M r)
      (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) (a r).bid) (C r)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ r in atTop, d ≤ ((problem (Γ r) (i r)).outcome (a r)).duplicates := by
  let j : Fin 2 → Fin n := fun k => ⟨k.val, lt_of_lt_of_le k.isLt hn⟩
  obtain ⟨d, hd, hde⟩ := eventually_nonrare_ppi_pair_acceptance_pos M C Γ i j
    (fun r => (a r).bid) σ hA hatom (fun r k => hj r (j k)) hb hσ hvar hσlim hp hρ0 hρ1 ε hε hq
  refine ⟨d / (Fintype.card (Equiv.Perm (Fin n)) : ℝ), by positivity, ?_⟩
  filter_upwards [hde] with r hr
  have hdiv := div_le_div_of_nonneg_right hr (show (0 : ℝ) ≤ Fintype.card (Equiv.Perm (Fin n)) by positivity)
  exact hdiv.trans (first_pair_acceptance_div_card_le_duplicates (Γ r) (i r) (a r) (hk r))

theorem eventually_nonrare_ppi_duplicates_pos_general
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (a : ℕ → JointAction n)
    (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hb : ∀ r, 0 < (a r).bid) (hk : ∀ r, 2 ≤ (a r).routeCount)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (ε : ℝ) (hε : 0 < ε) (hq : ∀ᶠ r in atTop, ε ≤ binomBelow (M r)
      (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) (a r).bid) (C r)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ r in atTop, d ≤ ((problem (Γ r) (i r)).outcome (a r)).duplicates := by
  let j : Fin 2 → Fin n := fun k => ⟨k.val, lt_of_lt_of_le k.isLt hn⟩
  obtain ⟨d, hd, hde⟩ := eventually_nonrare_ppi_pair_pos M C Γ i j (fun r => (a r).bid)
    hA hatom (fun r k => hj r (j k)) hb hM hC hρ0 hρ1 hc ε hε hq
  refine ⟨d / (Fintype.card (Equiv.Perm (Fin n)) : ℝ), by positivity, ?_⟩
  filter_upwards [hde] with r hr
  have hdiv := div_le_div_of_nonneg_right hr (show (0 : ℝ) ≤ Fintype.card (Equiv.Perm (Fin n)) by positivity)
  exact hdiv.trans (first_pair_acceptance_div_card_le_duplicates (Γ r) (i r) (a r) (hk r))

theorem uniform_nonrare_ppi_duplicates_pos
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1))
    (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ r in atTop, ∀ a : JointAction n,
      0 < a.bid → 2 ≤ a.routeCount →
      ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) a.bid) (C r) →
      d ≤ ((problem (Γ r) (i r)).outcome a).duplicates := by
  classical
  by_contra hnot
  have hex : ∀ k : ℕ, ∃ r : ℕ, k ≤ r ∧ ∃ a : JointAction n,
      0 < a.bid ∧ 2 ≤ a.routeCount ∧
      ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) a.bid) (C r) ∧
      ((problem (Γ r) (i r)).outcome a).duplicates < 1 / ((k : ℝ) + 1) := by
    intro k
    have hbad : ¬ ∀ᶠ r in atTop, ∀ a : JointAction n,
        0 < a.bid → 2 ≤ a.routeCount →
        ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) a.bid) (C r) →
        1 / ((k : ℝ) + 1) ≤ ((problem (Γ r) (i r)).outcome a).duplicates := by
      intro hh
      exact hnot ⟨1 / ((k : ℝ) + 1), by positivity, hh⟩
    simp only [eventually_atTop] at hbad
    push Not at hbad
    exact hbad k
  choose f hf a hab hak haq had using hex
  have hft : Tendsto f atTop atTop := tendsto_atTop_mono hf tendsto_id
  obtain ⟨d, hd, hde⟩ := eventually_nonrare_ppi_duplicates_pos_general hn (M ∘ f) (C ∘ f)
    (fun r => Γ (f r)) (fun r => i (f r)) a (fun r => hA (f r)) (fun r => hatom (f r))
    (fun r => hj (f r)) hab hak (hM.comp hft) (fun r => hC (f r)) hρ0 hρ1 (hc.comp hft)
    ε hε (Filter.Eventually.of_forall haq)
  have hzero : Tendsto (fun r => ((problem (Γ (f r)) (i (f r))).outcome (a r)).duplicates)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun r => CountLaw.duplicates_nonneg _) (fun r => (had r).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hh : d ≤ 0 := ge_of_tendsto hzero hde
  linarith

end FCAppendix.Bayes
