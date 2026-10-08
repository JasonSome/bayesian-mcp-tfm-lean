import FCAppendix.Ample.VisibleContactLaw
import FCAppendix.Ample.CongestionRate

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology Real
open scoped BigOperators

variable {m n N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem focalCount_zero_iff (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (ω : Sample m n Seed) :
    (focalCount Γ i a ω).val = 0 ↔
      ∀ j ∈ firstK ω.2 a.routeCount, ¬ Accepts Γ i a.bid j ω.1 := by
  classical
  have hz : (focalCount Γ i a ω).val = 0 ↔
      ((focalCount Γ i a ω).val : ℝ) = 0 := by norm_cast
  rw [hz, focalCount_val_eq, Finset.sum_eq_zero_iff_of_nonneg]
  · simp only [Finset.mem_univ, true_implies]
    constructor
    · intro h j hj hacc
      have hh := h j
      simp [hj, hacc] at hh
    · intro h j
      by_cases hj : j ∈ firstK ω.2 a.routeCount
      · simp [hj, h j hj]
      · simp [hj]
  · intro j _
    positivity

theorem one_sub_success_eq_failure_integral (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) :
    1 - ((problem Γ i).outcome a).success =
      ∫ ω, (if (focalCount Γ i a ω).val = 0 then (1 : ℝ) else 0) ∂sampleLaw Γ := by
  classical
  have htest : (fun r : Fin (n + 1) => 1 - successIndicator r.val) =
      fun r => if r.val = 0 then (1 : ℝ) else 0 := by
    funext r
    by_cases hr : r.val = 0 <;> simp [successIndicator, hr]
  calc
    _ = ((problem Γ i).outcome a).expect (fun r => 1 - successIndicator r.val) := by
      rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
      rfl
    _ = _ := by rw [htest, problem_outcome, CountLaw.expect_ofMeasure]

theorem ppi_failure_eq_congestProb (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (a : JointAction n) (hb : 0 < a.bid) :
    1 - ((problem Γ i).outcome a).success =
      Ample.congestProb n N c a.routeCount (visibleClassMass Γ a.bid) := by
  classical
  let f : Sample (N + 1) n Seed → ℝ :=
    fun ω => if (focalCount Γ i a ω).val = 0 then 1 else 0
  have hi : Integrable f (sampleLaw Γ) :=
    CountLaw.integrable_comp _ _ (measurable_focalCount Γ i a)
      (fun r => if r.val = 0 then 1 else 0)
  rw [one_sub_success_eq_failure_integral]
  change (∫ ω, f ω ∂(backgroundLaw Γ).prod (permLaw n)) = _
  rw [integral_prod_symm f hi]
  have hin (τ : Equiv.Perm (Fin n)) :
      (∫ ω, f (ω, τ) ∂backgroundLaw Γ) =
        Ample.congestProb n N c a.routeCount (visibleClassMass Γ a.bid) := by
    have hmeas (K : Finset (Fin n)) : MeasurableSet
        {ω : Background (N + 1) n Seed | ∀ j ∈ K, ¬ Accepts Γ i a.bid j ω} := by
      induction K using Finset.induction_on with
      | empty => simp
      | @insert j K hj ih =>
        have he : {ω : Background (N + 1) n Seed | ∀ s ∈ insert j K, ¬ Accepts Γ i a.bid s ω} =
            {ω | ¬ Accepts Γ i a.bid j ω} ∩ {ω | ∀ s ∈ K, ¬ Accepts Γ i a.bid s ω} := by
          ext ω
          simp
        rw [he]
        exact (measurableSet_accepts Γ i a.bid j).compl.inter ih
    have hE := hmeas (firstK τ a.routeCount)
    calc
      _ = (backgroundLaw Γ).real {ω | ∀ j ∈ firstK τ a.routeCount,
          ¬ Accepts Γ i a.bid j ω} := by
        have he : f ∘ (fun ω => (ω, τ)) =
            fun ω => if ∀ j ∈ firstK τ a.routeCount, ¬ Accepts Γ i a.bid j ω
              then (1 : ℝ) else 0 := by
          funext ω
          simp only [f, Function.comp_apply, focalCount_zero_iff]
        change (∫ ω, (f ∘ (fun ω => (ω, τ))) ω ∂backgroundLaw Γ) = _
        rw [he]
        simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
          integral_indicator_one (μ := backgroundLaw Γ) hE
      _ = _ := by
        rw [ppi_joint_rejection_eq_congestProbAt Γ hA hatom hj i a.bid hb,
          Ample.congestProbAt_eq_congestProb, card_firstK _ _ a.routeCount_le]
  simp_rw [hin]
  simp

theorem ppi_joint_rejection_log_rate
    {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    {N C : ℕ → ℕ} {Seed : ℕ → Type*} [∀ a, MeasurableSpace (Seed a)]
    (Γ : ∀ a, FiniteGame (N a + 1) n (C a) (Seed a))
    (hA : ∀ a, (Γ a).A = Schedule.ppi n)
    (hatom : ∀ a, PositiveVisibleAtomless (Γ a))
    (hj : ∀ a j, ProposerRationalAtFeasibleLists (Γ a) j)
    (i : ∀ a, Fin (N a + 1)) (b : ℕ → ℝ)
    (hb : ∀ᶠ a in atTop, 0 < b a)
    (K : ℕ → Finset (Fin n)) (hK : ∀ a, (K a).card = k)
    {lawWeights : ℕ → ℝ} (hlam : Ample.ValidLaw n lawWeights)
    (hconv : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun a => visibleClassMass (Γ a) (b a) j) atTop (𝓝 (lawWeights j)))
    (hN : Tendsto (fun a => N a + 1) atTop atTop) {ρ : ℝ}
    (hc : Tendsto (fun a => (C a : ℝ) / (N a + 1)) atTop (𝓝 ρ))
    (hslack : Ample.contactMarginal n lawWeights < ρ)
    (htop : ∃ j ∈ Finset.Icc 1 n, 0 < lawWeights j ∧ (k : ℝ) * ρ < (min k j : ℕ)) :
    (∀ᶠ a in atTop, 0 < (backgroundLaw (Γ a)).real
      {ω | ∀ s ∈ K a, ¬ Accepts (Γ a) (i a) (b a) s ω}) ∧
    Tendsto (fun a => -log ((backgroundLaw (Γ a)).real
      {ω | ∀ s ∈ K a, ¬ Accepts (Γ a) (i a) (b a) s ω}) / (N a + 1)) atTop
        (𝓝 (Ample.rivalRate n ρ k lawWeights)) := by
  have hr := Ample.ample_event_rate hk1 hk
    (fun a => visibleClassMass_valid (Γ a) (b a)) hlam hconv hN (by simpa only [Nat.cast_add, Nat.cast_one] using hc) hslack htop
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hr
  have he : ∀ᶠ a in atTop,
      (backgroundLaw (Γ a)).real {ω | ∀ s ∈ K a, ¬ Accepts (Γ a) (i a) (b a) s ω} =
      Ample.congestProb n (N a) (C a) k (visibleClassMass (Γ a) (b a)) := by
    filter_upwards [hb] with a ha
    rw [ppi_joint_rejection_eq_congestProbAt (Γ a) (hA a) (hatom a) (hj a)
      (i a) (b a) ha, Ample.congestProbAt_eq_congestProb, hK a]
  refine ⟨?_, hr.2.congr' ?_⟩
  · filter_upwards [he, hr.1] with a he hp
    rwa [he]
  · filter_upwards [he] with a he
    rw [he]

theorem ppi_action_failure_log_rate
    {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    {N C : ℕ → ℕ} {Seed : ℕ → Type*} [∀ a, MeasurableSpace (Seed a)]
    (Γ : ∀ a, FiniteGame (N a + 1) n (C a) (Seed a))
    (hA : ∀ a, (Γ a).A = Schedule.ppi n)
    (hatom : ∀ a, PositiveVisibleAtomless (Γ a))
    (hj : ∀ a j, ProposerRationalAtFeasibleLists (Γ a) j)
    (i : ∀ a, Fin (N a + 1)) (act : ℕ → JointAction n)
    (hbid : ∀ᶠ a in atTop, 0 < (act a).bid)
    (hroute : ∀ᶠ a in atTop, (act a).routeCount = k)
    {lawWeights : ℕ → ℝ} (hlam : Ample.ValidLaw n lawWeights)
    (hconv : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun a => visibleClassMass (Γ a) (act a).bid j) atTop (𝓝 (lawWeights j)))
    (hN : Tendsto (fun a => N a + 1) atTop atTop) {ρ : ℝ}
    (hc : Tendsto (fun a => (C a : ℝ) / (N a + 1)) atTop (𝓝 ρ))
    (hslack : Ample.contactMarginal n lawWeights < ρ)
    (htop : ∃ j ∈ Finset.Icc 1 n, 0 < lawWeights j ∧ (k : ℝ) * ρ < (min k j : ℕ)) :
    (∀ᶠ a in atTop, 0 < 1 - (((problem (Γ a) (i a)).outcome (act a)).success)) ∧
    Tendsto (fun a => -log (1 - (((problem (Γ a) (i a)).outcome (act a)).success)) /
      (N a + 1)) atTop (𝓝 (Ample.rivalRate n ρ k lawWeights)) := by
  have hr := Ample.ample_event_rate hk1 hk
    (fun a => visibleClassMass_valid (Γ a) (act a).bid) hlam hconv hN (by simpa only [Nat.cast_add, Nat.cast_one] using hc) hslack htop
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hr
  have he : ∀ᶠ a in atTop,
      1 - (((problem (Γ a) (i a)).outcome (act a)).success) =
      Ample.congestProb n (N a) (C a) k (visibleClassMass (Γ a) (act a).bid) := by
    filter_upwards [hbid, hroute] with a hb hk'
    rw [ppi_failure_eq_congestProb (Γ a) (hA a) (hatom a) (hj a) (i a) (act a) hb, hk']
  refine ⟨?_, hr.2.congr' ?_⟩
  · filter_upwards [he, hr.1] with a he hp
    rwa [he]
  · filter_upwards [he] with a he
    rw [he]

end FCAppendix.Bayes
