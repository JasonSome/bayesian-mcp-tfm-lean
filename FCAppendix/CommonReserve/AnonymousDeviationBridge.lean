import FCAppendix.CommonReserve.AnonymousRoutedSource

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem routed_outcome_expect_eq_inputs (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (a : JointAction n) (τ : Equiv.Perm (Fin n)) (f : Fin (n + 1) → ℝ) :
    ((routedSource Γ r hr).outcome i (routedAction r ((0, a), τ))).expect f =
      ∫ d : Fin m → Bayes.UserDraw n,
        ∫ s, f (Bayes.focalCount Γ i a ((d, s), τ))
          ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)
        ∂(Measure.pi fun _ : Fin m => Bayes.userLaw Γ) := by
  let Γ' := routedSource Γ r hr
  let b := routedAction r ((0, a), τ)
  have hp := routedSample_measurePreserving Γ r hr
  have hK : Measurable (fun ω : Bayes.Background m n Seed =>
      Γ'.focalCount i b (routedSample r ω)) :=
    (Γ'.measurable_focalCount i b).comp hp.measurable
  have hmap : (∫ ω, f (Γ'.focalCount i b ω)
        ∂(Bayes.backgroundLaw Γ).map (routedSample r)) =
      ∫ ω, f (Γ'.focalCount i b (routedSample r ω)) ∂Bayes.backgroundLaw Γ :=
    integral_map_of_stronglyMeasurable hp.measurable
      ((measurable_of_countable f).comp (Γ'.measurable_focalCount i b)).stronglyMeasurable
  rw [Γ'.outcome_expect, ← hp.map_eq]
  change (∫ ω, f (Γ'.focalCount i b ω)
    ∂(Bayes.backgroundLaw Γ).map (routedSample r)) = _
  rw [hmap]
  rw [show Bayes.backgroundLaw Γ =
      (Measure.pi fun _ : Fin m => Bayes.userLaw Γ).prod
        (Measure.pi fun _ : Fin n => Γ.seedLaw) from rfl,
    integral_prod _ (CountLaw.integrable_comp _ _ hK f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun d => integral_routed_focalCount_seed Γ r hr hT d i a τ f

theorem anonymous_outcome_expect_eq_routed (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (a : JointAction n) (f : Fin (n + 1) → ℝ) :
    ((Bayes.problem Γ i).outcome a).expect f =
      ∫ τ, ((routedSource Γ r hr).outcome i (routedAction r ((0, a), τ))).expect f
        ∂permLaw n := by
  let H := fun x : (Fin m → Bayes.UserDraw n) × Equiv.Perm (Fin n) =>
    ∫ s, f (Bayes.focalCount Γ i a ((x.1, s), x.2))
      ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)
  have hH : Integrable H
      ((Measure.pi fun _ : Fin m => Bayes.userLaw Γ).prod (permLaw n)) := by
    apply Integrable.of_bound
      (Bayes.measurable_integral_focalCount_inputs Γ i a f).aestronglyMeasurable
      (∑ k, ‖f k‖)
    apply Eventually.of_forall
    intro x
    have hm : Measurable (fun s : Fin n → Seed => Bayes.focalCount Γ i a ((x.1, s), x.2)) :=
      (Bayes.measurable_focalCount Γ i a).comp
        ((measurable_const.prodMk measurable_id).prodMk measurable_const)
    change ‖∫ s, f (Bayes.focalCount Γ i a ((x.1, s), x.2))
      ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)‖ ≤ _
    rw [← CountLaw.expect_ofMeasure _ _ hm]
    exact (CountLaw.ofMeasure _ _ hm).norm_expect_le_sum_norm f
  rw [Bayes.problem_outcome, CountLaw.expect_ofMeasure,
    Bayes.integral_focalCount_eq_inputs]
  change (∫ x, H x ∂((Measure.pi fun _ : Fin m => Bayes.userLaw Γ).prod (permLaw n))) = _
  rw [integral_prod_symm _ hH]
  apply integral_congr_ae
  exact Eventually.of_forall fun τ => (routed_outcome_expect_eq_inputs Γ r hr hT i a τ f).symm

theorem routedAction_singleton (r b : ℝ) (hb : r ≤ b)
    (a : JointAction n) (ha : a.bid = b) (hk : a.routeCount = 1)
    (τ : Equiv.Perm (Fin n)) (hn : 0 < n) :
    routedAction r ((0, a), τ) = singleton (τ.symm ⟨0, hn⟩) b hb := by
  classical
  apply Subtype.ext
  funext j
  have he : j ∈ firstK τ 1 ↔ j = τ.symm ⟨0, hn⟩ := by
    simp only [mem_firstK]
    constructor
    · intro h
      have hz : τ j = (⟨0, hn⟩ : Fin n) := Fin.ext (by simpa using Nat.lt_one_iff.mp h)
      simpa using congrArg τ.symm hz
    · intro h
      subst j
      simp
  simp [routedAction, singleton, ha, hk, hb, he]

theorem anonymous_singleton_success_lower (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (hn : 0 < n) (i : Fin m) (b ε : ℝ) (hb : r ≤ b)
    (hS : ∀ j : Fin n,
      1 - ε ≤ ((routedSource Γ r hr).outcome i (singleton j b hb)).success) :
    1 - ε ≤ ((Bayes.problem Γ i).outcome
      (⟨b, hr.trans hb, 1, hn⟩ : JointAction n)).success := by
  let a : JointAction n := ⟨b, hr.trans hb, 1, hn⟩
  have he := anonymous_outcome_expect_eq_routed Γ r hr hT i a
    (fun k => successIndicator k.val)
  change ((Bayes.problem Γ i).outcome a).success =
    ∫ τ, ((routedSource Γ r hr).outcome i (routedAction r ((0, a), τ))).success ∂permLaw n at he
  rw [he]
  have hm : Measurable (fun τ : Equiv.Perm (Fin n) =>
      ((routedSource Γ r hr).outcome i (routedAction r ((0, a), τ))).success) :=
    measurable_of_countable _
  have hi : Integrable (fun τ : Equiv.Perm (Fin n) =>
      ((routedSource Γ r hr).outcome i (routedAction r ((0, a), τ))).success) (permLaw n) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall fun τ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CountLaw.success_nonneg _)]
      exact CountLaw.success_le_one _
  have hh := integral_mono (integrable_const (1 - ε)) hi (fun τ => by
    rw [routedAction_singleton r b hb a rfl rfl τ hn]
    exact hS _)
  simpa only [integral_const, probReal_univ, one_smul] using hh

end FCAppendix.CommonReserve
