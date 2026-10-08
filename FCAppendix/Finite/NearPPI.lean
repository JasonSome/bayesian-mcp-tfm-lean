import FCAppendix.Finite.NearPPIUtility
import FCAppendix.Finite.IdentitySymmetry
import FCAppendix.Finite.PPIBidConvergence
import FCAppendix.Finite.BelowCutoffCounts

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure CongestedAssumptions
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) (g ρ vstar : ℝ) : Prop where
  proposers_two : 2 ≤ n
  capacity_lt_population : ∀ k, C k < M k
  common_values : ∀ k, (Γ k).F = F
  common_fee : ∀ k, (Γ k).g = g
  ratio_pos : 0 < ρ
  ratio_lt_one : ρ < 1
  population_grows : Tendsto M atTop atTop
  capacity_ratio : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)
  equilibria : ∀ k, IsAEEquilibrium (Γ k)
  feasible_continuations : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j
  visible_atomless : ∀ k, PositiveVisibleAtomless (Γ k)
  policy_symmetry : ∀ k, PolicyLawEquivariant (Γ k)
  scarcity : (n : ℝ) * ρ < F.real (Ioi g)
  efficient_cutoff : F.real (Ioi vstar) = (n : ℝ) * ρ
  local_density : ∃ (f : ℝ → ℝ) (U : Set ℝ), Measurable f ∧ MeasurableSet U ∧ U ∈ 𝓝 vstar ∧
    F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U ∧
    ContinuousAt f vstar ∧ 0 < f vstar

structure NearPPIAssumptions
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) (g : ℝ) (a : ℕ → ℝ) (ρ vstar : ℝ) : Prop
    extends CongestedAssumptions M C Γ F g ρ vstar where
  coefficient_limit : Tendsto a atTop (𝓝 1)
  receipt_lower : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r

namespace NearPPIAssumptions

variable {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
  {g : ℝ} {a : ℕ → ℝ} {ρ vstar : ℝ}

omit [NullSingletonClass F] in
theorem cutoff_mass (h : NearPPIAssumptions M C Γ F g a ρ vstar) :
    (∀ v < vstar, 0 < F.real (Ioo v vstar)) ∧
      (∀ v > vstar, 0 < F.real (Ioo vstar v)) := by
  obtain ⟨f, U, hf, hU, hUn, hF, hc, hpos⟩ := h.local_density
  exact cutoff_interval_mass_of_local_density F f hf vstar U hU hUn hF hc hpos

omit [NullSingletonClass F] in
theorem price_pos (h : NearPPIAssumptions M C Γ F g a ρ vstar) : 0 < vstar - g :=
  sub_pos.mpr (cutoff_gt_fee_of_scarcity F g vstar _ h.efficient_cutoff h.scarcity)

theorem utility_limit (h : NearPPIAssumptions M C Γ F g a ρ vstar)
    (i : ∀ k, Fin (M k)) (v : ℝ) :
    Tendsto (fun k => (problem (Γ k) (i k)).envelope v) atTop (𝓝 (max (v - vstar) 0)) := by
  let j : Fin n := ⟨0, by have hh := h.proposers_two; omega⟩
  have hU := nearPPI_typeUtility_limit M C Γ j F h.common_values g h.common_fee a ρ vstar
    h.ratio_pos h.ratio_lt_one h.population_grows h.capacity_ratio h.coefficient_limit
    h.equilibria h.feasible_continuations h.visible_atomless h.receipt_lower h.scarcity
    h.efficient_cutoff h.cutoff_mass.1 h.cutoff_mass.2 v
  exact envelope_tendsto_of_typeUtility M C Γ h.policy_symmetry i v _ hU

theorem utility_uniformOn_compact (h : NearPPIAssumptions M C Γ F g a ρ vstar)
    (i : ∀ k, Fin (M k)) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun k v => (problem (Γ k) (i k)).envelope v)
      (fun v => max (v - vstar) 0) atTop K :=
  NearPPI.uniformOn_compact_of_lipschitz 1
    (fun k => (problem (Γ k) (i k)).envelope_lipschitzWith) (h.utility_limit i) hK

theorem above_cutoff (h : NearPPIAssumptions M C Γ F g a ρ vstar)
    (i : ∀ k, Fin (M k)) (v : ℝ) (hv : vstar < v) :
    ∀ η > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act →
      |((problem (Γ k) (i k)).outcome act).success - 1| < η ∧
      |act.bid - (vstar - g)| < η ∧ ((problem (Γ k) (i k)).outcome act).duplicates < η ∧
      |((problem (Γ k) (i k)).outcome act).load - 1| < η ∧
      ((problem (Γ k) (i k)).outcome act).prob (fun r => r.val ≠ 1) < η := by
  apply all_bestResponses_bid_and_count_converge M C Γ
    (by have hh := h.proposers_two; omega) i a v g (vstar - g) h.price_pos (by linarith)
    h.common_fee h.receipt_lower h.coefficient_limit
  intro w
  have he : w - g - (vstar - g) = w - vstar := by ring
  simpa only [he] using h.utility_limit i w

theorem below_cutoff (h : NearPPIAssumptions M C Γ F g a ρ vstar)
    (i : ∀ k, Fin (M k)) (v : ℝ) (hv : v < vstar) :
    ∀ η > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act →
      ((problem (Γ k) (i k)).outcome act).success < η ∧
      ((problem (Γ k) (i k)).outcome act).load < η ∧
      ((problem (Γ k) (i k)).outcome act).duplicates < η ∧
      ((problem (Γ k) (i k)).outcome act).prob (fun r => r.val ≠ 0) < η := by
  apply Interim.Problem.all_bestResponses_count_zero_converge
    (fun k => problem (Γ k) (i k)) v g (vstar - g) (by linarith)
  intro w
  have he : w - g - (vstar - g) = w - vstar := by ring
  simpa only [he] using h.utility_limit i w

theorem aggregates (h : NearPPIAssumptions M C Γ F g a ρ vstar) :
    Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 ((n : ℝ) * ρ)) ∧
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 ((n : ℝ) * ρ)) ∧
    Tendsto (fun k => finiteLoad (Γ k) - finiteCoverage (Γ k)) atTop (𝓝 0) ∧
    Tendsto (fun k => finiteMultiplicity (Γ k)) atTop (𝓝 1) := by
  let j : Fin n := ⟨0, by have hh := h.proposers_two; omega⟩
  have hh := nearPPI_aggregate_limits M C Γ j F h.common_values g h.common_fee a ρ
    h.ratio_pos h.ratio_lt_one h.population_grows h.capacity_ratio h.coefficient_limit
    h.equilibria h.feasible_continuations h.visible_atomless h.receipt_lower h.scarcity
  have hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 ((n : ℝ) * ρ)) :=
    ((show Continuous (fun z : ℝ × (ℝ × ℝ) => z.1) by fun_prop).tendsto _).comp hh
  have hL : Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 ((n : ℝ) * ρ)) :=
    ((show Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.2) by fun_prop).tendsto _).comp hh
  have hD : Tendsto (fun k => finiteLoad (Γ k) - finiteCoverage (Γ k)) atTop (𝓝 0) :=
    ((show Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) by fun_prop).tendsto _).comp hh
  refine ⟨hQ, hL, hD, ?_⟩
  exact NearPPI.multiplicity_limit (mul_pos (Nat.cast_pos.mpr (by have hh := h.proposers_two; omega))
    h.ratio_pos).ne' hQ hL

end NearPPIAssumptions
end FCAppendix.Bayes
