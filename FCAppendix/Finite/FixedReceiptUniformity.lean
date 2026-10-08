import FCAppendix.Finite.GeneralReceiptCapacity

namespace FCAppendix

open Filter Set Topology

theorem eventually_forall_of_cofinal_selections
    {I : ℕ → Type*} {P : ∀ k, I k → Prop}
    (h : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ z : ∀ k, I (φ k),
      ∀ᶠ k in atTop, P (φ k) (z k)) :
    ∀ᶠ k in atTop, ∀ z : I k, P k z := by
  classical
  by_contra hnot
  have hbad : ∀ N : ℕ, ∃ k, N ≤ k ∧ ∃ z : I k, ¬ P k z := by
    intro N
    by_contra hN
    apply hnot
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro k hk z
    by_contra hz
    exact hN ⟨k, hk, z, hz⟩
  choose φ hφ z hz using hbad
  have hcofinal : Tendsto φ atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hk.trans (hφ k)
  obtain ⟨k, hk⟩ := (h φ hcofinal z).exists
  exact hz k hk

namespace Bayes

open MeasureTheory ProbabilityTheory Game

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure FixedReceiptFamilyAssumptions
    (M C : ℕ → ℕ) (I : ℕ → Type*)
    (Γ : ∀ k, I k → FiniteGame (M k) n (C k) Seed)
    (B : ∀ k z, PosteriorSystem (Γ k z)) (F : Measure ℝ) (g a ρ : ℝ) : Prop where
  proposers_pos : 0 < n
  common_values : ∀ k z, (Γ k z).F = F
  common_fee : ∀ k z, (Γ k z).g = g
  factor_pos : 0 < a
  ratio_pos : 0 < ρ
  ratio_lt_one : ρ < 1
  population_grows : Tendsto M atTop atTop
  capacity_ratio : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)
  users : ∀ k z, UsersOptimal (Γ k z)
  bayes_receipts : ∀ k z, BayesReceiptOptimalOnPath (Γ k z) (B k z)
  feasible_continuations : ∀ k z j, ProposerRationalAtFeasibleLists (Γ k z) j
  visible_atomless : ∀ k z, PositiveVisibleAtomless (Γ k z)
  receipt_lower : ∀ k z r, 0 < r → r ≤ n → a * (r : ℝ) ≤ (Γ k z).A.charge r
  scarcity : (n : ℝ) * ρ < F.real (Ioi g)

namespace FixedReceiptFamilyAssumptions

variable {M C : ℕ → ℕ} {I : ℕ → Type*}
  {Γ : ∀ k, I k → FiniteGame (M k) n (C k) Seed}
  {B : ∀ k z, PosteriorSystem (Γ k z)} {F : Measure ℝ} {g a ρ : ℝ}

theorem select (h : FixedReceiptFamilyAssumptions M C I Γ B F g a ρ)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (z : ∀ k, I (φ k)) :
    FixedReceiptAssumptions (M ∘ φ) (C ∘ φ) (fun k => Γ (φ k) (z k))
      (fun k => B (φ k) (z k)) F g a ρ where
  proposers_pos := h.proposers_pos
  common_values := fun k => h.common_values (φ k) (z k)
  common_fee := fun k => h.common_fee (φ k) (z k)
  factor_pos := h.factor_pos
  ratio_pos := h.ratio_pos
  ratio_lt_one := h.ratio_lt_one
  population_grows := h.population_grows.comp hφ
  capacity_ratio := h.capacity_ratio.comp hφ
  users := fun k => h.users (φ k) (z k)
  bayes_receipts := fun k => h.bayes_receipts (φ k) (z k)
  feasible_continuations := fun k => h.feasible_continuations (φ k) (z k)
  visible_atomless := fun k => h.visible_atomless (φ k) (z k)
  receipt_lower := fun k => h.receipt_lower (φ k) (z k)
  scarcity := h.scarcity

variable [IsProbabilityMeasure F]

theorem uniform_coverage (h : FixedReceiptFamilyAssumptions M C I Γ B F g a ρ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ z : I k, (n : ℝ) * ρ * a ^ 2 - δ < finiteCoverage (Γ k z) := by
  apply eventually_forall_of_cofinal_selections
  intro φ hφ z
  exact (h.select φ hφ z).eventually_coverage_lower δ hδ

theorem uniform_load (h : FixedReceiptFamilyAssumptions M C I Γ B F g a ρ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ z : I k, |finiteLoad (Γ k z) - (n : ℝ) * ρ| < δ := by
  apply eventually_forall_of_cofinal_selections
  intro φ hφ z
  have hl := (h.select φ hφ z).load_tendsto_capacity
  filter_upwards [(tendsto_order.mp hl).1 ((n : ℝ) * ρ - δ) (by linarith),
    (tendsto_order.mp hl).2 ((n : ℝ) * ρ + δ) (by linarith)] with k hlo hhi
  dsimp only [Function.comp_def] at hlo hhi ⊢
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem uniform_duplicates (h : FixedReceiptFamilyAssumptions M C I Γ B F g a ρ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ z : I k, finiteLoad (Γ k z) - finiteCoverage (Γ k z) <
      (n : ℝ) * ρ * (1 - a ^ 2) + δ := by
  apply eventually_forall_of_cofinal_selections
  intro φ hφ z
  exact (h.select φ hφ z).eventually_duplicates_upper δ hδ

theorem uniform_multiplicity (h : FixedReceiptFamilyAssumptions M C I Γ B F g a ρ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ z : I k, finiteMultiplicity (Γ k z) <
      min (n : ℝ) ((a ^ 2)⁻¹) + δ := by
  apply eventually_forall_of_cofinal_selections
  intro φ hφ z
  exact (h.select φ hφ z).eventually_multiplicity_upper δ hδ

theorem uniform_all (h : FixedReceiptFamilyAssumptions M C I Γ B F g a ρ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ z : I k,
      |finiteLoad (Γ k z) - (n : ℝ) * ρ| < δ ∧
      (n : ℝ) * ρ * a ^ 2 - δ < finiteCoverage (Γ k z) ∧
      finiteLoad (Γ k z) - finiteCoverage (Γ k z) < (n : ℝ) * ρ * (1 - a ^ 2) + δ ∧
      finiteMultiplicity (Γ k z) < min (n : ℝ) ((a ^ 2)⁻¹) + δ := by
  filter_upwards [h.uniform_load δ hδ, h.uniform_coverage δ hδ,
    h.uniform_duplicates δ hδ, h.uniform_multiplicity δ hδ] with k hl hq hd hm
  exact fun z => ⟨hl z, hq z, hd z, hm z⟩

omit [IsProbabilityMeasure F] in

theorem with_affine_floor (h : FixedReceiptFamilyAssumptions M C I Γ B F g a ρ)
    (η₀ : ℝ) (η : ∀ k, I k → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k z, η₀ ≤ η k z) (hη1 : ∀ k z, η k z ≤ 1)
    (hA : ∀ k z, (Γ k z).A = Schedule.affine n (η k z)
      (hη₀.trans (hη k z)) (hη1 k z)) :
    FixedReceiptFamilyAssumptions M C I Γ B F g (Affine.fixedFactor n η₀) ρ where
  proposers_pos := h.proposers_pos
  common_values := h.common_values
  common_fee := h.common_fee
  factor_pos := Affine.fixedFactor_pos n h.proposers_pos η₀ hη₀
  ratio_pos := h.ratio_pos
  ratio_lt_one := h.ratio_lt_one
  population_grows := h.population_grows
  capacity_ratio := h.capacity_ratio
  users := h.users
  bayes_receipts := h.bayes_receipts
  feasible_continuations := h.feasible_continuations
  visible_atomless := h.visible_atomless
  receipt_lower := by
    intro k z r hr hrn
    rw [hA k z]
    exact Affine.fixedFactor_charge_lower n h.proposers_pos η₀ (η k z)
      hη₀ (hη k z) (hη1 k z) r hr hrn
  scarcity := h.scarcity

theorem affine_uniform_all (h : FixedReceiptFamilyAssumptions M C I Γ B F g a ρ)
    (η₀ : ℝ) (η : ∀ k, I k → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k z, η₀ ≤ η k z) (hη1 : ∀ k z, η k z ≤ 1)
    (hA : ∀ k z, (Γ k z).A = Schedule.affine n (η k z)
      (hη₀.trans (hη k z)) (hη1 k z)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ z : I k,
      |finiteLoad (Γ k z) - (n : ℝ) * ρ| < δ ∧
      (n : ℝ) * ρ * (Affine.fixedFactor n η₀) ^ 2 - δ < finiteCoverage (Γ k z) ∧
      finiteLoad (Γ k z) - finiteCoverage (Γ k z) <
        (n : ℝ) * ρ * (1 - (Affine.fixedFactor n η₀) ^ 2) + δ ∧
      finiteMultiplicity (Γ k z) < min (n : ℝ) (((Affine.fixedFactor n η₀) ^ 2)⁻¹) + δ :=
  (h.with_affine_floor η₀ η hη₀ hη hη1 hA).uniform_all δ hδ

end FixedReceiptFamilyAssumptions
end Bayes
end FCAppendix
