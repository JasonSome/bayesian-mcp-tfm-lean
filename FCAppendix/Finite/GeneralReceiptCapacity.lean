import FCAppendix.Affine.FixedTheorem

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem schedule_inverse_count_floor (A : Schedule n) (hn : 0 < n)
    (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) :
    (1 / (n : ℝ)) * r ≤ A.charge r := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc
    (1 / (n : ℝ)) * r = (r : ℝ) / n := by ring
    _ ≤ 1 := (div_le_iff₀ hnR).mpr (by simpa using (Nat.cast_le.mpr hrn : (r : ℝ) ≤ n))
    _ ≤ A.charge r := A.lower r hr hrn

theorem CongestedAssumptions.fixedReceipt_from_schedule
    {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {F : Measure ℝ} {g ρ vstar : ℝ}
    (h : CongestedAssumptions M C Γ F g ρ vstar)
    (B : ∀ k, PosteriorSystem (Γ k))
    (hB : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k)) :
    FixedReceiptAssumptions M C Γ B F g (1 / (n : ℝ)) ρ where
  proposers_pos := by have hh := h.proposers_two; omega
  common_values := h.common_values
  common_fee := h.common_fee
  factor_pos := one_div_pos.mpr (Nat.cast_pos.mpr (by have hh := h.proposers_two; omega))
  ratio_pos := h.ratio_pos
  ratio_lt_one := h.ratio_lt_one
  population_grows := h.population_grows
  capacity_ratio := h.capacity_ratio
  users := fun k => (h.equilibria k).users
  bayes_receipts := hB
  feasible_continuations := h.feasible_continuations
  visible_atomless := h.visible_atomless
  receipt_lower := fun k r hr hrn => schedule_inverse_count_floor (Γ k).A
    (by have hh := h.proposers_two; omega) r hr hrn
  scarcity := h.scarcity

theorem congested_actual_load_tendsto_capacity
    {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] {g ρ vstar : ℝ}
    (h : CongestedAssumptions M C Γ F g ρ vstar)
    (B : ∀ k, PosteriorSystem (Γ k))
    (hB : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k)) :
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 ((n : ℝ) * ρ)) :=
  (h.fixedReceipt_from_schedule B hB).load_tendsto_capacity

theorem affine_eventually_strict_actual_baseline
    {M C : ℕ → ℕ} {Γ Γ₀ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] {g ρ vstar : ℝ}
    (h : CongestedAssumptions M C Γ F g ρ vstar)
    (h₀ : CongestedAssumptions M C Γ₀ F g ρ vstar)
    (B : ∀ k, PosteriorSystem (Γ k)) (B₀ : ∀ k, PosteriorSystem (Γ₀ k))
    (hB : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k))
    (hB₀ : ∀ k, BayesReceiptOptimalOnPath (Γ₀ k) (B₀ k))
    (η₀ : ℝ) (η : ℕ → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k) (hη₀.trans (hη k)) (hη1 k))
    (Q₀ : ℝ) (hq₀ : Tendsto (fun k => finiteCoverage (Γ₀ k)) atTop (𝓝 Q₀))
    (hthreshold : ((n : ℝ) * Real.sqrt (Q₀ / ((n : ℝ) * ρ)) - 1) /
      ((n : ℝ) - 1) < η₀) :
    ∀ᶠ k in atTop, finiteCoverage (Γ₀ k) < finiteCoverage (Γ k) ∧
      finiteLoad (Γ k) - finiteCoverage (Γ k) <
        finiteLoad (Γ₀ k) - finiteCoverage (Γ₀ k) ∧
      finiteMultiplicity (Γ k) < finiteMultiplicity (Γ₀ k) := by
  have hb := h₀.fixedReceipt_from_schedule B₀ hB₀
  have hpos := hb.limit_coverage_pos Q₀ hq₀
  have hl := hb.load_tendsto_capacity
  exact affine_eventually_strict_baseline h B hB η₀ η hη₀ hη hη1 hA
    (fun k => finiteCoverage (Γ₀ k))
    (fun k => finiteLoad (Γ₀ k) - finiteCoverage (Γ₀ k))
    (fun k => finiteMultiplicity (Γ₀ k)) Q₀ hpos hq₀
    (hl.sub hq₀) (hl.div hq₀ hpos.ne') hthreshold

theorem affine_exists_strict_actual_baseline
    {M C : ℕ → ℕ} {Γ₀ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] {g ρ vstar : ℝ}
    (h₀ : CongestedAssumptions M C Γ₀ F g ρ vstar)
    (B₀ : ∀ k, PosteriorSystem (Γ₀ k))
    (hB₀ : ∀ k, BayesReceiptOptimalOnPath (Γ₀ k) (B₀ k))
    (Q₀ : ℝ) (hq₀ : Tendsto (fun k => finiteCoverage (Γ₀ k)) atTop (𝓝 Q₀))
    (hdup : 0 < (n : ℝ) * ρ - Q₀)
    (ηbase : ℝ) (hbase : ηbase < 1) :
    ∃ η₀ : ℝ, ∃ hη₀ : 0 < η₀, ηbase < η₀ ∧ η₀ < 1 ∧
      ∀ (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
        (_h : CongestedAssumptions M C Γ F g ρ vstar)
        (B : ∀ k, PosteriorSystem (Γ k))
        (_hB : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k))
        (η : ℕ → ℝ) (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1),
        (∀ k, (Γ k).A = Schedule.affine n (η k) (hη₀.le.trans (hη k)) (hη1 k)) →
        ∀ᶠ k in atTop, finiteCoverage (Γ₀ k) < finiteCoverage (Γ k) ∧
          finiteLoad (Γ k) - finiteCoverage (Γ k) <
            finiteLoad (Γ₀ k) - finiteCoverage (Γ₀ k) ∧
          finiteMultiplicity (Γ k) < finiteMultiplicity (Γ₀ k) := by
  have hb := h₀.fixedReceipt_from_schedule B₀ hB₀
  have hpos := hb.limit_coverage_pos Q₀ hq₀
  obtain ⟨η₀, hη₀, habove, hbelow, hthreshold⟩ :=
    Affine.exists_improving_coefficient_floor n h₀.proposers_two ((n : ℝ) * ρ) Q₀ ηbase
      (mul_pos (Nat.cast_pos.mpr hb.proposers_pos) h₀.ratio_pos) hpos.le
      (sub_pos.mp hdup) hbase
  refine ⟨η₀, hη₀, habove, hbelow, ?_⟩
  intro Γ h B hB η hη hη1 hA
  exact affine_eventually_strict_actual_baseline h h₀ B B₀ hB hB₀ η₀ η hη₀.le
    hη hη1 hA Q₀ hq₀ hthreshold

end FCAppendix.Bayes
