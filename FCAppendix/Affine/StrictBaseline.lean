import FCAppendix.Finite.FixedReceiptUniformity

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g a a₀ ρ : ℝ}

namespace FixedReceiptAssumptions

variable {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)}

omit [IsProbabilityMeasure F] in

theorem with_affine_floor (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (η₀ : ℝ) (η : ℕ → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k)
      (hη₀.trans (hη k)) (hη1 k)) :
    FixedReceiptAssumptions M C Γ B F g (Affine.fixedFactor n η₀) ρ where
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
    intro k r hr hrn
    rw [hA k]
    exact Affine.fixedFactor_charge_lower n h.proposers_pos η₀ (η k)
      hη₀ (hη k) (hη1 k) r hr hrn
  scarcity := h.scarcity

theorem affine_eventually_strict_actual_baseline
    {Γ₀ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {B₀ : ∀ k, PosteriorSystem (Γ₀ k)}
    (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (h₀ : FixedReceiptAssumptions M C Γ₀ B₀ F g a₀ ρ)
    (hn : 2 ≤ n)
    (η₀ : ℝ) (η : ℕ → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k)
      (hη₀.trans (hη k)) (hη1 k))
    (Q₀ : ℝ) (hq₀ : Tendsto (fun k => finiteCoverage (Γ₀ k)) atTop (𝓝 Q₀))
    (hthreshold : ((n : ℝ) * Real.sqrt (Q₀ / ((n : ℝ) * ρ)) - 1) /
      ((n : ℝ) - 1) < η₀) :
    ∀ᶠ k in atTop, finiteCoverage (Γ₀ k) < finiteCoverage (Γ k) ∧
      finiteLoad (Γ k) - finiteCoverage (Γ k) <
        finiteLoad (Γ₀ k) - finiteCoverage (Γ₀ k) ∧
      finiteMultiplicity (Γ k) < finiteMultiplicity (Γ₀ k) := by
  have hf := h.with_affine_floor η₀ η hη₀ hη hη1 hA
  have hpos := h₀.limit_coverage_pos Q₀ hq₀
  have hl := h₀.load_tendsto_capacity
  have hgap := Affine.strict_gap_of_coefficient_threshold n hn
    ((n : ℝ) * ρ) Q₀ η₀
    (mul_pos (Nat.cast_pos.mpr h.proposers_pos) h.ratio_pos) hpos.le hthreshold
  exact hf.eventually_strict_comparisons
    (fun k => finiteCoverage (Γ₀ k))
    (fun k => finiteLoad (Γ₀ k) - finiteCoverage (Γ₀ k))
    (fun k => finiteMultiplicity (Γ₀ k)) Q₀ hpos hq₀
    (hl.sub hq₀) (hl.div hq₀ hpos.ne') hgap

theorem affine_strict_limiting_baseline
    {Γ₀ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {B₀ : ∀ k, PosteriorSystem (Γ₀ k)}
    (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (h₀ : FixedReceiptAssumptions M C Γ₀ B₀ F g a₀ ρ)
    (hn : 2 ≤ n)
    (η₀ : ℝ) (η : ℕ → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k)
      (hη₀.trans (hη k)) (hη1 k))
    (Q₀ : ℝ) (hq₀ : Tendsto (fun k => finiteCoverage (Γ₀ k)) atTop (𝓝 Q₀))
    (Q : ℝ) (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q))
    (hthreshold : ((n : ℝ) * Real.sqrt (Q₀ / ((n : ℝ) * ρ)) - 1) /
      ((n : ℝ) - 1) < η₀) :
    Q₀ < Q ∧ (n : ℝ) * ρ - Q < (n : ℝ) * ρ - Q₀ ∧
      ((n : ℝ) * ρ) / Q < ((n : ℝ) * ρ) / Q₀ := by
  have hf := h.with_affine_floor η₀ η hη₀ hη hη1 hA
  have hpos := h₀.limit_coverage_pos Q₀ hq₀
  have hbeta := mul_pos (Nat.cast_pos.mpr h.proposers_pos) h.ratio_pos
  have hgap := Affine.strict_gap_of_coefficient_threshold n hn
    ((n : ℝ) * ρ) Q₀ η₀ hbeta hpos.le hthreshold
  exact Affine.strict_baseline_comparison (Affine.fixedFactor n η₀)
    ((n : ℝ) * ρ) Q Q₀ ((n : ℝ) * ρ - Q) ((n : ℝ) * ρ - Q₀)
    (((n : ℝ) * ρ) / Q) (((n : ℝ) * ρ) / Q₀)
    hbeta hpos hgap (hf.coverage_limit_lower Q hQ) rfl rfl rfl rfl

theorem affine_exists_strict_actual_baseline
    {Γ₀ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {B₀ : ∀ k, PosteriorSystem (Γ₀ k)}
    (h₀ : FixedReceiptAssumptions M C Γ₀ B₀ F g a₀ ρ)
    (hn : 2 ≤ n)
    (Q₀ : ℝ) (hq₀ : Tendsto (fun k => finiteCoverage (Γ₀ k)) atTop (𝓝 Q₀))
    (hdup : 0 < (n : ℝ) * ρ - Q₀)
    (ηbase : ℝ) (hbase : ηbase < 1) :
    ∃ η₀ : ℝ, ∃ hη₀ : 0 < η₀, ηbase < η₀ ∧ η₀ < 1 ∧
      ∀ (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
        (B : ∀ k, PosteriorSystem (Γ k)) (a : ℝ)
        (_h : FixedReceiptAssumptions M C Γ B F g a ρ)
        (η : ℕ → ℝ) (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1),
        (∀ k, (Γ k).A = Schedule.affine n (η k)
          (hη₀.le.trans (hη k)) (hη1 k)) →
        (∀ᶠ k in atTop, finiteCoverage (Γ₀ k) < finiteCoverage (Γ k) ∧
          finiteLoad (Γ k) - finiteCoverage (Γ k) <
            finiteLoad (Γ₀ k) - finiteCoverage (Γ₀ k) ∧
          finiteMultiplicity (Γ k) < finiteMultiplicity (Γ₀ k)) ∧
        (∀ Q : ℝ, Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q) →
          Q₀ < Q ∧ (n : ℝ) * ρ - Q < (n : ℝ) * ρ - Q₀ ∧
            ((n : ℝ) * ρ) / Q < ((n : ℝ) * ρ) / Q₀) := by
  have hpos := h₀.limit_coverage_pos Q₀ hq₀
  obtain ⟨η₀, hη₀, habove, hbelow, hthreshold⟩ :=
    Affine.exists_improving_coefficient_floor n hn ((n : ℝ) * ρ) Q₀ ηbase
      (mul_pos (Nat.cast_pos.mpr h₀.proposers_pos) h₀.ratio_pos) hpos.le
      (sub_pos.mp hdup) hbase
  refine ⟨η₀, hη₀, habove, hbelow, ?_⟩
  intro Γ B a h η hη hη1 hA
  refine ⟨h.affine_eventually_strict_actual_baseline h₀ hn η₀ η hη₀.le
    hη hη1 hA Q₀ hq₀ hthreshold, ?_⟩
  intro Q hQ
  exact h.affine_strict_limiting_baseline h₀ hn η₀ η hη₀.le
    hη hη1 hA Q₀ hq₀ Q hQ hthreshold

end FixedReceiptAssumptions
end FCAppendix.Bayes
