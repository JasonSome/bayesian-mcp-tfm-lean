import FCAppendix.Finite.FixedReceiptLimits
import FCAppendix.Finite.NearPPITheorem

namespace FCAppendix.Affine

theorem exists_improving_coefficient_floor (n : ℕ) (hn : 2 ≤ n)
    (β Q₀ ηbase : ℝ) (hβ : 0 < β) (hQ₀ : 0 ≤ Q₀)
    (hdup : Q₀ < β) (hbase : ηbase < 1) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ηbase < η₀ ∧ η₀ < 1 ∧
      ((n : ℝ) * Real.sqrt (Q₀ / β) - 1) / ((n : ℝ) - 1) < η₀ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (Q₀ / β) < 1 := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (div_nonneg hQ₀ hβ.le) ((div_lt_one hβ).mpr hdup)
  have ht : ((n : ℝ) * Real.sqrt (Q₀ / β) - 1) / ((n : ℝ) - 1) < 1 := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)).mpr
    nlinarith
  obtain ⟨η₀, hlo, hhi⟩ := exists_between (max_lt (by norm_num : (0 : ℝ) < 1)
    (max_lt hbase ht))
  exact ⟨η₀, (le_max_left _ _).trans_lt hlo,
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hlo), hhi,
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hlo)⟩

end FCAppendix.Affine

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g a ρ : ℝ}

namespace FixedReceiptAssumptions

theorem limit_coverage_pos (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (Q : ℝ) (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q)) : 0 < Q :=
  lt_of_lt_of_le (mul_pos (mul_pos (Nat.cast_pos.mpr h.proposers_pos) h.ratio_pos)
    (sq_pos_of_pos h.factor_pos)) (h.coverage_limit_lower Q hQ)

theorem limit_aggregate_bounds (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (Q : ℝ) (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q)) :
    (n : ℝ) * ρ * a ^ 2 ≤ Q ∧ Q ≤ (n : ℝ) * ρ ∧
      (n : ℝ) * ρ - Q ≤ (n : ℝ) * ρ * (1 - a ^ 2) ∧
      ((n : ℝ) * ρ) / Q ≤ min (n : ℝ) ((a ^ 2)⁻¹) := by
  have hlo := h.coverage_limit_lower Q hQ
  have hupper := le_of_tendsto_of_tendsto hQ (h.capacity_ratio.const_mul (n : ℝ))
    (Eventually.of_forall fun k => finiteCoverage_le_capacity (Γ k))
  have hcount : (n : ℝ) * ρ ≤ n * Q := by
    apply le_of_tendsto_of_tendsto h.load_tendsto_capacity (hQ.const_mul (n : ℝ))
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with k hk
    exact finiteLoad_le_mul_coverage (Γ k) hk
  refine ⟨hlo, hupper, ?_, ?_⟩
  · nlinarith
  · exact Affine.multiplicity_of_coverage n a ((n : ℝ) * ρ) Q (((n : ℝ) * ρ) / Q)
      h.factor_pos (mul_pos (Nat.cast_pos.mpr h.proposers_pos) h.ratio_pos) rfl hlo hcount

theorem eventually_duplicates_upper (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, finiteLoad (Γ k) - finiteCoverage (Γ k) <
      (n : ℝ) * ρ * (1 - a ^ 2) + δ := by
  filter_upwards [h.eventually_coverage_lower (δ / 2) (by linarith),
    (tendsto_order.mp h.load_tendsto_capacity).2 ((n : ℝ) * ρ + δ / 2) (by linarith)]
    with k hq hl
  nlinarith

theorem multiplicity_excess_tendsto_zero
    (h : FixedReceiptAssumptions M C Γ B F g a ρ) :
    Tendsto (fun k => max (finiteMultiplicity (Γ k) - min (n : ℝ) ((a ^ 2)⁻¹)) 0)
      atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have h' := h.along ns hns
  have hb : ∀ᶠ k in atTop, finiteCoverage (Γ (ns k)) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [h'.population_grows.eventually_gt_atTop 0] with k hk
    exact finiteCoverage_unit_bounds (Γ (ns k)) hk
  obtain ⟨Q, _, φ, hφ, hQ⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).tendsto_subseq' hb.frequently
  have h'' := h'.along φ hφ.tendsto_atTop
  have hpos := h''.limit_coverage_pos Q hQ
  have hm : Tendsto (fun k => finiteMultiplicity (Γ (ns (φ k))))
      atTop (𝓝 (((n : ℝ) * ρ) / Q)) :=
    h''.load_tendsto_capacity.div hQ hpos.ne'
  have hbnd := (h''.limit_aggregate_bounds Q hQ).2.2.2
  have hlim := (hm.sub_const (min (n : ℝ) ((a ^ 2)⁻¹))).max (show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds)
  exact ⟨φ, by simpa only [Function.comp_def, max_eq_right (sub_nonpos.mpr hbnd)] using hlim⟩

theorem eventually_multiplicity_upper
    (h : FixedReceiptAssumptions M C Γ B F g a ρ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, finiteMultiplicity (Γ k) < min (n : ℝ) ((a ^ 2)⁻¹) + δ := by
  filter_upwards [(tendsto_order.mp h.multiplicity_excess_tendsto_zero).2 δ hδ] with k hk
  have hh := le_max_left (finiteMultiplicity (Γ k) - min (n : ℝ) ((a ^ 2)⁻¹)) 0
  linarith

theorem eventually_strict_comparisons
    (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (q₀ d₀ μ₀ : ℕ → ℝ) (Q₀ : ℝ) (hQ₀ : 0 < Q₀)
    (hq₀ : Tendsto q₀ atTop (𝓝 Q₀))
    (hd₀ : Tendsto d₀ atTop (𝓝 ((n : ℝ) * ρ - Q₀)))
    (hμ₀ : Tendsto μ₀ atTop (𝓝 (((n : ℝ) * ρ) / Q₀)))
    (hgap : Q₀ < (n : ℝ) * ρ * a ^ 2) :
    ∀ᶠ k in atTop, q₀ k < finiteCoverage (Γ k) ∧
      finiteLoad (Γ k) - finiteCoverage (Γ k) < d₀ k ∧
      finiteMultiplicity (Γ k) < μ₀ k := by
  let b : ℝ := (n : ℝ) * ρ * a ^ 2
  let q : ℝ := (Q₀ + b) / 2
  have hq0 : 0 < q := by dsimp [q, b]; linarith
  have hq₀q : Q₀ < q := by dsimp [q, b]; linarith
  have hqb : q < b := by dsimp [q, b]; linarith
  have hQ : ∀ᶠ k in atTop, q < finiteCoverage (Γ k) := by
    have hh := h.eventually_coverage_lower (b - q) (sub_pos.mpr hqb)
    filter_upwards [hh] with k hk
    dsimp only [b] at *
    linarith
  have hbeta : 0 < (n : ℝ) * ρ := mul_pos (Nat.cast_pos.mpr h.proposers_pos) h.ratio_pos
  have hratio : ((n : ℝ) * ρ) / q < ((n : ℝ) * ρ) / Q₀ := by
    apply (div_lt_div_iff₀ hq0 hQ₀).mpr
    exact mul_lt_mul_of_pos_left hq₀q hbeta
  have hmdiff : Tendsto (fun k => μ₀ k - finiteLoad (Γ k) / q)
      atTop (𝓝 (((n : ℝ) * ρ) / Q₀ - ((n : ℝ) * ρ) / q)) :=
    hμ₀.sub (h.load_tendsto_capacity.div_const q)
  have hddiff : Tendsto (fun k => d₀ k - (finiteLoad (Γ k) - q))
      atTop (𝓝 (q - Q₀)) := by
    have heq : ((n : ℝ) * ρ - Q₀) - ((n : ℝ) * ρ - q) = q - Q₀ := by ring
    simpa only [heq] using hd₀.sub (h.load_tendsto_capacity.sub_const q)
  filter_upwards [hQ, (tendsto_order.mp hq₀).2 q hq₀q,
    (tendsto_order.mp hmdiff).1 0 (sub_pos.mpr hratio),
    (tendsto_order.mp hddiff).1 0 (sub_pos.mpr hq₀q),
    h.population_grows.eventually_gt_atTop 0] with k hQk hqk hmk hdk hpop
  have hload0 := (finiteLoad_interval_bounds (Γ k) hpop).1
  have hmul : finiteMultiplicity (Γ k) ≤ finiteLoad (Γ k) / q :=
    div_le_div_of_nonneg_left hload0 hq0 hQk.le
  exact ⟨hqk.trans hQk, by linarith, hmul.trans_lt (by linarith)⟩

end FixedReceiptAssumptions

omit [IsProbabilityMeasure F] in

theorem CongestedAssumptions.fixedReceipt_of_affine
    {vstar : ℝ} (h : CongestedAssumptions M C Γ F g ρ vstar)
    (B : ∀ k, PosteriorSystem (Γ k))
    (hB : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k))
    (η₀ : ℝ) (η : ℕ → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k) (hη₀.trans (hη k)) (hη1 k)) :
    FixedReceiptAssumptions M C Γ B F g (Affine.fixedFactor n η₀) ρ where
  proposers_pos := by have hh := h.proposers_two; omega
  common_values := h.common_values
  common_fee := h.common_fee
  factor_pos := Affine.fixedFactor_pos n (by have hh := h.proposers_two; omega) η₀ hη₀
  ratio_pos := h.ratio_pos
  ratio_lt_one := h.ratio_lt_one
  population_grows := h.population_grows
  capacity_ratio := h.capacity_ratio
  users := fun k => (h.equilibria k).users
  bayes_receipts := hB
  feasible_continuations := h.feasible_continuations
  visible_atomless := h.visible_atomless
  receipt_lower := by
    intro k r hr hrn
    rw [hA k]
    exact Affine.fixedFactor_charge_lower n (by have hh := h.proposers_two; omega)
      η₀ (η k) hη₀ (hη k) (hη1 k) r hr hrn
  scarcity := h.scarcity

structure FixedReceiptConclusions
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (a ρ : ℝ) : Prop where
  load : Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 ((n : ℝ) * ρ))
  coverage : ∀ δ > 0, ∀ᶠ k in atTop, (n : ℝ) * ρ * a ^ 2 - δ < finiteCoverage (Γ k)
  duplicates : ∀ δ > 0, ∀ᶠ k in atTop, finiteLoad (Γ k) - finiteCoverage (Γ k) <
    (n : ℝ) * ρ * (1 - a ^ 2) + δ
  multiplicity : ∀ δ > 0, ∀ᶠ k in atTop,
    finiteMultiplicity (Γ k) < min (n : ℝ) ((a ^ 2)⁻¹) + δ
  limiting_outcomes : ∀ Q, Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q) →
    (n : ℝ) * ρ * a ^ 2 ≤ Q ∧ Q ≤ (n : ℝ) * ρ ∧
      (n : ℝ) * ρ - Q ≤ (n : ℝ) * ρ * (1 - a ^ 2) ∧
      ((n : ℝ) * ρ) / Q ≤ min (n : ℝ) ((a ^ 2)⁻¹)

theorem fixed_receipt_bounds (h : FixedReceiptAssumptions M C Γ B F g a ρ) :
    FixedReceiptConclusions M C Γ a ρ where
  load := h.load_tendsto_capacity
  coverage := h.eventually_coverage_lower
  duplicates := h.eventually_duplicates_upper
  multiplicity := h.eventually_multiplicity_upper
  limiting_outcomes := h.limit_aggregate_bounds

theorem affine_fixed_bounds
    {vstar : ℝ} (h : CongestedAssumptions M C Γ F g ρ vstar)
    (B : ∀ k, PosteriorSystem (Γ k))
    (hB : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k))
    (η₀ : ℝ) (η : ℕ → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k) (hη₀.trans (hη k)) (hη1 k)) :
    FixedReceiptConclusions M C Γ (Affine.fixedFactor n η₀) ρ :=
  fixed_receipt_bounds (h.fixedReceipt_of_affine B hB η₀ η hη₀ hη hη1 hA)

theorem affine_eventually_strict_baseline
    {vstar : ℝ} (h : CongestedAssumptions M C Γ F g ρ vstar)
    (B : ∀ k, PosteriorSystem (Γ k))
    (hB : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k))
    (η₀ : ℝ) (η : ℕ → ℝ) (hη₀ : 0 ≤ η₀)
    (hη : ∀ k, η₀ ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k) (hη₀.trans (hη k)) (hη1 k))
    (q₀ d₀ μ₀ : ℕ → ℝ) (Q₀ : ℝ) (hQ₀ : 0 < Q₀)
    (hq₀ : Tendsto q₀ atTop (𝓝 Q₀))
    (hd₀ : Tendsto d₀ atTop (𝓝 ((n : ℝ) * ρ - Q₀)))
    (hμ₀ : Tendsto μ₀ atTop (𝓝 (((n : ℝ) * ρ) / Q₀)))
    (hthreshold : ((n : ℝ) * Real.sqrt (Q₀ / ((n : ℝ) * ρ)) - 1) /
      ((n : ℝ) - 1) < η₀) :
    ∀ᶠ k in atTop, q₀ k < finiteCoverage (Γ k) ∧
      finiteLoad (Γ k) - finiteCoverage (Γ k) < d₀ k ∧
      finiteMultiplicity (Γ k) < μ₀ k := by
  have hf := h.fixedReceipt_of_affine B hB η₀ η hη₀ hη hη1 hA
  have hgap := Affine.strict_gap_of_coefficient_threshold n (by have hh := h.proposers_two; omega)
    ((n : ℝ) * ρ) Q₀ η₀ (mul_pos (Nat.cast_pos.mpr hf.proposers_pos) h.ratio_pos)
    hQ₀.le hthreshold
  exact hf.eventually_strict_comparisons q₀ d₀ μ₀ Q₀ hQ₀ hq₀ hd₀ hμ₀ hgap

end FCAppendix.Bayes
