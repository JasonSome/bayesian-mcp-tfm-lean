import FCAppendix.Ample.Service
import FCAppendix.Finite.NearPPILimit

namespace FCAppendix.Bayes.ReceiptSequenceAssumptions

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g a ρ : ℝ}

omit [IsProbabilityMeasure F] in

theorem exists_ample_fixed_floor
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hA : ∀ k r, 0 < r → r ≤ n → α k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ F.real (Ioi g) < (n : ℝ) * ρ * a₀ ^ 2 ∧
      ∃ N : ℕ, ReceiptSequenceAssumptions (fun k => M (k + N))
        (fun k => C (k + N)) (fun k => Γ (k + N)) (fun k => B (k + N)) F g a₀ ρ := by
  let b : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 1)
  have hb : Tendsto b atTop (𝓝 1) := by
    have hh : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [b] using hh.const_sub 1
  have ht : Tendsto (fun k => (n : ℝ) * ρ * b k ^ 2) atTop (𝓝 ((n : ℝ) * ρ)) := by
    simpa using (hb.pow 2).const_mul ((n : ℝ) * ρ)
  obtain ⟨r, hr0, hramp⟩ := (((tendsto_order.mp hb).1 0 zero_lt_one).and
    ((tendsto_order.mp ht).1 _ hample)).exists
  have hr1 : b r < 1 := by
    dsimp [b]
    have hp : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hα).1 (b r) hr1)
  refine ⟨b r, hr0, hramp, N, ?_⟩
  have hs : Tendsto (fun k : ℕ => k + N) atTop atTop := tendsto_add_atTop_nat N
  exact {
    proposers_pos := h.proposers_pos
    common_values := fun k => h.common_values (k + N)
    common_fee := fun k => h.common_fee (k + N)
    factor_pos := hr0
    ratio_pos := h.ratio_pos
    ratio_lt_one := h.ratio_lt_one
    population_grows := h.population_grows.comp hs
    capacity_ratio := h.capacity_ratio.comp hs
    users := fun k => h.users (k + N)
    bayes_receipts := fun k => h.bayes_receipts (k + N)
    feasible_continuations := fun k => h.feasible_continuations (k + N)
    visible_atomless := fun k => h.visible_atomless (k + N)
    receipt_lower := fun k r hr hrn => (mul_le_mul_of_nonneg_right
      (hN (k + N) (by omega)).le (Nat.cast_nonneg r)).trans (hA (k + N) r hr hrn) }

theorem ample_nearPPI_envelope_tendsto
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hA : ∀ k r, 0 < r → r ≤ n → α k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (i : ∀ k, Fin (M k)) (v : ℝ) :
    Tendsto (fun k => (problem (Γ k) (i k)).envelope v) atTop (𝓝 (max (v - g) 0)) := by
  obtain ⟨a₀, _, hfloor, N, hN⟩ := h.exists_ample_fixed_floor α hα hA hample
  apply (tendsto_add_atTop_iff_nat N).mp
  exact hN.ample_envelope_tendsto hg hfloor (fun k => i (k + N)) v

theorem ample_nearPPI_envelope_uniformOn_compact
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hA : ∀ k r, 0 < r → r ≤ n → α k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (i : ∀ k, Fin (M k)) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun k v => (problem (Γ k) (i k)).envelope v)
      (fun v => max (v - g) 0) atTop K :=
  NearPPI.uniformOn_compact_of_lipschitz 1
    (fun k => (problem (Γ k) (i k)).envelope_lipschitzWith)
    (h.ample_nearPPI_envelope_tendsto hg α hα hA hample i) hK

theorem ample_nearPPI_bestResponses
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hA : ∀ k r, 0 < r → r ≤ n → α k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (i : ∀ k, Fin (M k)) (v : ℝ) (hv : g < v) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act →
      1 - ((problem (Γ k) (i k)).outcome act).success < ε ∧ act.bid < ε ∧
      g * (((problem (Γ k) (i k)).outcome act).charge (Γ k).G -
        ((problem (Γ k) (i k)).outcome act).success) < ε := by
  have hU := h.ample_nearPPI_envelope_tendsto hg α hα hA hample i v
  have hdef : Tendsto (fun k => Ample.deficit (problem (Γ k) (i k)) (v - g))
      atTop (𝓝 0) := by
    have he (k : ℕ) : (v - g) + (problem (Γ k) (i k)).g = v := by
      change (v - g) + (Γ k).g = v
      rw [h.common_fee k]
      ring
    simpa only [Ample.deficit, he, max_eq_left (sub_pos.mpr hv).le, sub_self] using
      hU.const_sub (v - g)
  have hh := Ample.all_bestResponses_full_service_of_deficit
    (fun k => problem (Γ k) (i k)) (v - g) (sub_pos.mpr hv) hdef
  have he (k : ℕ) : (problem (Γ k) (i k)).g = g := h.common_fee k
  have hG (k : ℕ) : (problem (Γ k) (i k)).G = (Γ k).G := rfl
  simpa only [he, hG, sub_add_cancel] using hh

theorem ample_nearPPI_coverage_tendsto
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hA : ∀ k r, 0 < r → r ≤ n → α k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ) :
    Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 (F.real (Ioi g))) := by
  obtain ⟨a₀, _, hfloor, N, hN⟩ := h.exists_ample_fixed_floor α hα hA hample
  apply (tendsto_add_atTop_iff_nat N).mp
  exact hN.ample_coverage_tendsto hg hfloor

end FCAppendix.Bayes.ReceiptSequenceAssumptions
