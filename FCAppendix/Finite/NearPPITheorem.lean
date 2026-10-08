import FCAppendix.Finite.NearPPI
import FCAppendix.Finite.MixedBestResponseCounts

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
  {g : ℝ} {a : ℕ → ℝ} {ρ vstar : ℝ}

namespace NearPPIAssumptions

theorem mixed_count_limit (h : NearPPIAssumptions M C Γ F g a ρ vstar)
    (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ) (hv : v ≠ vstar)
    (hbr : ∀ k, ∀ᵐ act ∂ν k, (problem (Γ k) (i k)).BestResponse v act)
    (f : ℕ → ℝ) :
    Tendsto (fun k => (mixedCountLaw (Γ k) (i k) (ν k)).expect (fun r => f r.val))
      atTop (𝓝 (f (if vstar < v then 1 else 0))) := by
  by_cases habove : vstar < v
  · let j : Fin (n + 1) := ⟨1, by have hh := h.proposers_two; omega⟩
    have hlim : ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
        (problem (Γ k) (i k)).BestResponse v act →
        ((problem (Γ k) (i k)).outcome act).prob (fun r => r.val ≠ j.val) < ε := by
      intro ε hε
      filter_upwards [h.above_cutoff i v habove ε hε] with k hk
      exact fun act hact => (hk act hact).2.2.2.2
    simpa only [if_pos habove, j] using
      mixedCountLaw_test_tendsto_of_all_bestResponses M C Γ i ν v j hbr hlim (fun r => f r.val)
  · have hbelow : v < vstar := lt_of_le_of_ne (le_of_not_gt habove) hv
    have hlim : ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
        (problem (Γ k) (i k)).BestResponse v act →
        ((problem (Γ k) (i k)).outcome act).prob (fun r => r.val ≠ (0 : Fin (n + 1)).val) < ε := by
      intro ε hε
      filter_upwards [h.below_cutoff i v hbelow ε hε] with k hk
      exact fun act hact => (hk act hact).2.2.2
    simpa only [if_neg habove, Fin.val_zero] using
      mixedCountLaw_test_tendsto_of_all_bestResponses M C Γ i ν v 0 hbr hlim (fun r => f r.val)

theorem ae_actual_count_limit (h : NearPPIAssumptions M C Γ F g a ρ vstar) :
    ∀ᵐ v ∂F, v ≠ vstar → ∀ (i : ∀ k, Fin (M k)) (f : ℕ → ℝ),
      Tendsto (fun k => (typeOutcome (Γ k) (i k) v).expect (fun r => f r.val))
        atTop (𝓝 (f (if vstar < v then 1 else 0))) := by
  filter_upwards [ae_all_rows_bestResponse M C Γ F h.common_values (fun k => (h.equilibria k).users)]
    with v hv
  intro hvc i f
  exact h.mixed_count_limit i (fun k => (Γ k).σ v) v hvc (fun k => hv k (i k)) f

theorem mixed_bid_tail (h : NearPPIAssumptions M C Γ F g a ρ vstar)
    (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    (v : ℝ) (hv : vstar < v)
    (hbr : ∀ k, ∀ᵐ act ∂ν k, (problem (Γ k) (i k)).BestResponse v act) :
    ∀ ε > 0, ∀ᶠ k in atTop, (ν k).real {act | ε ≤ |act.bid - (vstar - g)|} = 0 := by
  apply mixed_bid_tail_eventually_zero_of_all_bestResponses M C Γ i ν v (vstar - g) hbr
  intro ε hε
  filter_upwards [h.above_cutoff i v hv ε hε] with k hk
  exact fun act hact => (hk act hact).2.1

end NearPPIAssumptions

omit [IsProbabilityMeasure F] [NullSingletonClass F] in

structure NearPPIConclusions
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) (g ρ vstar : ℝ) : Prop where
  utility : ∀ (i : ∀ k, Fin (M k)) (v : ℝ),
    Tendsto (fun k => (problem (Γ k) (i k)).envelope v) atTop (𝓝 (max (v - vstar) 0))
  utility_compact : ∀ (i : ∀ k, Fin (M k)) (K : Set ℝ), IsCompact K →
    TendstoUniformlyOn (fun k v => (problem (Γ k) (i k)).envelope v)
      (fun v => max (v - vstar) 0) atTop K
  mixed_count : ∀ (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ), v ≠ vstar →
    (∀ k, ∀ᵐ act ∂ν k, (problem (Γ k) (i k)).BestResponse v act) → ∀ f : ℕ → ℝ,
    Tendsto (fun k => (mixedCountLaw (Γ k) (i k) (ν k)).expect (fun r => f r.val))
      atTop (𝓝 (f (if vstar < v then 1 else 0)))
  actual_count : ∀ᵐ v ∂F, v ≠ vstar → ∀ (i : ∀ k, Fin (M k)) (f : ℕ → ℝ),
    Tendsto (fun k => (typeOutcome (Γ k) (i k) v).expect (fun r => f r.val))
      atTop (𝓝 (f (if vstar < v then 1 else 0)))
  supported_bids : ∀ (i : ∀ k, Fin (M k)) (v : ℝ), vstar < v →
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → |act.bid - (vstar - g)| < ε
  coverage : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 ((n : ℝ) * ρ))
  load : Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 ((n : ℝ) * ρ))
  duplicates : Tendsto (fun k => finiteLoad (Γ k) - finiteCoverage (Γ k)) atTop (𝓝 0)
  multiplicity : Tendsto (fun k => finiteMultiplicity (Γ k)) atTop (𝓝 1)

theorem near_ppi (h : NearPPIAssumptions M C Γ F g a ρ vstar) :
    NearPPIConclusions M C Γ F g ρ vstar where
  utility := h.utility_limit
  utility_compact := fun i _ hK => h.utility_uniformOn_compact i hK
  mixed_count := h.mixed_count_limit
  actual_count := h.ae_actual_count_limit
  supported_bids := by
    intro i v hv ε hε
    filter_upwards [h.above_cutoff i v hv ε hε] with k hk
    exact fun act hact => (hk act hact).2.1
  coverage := h.aggregates.1
  load := h.aggregates.2.1
  duplicates := h.aggregates.2.2.1
  multiplicity := h.aggregates.2.2.2

omit [IsProbabilityMeasure F] [NullSingletonClass F] in

theorem CongestedAssumptions.nearPPI_of_ppi
    (h : CongestedAssumptions M C Γ F g ρ vstar)
    (hA : ∀ k, (Γ k).A = Schedule.ppi n) :
    NearPPIAssumptions M C Γ F g (fun _ => 1) ρ vstar where
  toCongestedAssumptions := h
  coefficient_limit := tendsto_const_nhds
  receipt_lower := by
    intro k r _ _
    rw [hA k]
    simp only [Schedule.ppi, one_mul, le_refl]

theorem ppi_endpoint
    (h : CongestedAssumptions M C Γ F g ρ vstar)
    (hA : ∀ k, (Γ k).A = Schedule.ppi n) :
    NearPPIConclusions M C Γ F g ρ vstar := near_ppi (h.nearPPI_of_ppi hA)

omit [IsProbabilityMeasure F] [NullSingletonClass F] in

theorem CongestedAssumptions.nearPPI_of_affine
    (h : CongestedAssumptions M C Γ F g ρ vstar)
    (η : ℕ → ℝ) (hη0 : ∀ k, 0 ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hη : Tendsto η atTop (𝓝 1))
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k) (hη0 k) (hη1 k)) :
    NearPPIAssumptions M C Γ F g (fun k => (1 + ((n : ℝ) - 1) * η k) / n) ρ vstar where
  toCongestedAssumptions := h
  coefficient_limit := by
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have hh := h.proposers_two; omega)
    have he : (1 + ((n : ℝ) - 1) * 1) / n = 1 := by
      rw [mul_one, add_sub_cancel, div_self hn]
    have hh : Tendsto (fun k => (1 + ((n : ℝ) - 1) * η k) / n) atTop
        (𝓝 ((1 + ((n : ℝ) - 1) * 1) / n)) :=
      (tendsto_const_nhds.add (hη.const_mul ((n : ℝ) - 1))).div_const (n : ℝ)
    simpa only [he] using hh
  receipt_lower := by
    intro k r hr hrn
    rw [hA k]
    have hn : 0 < n := by have hh := h.proposers_two; omega
    have hh := Schedule.affine_ratio_lower n r hn hr hrn (η k) (hη0 k) (hη1 k)
    exact (le_div_iff₀ (Nat.cast_pos.mpr hr)).mp hh

theorem affine_near_ppi
    (h : CongestedAssumptions M C Γ F g ρ vstar)
    (η : ℕ → ℝ) (hη0 : ∀ k, 0 ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (hη : Tendsto η atTop (𝓝 1))
    (hA : ∀ k, (Γ k).A = Schedule.affine n (η k) (hη0 k) (hη1 k)) :
    NearPPIConclusions M C Γ F g ρ vstar := near_ppi (h.nearPPI_of_affine η hη0 hη1 hη hA)

end FCAppendix.Bayes
