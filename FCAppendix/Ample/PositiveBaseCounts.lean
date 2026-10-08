import FCAppendix.Ample.NearPPI
import FCAppendix.Finite.MixedBestResponseCounts

namespace FCAppendix.CountLaw
variable {n : ℕ}

theorem duplicates_le_scaled_excess_base (μ : CountLaw n) (G : Schedule n)
    (g d : ℝ) (hd : 0 < d)
    (hG : ∀ r, 2 ≤ r → r ≤ n → d ≤ g * (G.charge r - 1)) :
    μ.duplicates ≤ (n : ℝ) / d * (g * (μ.charge G - μ.success)) := by
  classical
  have hdup : μ.duplicates ≤ (n : ℝ) * μ.prob (fun r => 2 ≤ r.val) := by
    rw [duplicates_eq_expect, FiniteLaw.prob_eq_expect, ← μ.expect_const_mul]
    apply μ.expect_mono
    intro r
    by_cases hr : 2 ≤ r.val
    · simp only [if_pos hr, mul_one, successIndicator, if_neg (by omega : r.val ≠ 0)]
      have hh : (r.val : ℝ) ≤ n := by exact_mod_cast (show r.val ≤ n by omega)
      linarith
    · have hr0 : r.val = 0 ∨ r.val = 1 := by omega
      rcases hr0 with hr0 | hr0 <;> simp [hr0, successIndicator]
  have hprob := μ.duplicate_probability_le_excess_base G g d hG
  calc
    μ.duplicates ≤ (n : ℝ) * μ.prob (fun r => 2 ≤ r.val) := hdup
    _ ≤ (n : ℝ) * (g * (μ.charge G - μ.success) / d) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mpr (by nlinarith)) (Nat.cast_nonneg n)
    _ = _ := by ring
end FCAppendix.CountLaw

namespace FCAppendix.Bayes.ReceiptSequenceAssumptions
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g a ρ : ℝ}

theorem ample_positive_base_duplicates_uniform
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2)
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1))
    (v : ℝ) (hv : g < v) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ (i : Fin (M k)) (act : JointAction n),
      (problem (Γ k) i).BestResponse v act →
      ((problem (Γ k) i).outcome act).duplicates < ε := by
  intro ε hε
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr h.proposers_pos
  have hnd : 0 < (n : ℝ) / d := div_pos hn hd
  filter_upwards [h.ample_envelope_uniform hg hample v (ε / ((n : ℝ) / d))
    (div_pos hε hnd)] with k hk
  intro i act hbr
  have hb := CountLaw.duplicates_le_scaled_excess_base ((problem (Γ k) i).outcome act)
    (Γ k).G g d hd (hG k)
  have he := Ample.excess_base_le_deficit (problem (Γ k) i) (v - g)
    (sub_pos.mpr hv).le act (by simpa only [show (problem (Γ k) i).g = g from h.common_fee k,
      sub_add_cancel] using hbr)
  have heq : (problem (Γ k) i).g = g := h.common_fee k
  have hGq : (problem (Γ k) i).G = (Γ k).G := rfl
  simp only [Ample.deficit, heq, hGq, sub_add_cancel] at he
  have heps := hk i v le_rfl
  rw [max_eq_left (sub_pos.mpr hv).le, abs_sub_comm] at heps
  have hdif : v - g - (problem (Γ k) i).envelope v < ε / ((n : ℝ) / d) :=
    lt_of_le_of_lt (le_abs_self _) heps
  have hh := (lt_div_iff₀ hnd).mp hdif
  have hlt : (n : ℝ) / d * (v - g - (problem (Γ k) i).envelope v) < ε := by nlinarith
  exact (hb.trans (mul_le_mul_of_nonneg_left he hnd.le)).trans_lt hlt

theorem ample_positive_base_mixed_count
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2)
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1))
    (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ) (hv : g < v)
    (hbr : ∀ k, ∀ᵐ act ∂ν k, (problem (Γ k) (i k)).BestResponse v act)
    (f : ℕ → ℝ) :
    Tendsto (fun k => (mixedCountLaw (Γ k) (i k) (ν k)).expect (fun r => f r.val))
      atTop (𝓝 (f 1)) := by
  let j : Fin (n + 1) := ⟨1, by have hh := h.proposers_pos; omega⟩
  apply mixedCountLaw_test_tendsto_of_all_bestResponses M C Γ i ν v j hbr
  intro ε hε
  filter_upwards [h.ample_bestResponses hg hample i v hv (ε / 2) (half_pos hε),
    h.ample_positive_base_duplicates_uniform hg hample d hd hG v hv (ε / 2) (half_pos hε)]
    with k hs hd'
  intro act hact
  have hb := ((problem (Γ k) (i k)).outcome act).not_one_probability_bound
  have h1 := (hs act hact).1
  have h2 := hd' (i k) act hact
  change ((problem (Γ k) (i k)).outcome act).prob (fun r => r.val ≠ 1) < ε
  linarith

theorem ample_positive_base_duplicates_tendsto_of_pos
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2)
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1))
    (hm : ∀ k, 0 < M k) :
    Tendsto (fun k => finiteLoad (Γ k) - finiteCoverage (Γ k)) atTop (𝓝 0) := by
  have hlim : ∀ᵐ v ∂F, Tendsto
      (fun k => (conditionalTypeCountLaw (Γ k) (hm k) v).duplicates) atTop (𝓝 0) := by
    filter_upwards [ae_all_rows_bestResponse M C Γ F h.common_values h.users,
      measure_eq_zero_iff_ae_notMem.mp hg] with v hv hvg
    have hne : v ≠ g := by simpa only [mem_singleton_iff] using hvg
    by_cases hpos : g < v
    · apply tendsto_order.mpr
      constructor
      · intro ε hε
        exact Eventually.of_forall fun k => hε.trans_le (CountLaw.duplicates_nonneg _)
      · intro ε hε
        filter_upwards [h.ample_positive_base_duplicates_uniform hg hample d hd hG v hpos
          (ε / 2) (half_pos hε)] with k hk
        have hbound (i : Fin (M k)) :
            (∫ act, ((problem (Γ k) i).outcome act).duplicates ∂(Γ k).σ v) ≤ ε / 2 := by
          have hint : Integrable (fun act => ((problem (Γ k) i).outcome act).duplicates)
              ((Γ k).σ v) := by
            simpa only [CountLaw.duplicates_eq_expect] using
              FiniteLaw.integrable_expect ((Γ k).σ v) (problem (Γ k) i).outcome
                (measurable_outcome_mass (Γ k) i) (fun r => (r.val : ℝ) - successIndicator r.val)
          have hh := integral_mono_ae hint (integrable_const (ε / 2)) (by
            filter_upwards [hv k i] with act ha
            exact (hk i act ha).le)
          simpa only [integral_const, probReal_univ, one_smul] using hh
        rw [conditionalTypeCountLaw_duplicates]
        have hh := div_le_div_of_nonneg_right
          (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i))
          (Nat.cast_nonneg (M k) : (0 : ℝ) ≤ M k)
        have hmk : (M k : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hm k)).ne'
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_div_cancel_left₀ _ hmk] at hh
        exact hh.trans_lt (half_lt_self hε)
    · have hbelow : v < g := lt_of_le_of_ne (le_of_not_gt hpos) hne
      have hz (k : ℕ) : (conditionalTypeCountLaw (Γ k) (hm k) v).duplicates = 0 := by
        have hzero (i : Fin (M k)) :
            (∫ act, ((problem (Γ k) i).outcome act).duplicates ∂(Γ k).σ v) = 0 := by
          apply integral_eq_zero_of_ae
          filter_upwards [hv k i] with act ha
          have hs := bestResponse_success_zero_below_fee (problem (Γ k) i) v act ha
            (by simpa only [show (problem (Γ k) i).g = g from h.common_fee k] using hbelow)
          have hl := ((problem (Γ k) i).outcome act).load_le_mul_success
          have hn := ((problem (Γ k) i).outcome act).load_nonneg
          simp only [hs, mul_zero] at hl
          change ((problem (Γ k) i).outcome act).duplicates = 0
          unfold CountLaw.duplicates
          rw [hs, sub_zero]
          exact le_antisymm hl hn
        simp only [conditionalTypeCountLaw_duplicates, hzero, Finset.sum_const_zero, zero_div]
      simpa only [hz] using tendsto_const_nhds (x := (0 : ℝ))
  have hh := tendsto_integral_of_dominated_convergence (μ := F) (fun _ => (n : ℝ))
    (fun k => (measurable_conditionalTypeCountLaw_duplicates (Γ k) (hm k)).aestronglyMeasurable)
    (integrable_const (n : ℝ))
    (fun k => ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CountLaw.duplicates_nonneg _)]
      have hl := (conditionalTypeCountLaw (Γ k) (hm k) v).load_le_n
      have hs := (conditionalTypeCountLaw (Γ k) (hm k) v).success_nonneg
      unfold CountLaw.duplicates
      linarith) hlim
  have he (k : ℕ) : (∫ v, (conditionalTypeCountLaw (Γ k) (hm k) v).duplicates ∂F) =
      finiteLoad (Γ k) - finiteCoverage (Γ k) := by
    rw [← h.common_values k, integral_conditionalTypeCountLaw_duplicates]
  simpa only [he, integral_zero] using hh

theorem ample_positive_base_duplicates_tendsto
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2)
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1)) :
    Tendsto (fun k => finiteLoad (Γ k) - finiteCoverage (Γ k)) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.population_grows.eventually_gt_atTop 0)
  apply (tendsto_add_atTop_iff_nat N).mp
  exact (h.along (fun k => k + N) (tendsto_add_atTop_nat N)).ample_positive_base_duplicates_tendsto_of_pos
    hg hample d hd (fun k => hG (k + N)) (fun k => hN (k + N) (by omega))

theorem ample_positive_base_aggregates
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2)
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1))
    (hactive : 0 < F.real (Ioi g)) :
    Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 (F.real (Ioi g))) ∧
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 (F.real (Ioi g))) ∧
    Tendsto (fun k => finiteLoad (Γ k) - finiteCoverage (Γ k)) atTop (𝓝 0) ∧
    Tendsto (fun k => finiteMultiplicity (Γ k)) atTop (𝓝 1) := by
  have hQ := h.ample_coverage_tendsto hg hample
  have hD := h.ample_positive_base_duplicates_tendsto hg hample d hd hG
  have hL : Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 (F.real (Ioi g))) := by
    simpa only [sub_add_cancel, zero_add] using hD.add hQ
  exact ⟨hQ, hL, hD, NearPPI.multiplicity_limit hactive.ne' hQ hL⟩

theorem ample_nearPPI_positive_base_aggregates
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hA : ∀ k r, 0 < r → r ≤ n → α k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1))
    (hactive : 0 < F.real (Ioi g)) :
    Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 (F.real (Ioi g))) ∧
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 (F.real (Ioi g))) ∧
    Tendsto (fun k => finiteLoad (Γ k) - finiteCoverage (Γ k)) atTop (𝓝 0) ∧
    Tendsto (fun k => finiteMultiplicity (Γ k)) atTop (𝓝 1) := by
  obtain ⟨a₀, _, hfloor, N, hN⟩ := h.exists_ample_fixed_floor α hα hA hample
  have hh := hN.ample_positive_base_aggregates hg hfloor d hd (fun k => hG (k + N)) hactive
  exact ⟨(tendsto_add_atTop_iff_nat N).mp hh.1,
    (tendsto_add_atTop_iff_nat N).mp hh.2.1,
    (tendsto_add_atTop_iff_nat N).mp hh.2.2.1,
    (tendsto_add_atTop_iff_nat N).mp hh.2.2.2⟩

theorem ample_positive_base_ae_actual_count
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2)
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1)) :
    ∀ᵐ v ∂F, g < v → ∀ (i : ∀ k, Fin (M k)) (f : ℕ → ℝ),
      Tendsto (fun k => (typeOutcome (Γ k) (i k) v).expect (fun r => f r.val))
        atTop (𝓝 (f 1)) := by
  filter_upwards [ae_all_rows_bestResponse M C Γ F h.common_values h.users] with v hv
  intro hvg i f
  exact h.ample_positive_base_mixed_count hg hample d hd hG i (fun k => (Γ k).σ v)
    v hvg (fun k => hv k (i k)) f

end FCAppendix.Bayes.ReceiptSequenceAssumptions
