import FCAppendix.Finite.ConditionalCountLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace FCAppendix.Affine.Multiple07

open MeasureTheory ProbabilityTheory Game Bayes Filter Topology
open scoped BigOperators

variable {n : ℕ}

theorem count_expect_tendsto {α : Type*} {l : Filter α}
    (P : α → CountLaw n) (Q : CountLaw n)
    (h : ∀ r, Tendsto (fun a => (P a).mass r) l (𝓝 (Q.mass r)))
    (f : Fin (n + 1) → ℝ) :
    Tendsto (fun a => (P a).expect f) l (𝓝 (Q.expect f)) := by
  unfold FiniteLaw.expect
  exact tendsto_finsetSum _ (fun r _ => (h r).mul_const (f r))

theorem common_conull_mass_limits {Ω α : Type*} [MeasurableSpace Ω]
    (F : Measure Ω) (l : Filter α) (P : α → Ω → CountLaw n)
    (Q : Ω → CountLaw n)
    (h : ∀ r, ∀ᵐ v ∂F,
      Tendsto (fun a => (P a v).mass r) l (𝓝 ((Q v).mass r))) :
    ∀ᵐ v ∂F, ∀ r,
      Tendsto (fun a => (P a v).mass r) l (𝓝 ((Q v).mass r)) :=
  ae_all_iff.mpr h

theorem count_integral_limit {Ω : Type*} [MeasurableSpace Ω]
    (F : Measure Ω) [IsFiniteMeasure F]
    (P : ℕ → Ω → CountLaw n) (Q : Ω → CountLaw n)
    (hmeas : ∀ k r, Measurable (fun v => (P k v).mass r))
    (hlim : ∀ᵐ v ∂F, ∀ r,
      Tendsto (fun k => (P k v).mass r) atTop (𝓝 ((Q v).mass r)))
    (f : Fin (n + 1) → ℝ) :
    Tendsto (fun k => ∫ v, (P k v).expect f ∂F) atTop
      (𝓝 (∫ v, (Q v).expect f ∂F)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun _ => ∑ r, ‖f r‖) ?_ (integrable_const _) ?_ ?_
  · intro k
    exact (Finset.measurable_sum _
      (fun r _ => (hmeas k r).mul_const (f r))).aestronglyMeasurable
  · intro k
    exact Eventually.of_forall fun v => (P k v).norm_expect_le_sum_norm f
  · filter_upwards [hlim] with v hv
    exact count_expect_tendsto (fun k => P k v) (Q v) hv f

variable {Seed : Type*} [MeasurableSpace Seed]
variable {users capacity : ℕ → ℕ}

theorem measurable_actual_conditional_mass
    {m c : ℕ} (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (r : Fin (n + 1)) :
    Measurable (fun v => (conditionalTypeCountLaw Γ hm v).mass r) := by
  simpa only [FiniteLaw.expect_singleton] using
    measurable_conditionalTypeCountLaw_expect Γ hm
      (fun r' => if r' = r then 1 else 0)

theorem actual_count_moment_limit
    (Γ : ∀ k, FiniteGame (users k) n (capacity k) Seed)
    (hm : ∀ k, 0 < users k)
    (F : Measure ℝ) [IsFiniteMeasure F]
    (hF : ∀ k, (Γ k).F = F) (Q : ℝ → CountLaw n)
    (hlim : ∀ᵐ v ∂F, ∀ r,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hm k) v).mass r)
        atTop (𝓝 ((Q v).mass r)))
    (f : Fin (n + 1) → ℝ) :
    Tendsto
      (fun k =>
        (∑ i, ∫ ω, f (playedCount (Γ k) i ω) ∂backgroundLaw (Γ k)) /
          users k)
      atTop (𝓝 (∫ v, (Q v).expect f ∂F)) := by
  have h := count_integral_limit F
    (fun k v => conditionalTypeCountLaw (Γ k) (hm k) v) Q
    (fun k r => measurable_actual_conditional_mass (Γ k) (hm k) r) hlim f
  apply h.congr'
  exact Eventually.of_forall fun k => by
    rw [← hF k]
    exact integral_conditionalTypeCountLaw_expect_eq_actual (Γ k) (hm k) f

theorem actual_aggregate_limits
    (Γ : ∀ k, FiniteGame (users k) n (capacity k) Seed)
    (hm : ∀ k, 0 < users k)
    (F : Measure ℝ) [IsFiniteMeasure F]
    (hF : ∀ k, (Γ k).F = F) (Q : ℝ → CountLaw n)
    (hlim : ∀ᵐ v ∂F, ∀ r,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hm k) v).mass r)
        atTop (𝓝 ((Q v).mass r))) :
    Tendsto (fun k => finiteCoverage (Γ k)) atTop
        (𝓝 (∫ v, (Q v).success ∂F)) ∧
      Tendsto (fun k => finiteLoad (Γ k)) atTop
        (𝓝 (∫ v, (Q v).load ∂F)) ∧
      Tendsto (fun k => finiteLoad (Γ k) - finiteCoverage (Γ k)) atTop
        (𝓝 (∫ v, (Q v).duplicates ∂F)) := by
  have hs := actual_count_moment_limit Γ hm F hF Q hlim
    (fun r => successIndicator r.val)
  have hl := actual_count_moment_limit Γ hm F hF Q hlim
    (fun r => (r.val : ℝ))
  have hd := count_integral_limit F
    (fun k v => conditionalTypeCountLaw (Γ k) (hm k) v) Q
    (fun k r => measurable_actual_conditional_mass (Γ k) (hm k) r) hlim
    (fun r => (r.val : ℝ) - successIndicator r.val)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [← finiteCoverage_eq_actual, CountLaw.success] using hs
  · simpa only [← finiteLoad_eq_actual, CountLaw.load] using hl
  · simp only [← CountLaw.duplicates_eq_expect] at hd
    apply hd.congr'
    exact Eventually.of_forall fun k => by
      rw [← hF k]
      exact integral_conditionalTypeCountLaw_duplicates (Γ k) (hm k)

theorem actual_multiplicity_limit
    (Γ : ∀ k, FiniteGame (users k) n (capacity k) Seed)
    {q ell : ℝ}
    (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 q))
    (hL : Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 ell))
    (hq : 0 < q) :
    Tendsto (fun k => finiteMultiplicity (Γ k)) atTop (𝓝 (ell / q)) ∧
      ∀ᶠ k in atTop, 0 < finiteCoverage (Γ k) := by
  refine ⟨?_, ?_⟩
  · change Tendsto (fun k => finiteLoad (Γ k)/finiteCoverage (Γ k)) atTop (𝓝 (ell/q))
    exact hL.div hQ hq.ne'
  · exact hQ.eventually (eventually_gt_nhds hq)

theorem actual_fixed_value_outcomes
    (Γ : ∀ k, FiniteGame (users k) n (capacity k) Seed)
    (hm : ∀ k, 0 < users k) (v : ℝ) (Q : CountLaw n)
    (hlim : ∀ r,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hm k) v).mass r)
        atTop (𝓝 (Q.mass r))) :
    Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hm k) v).success)
        atTop (𝓝 Q.success) ∧
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hm k) v).load)
        atTop (𝓝 Q.load) ∧
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hm k) v).duplicates)
        atTop (𝓝 Q.duplicates) ∧
      (0 < Q.success →
        Tendsto
          (fun k => conditionalMultiplicity
            (conditionalTypeCountLaw (Γ k) (hm k) v).success
            (conditionalTypeCountLaw (Γ k) (hm k) v).load)
          atTop (𝓝 (conditionalMultiplicity Q.success Q.load))) := by
  have hs := count_expect_tendsto
    (fun k => conditionalTypeCountLaw (Γ k) (hm k) v) Q hlim
    (fun r => successIndicator r.val)
  have hl := count_expect_tendsto
    (fun k => conditionalTypeCountLaw (Γ k) (hm k) v) Q hlim
    (fun r => (r.val : ℝ))
  change Tendsto _ atTop (𝓝 Q.success) at hs
  change Tendsto _ atTop (𝓝 Q.load) at hl
  refine ⟨hs, hl, hl.sub hs, ?_⟩
  intro hq
  exact hl.div hs hq.ne'

theorem common_actual_strict_outcomes
    (Γ₁ Γ₂ : ∀ k, FiniteGame (users k) n (capacity k) Seed)
    {q₁ q₂ d₁ d₂ ell : ℝ}
    (hQ₁ : Tendsto (fun k => finiteCoverage (Γ₁ k)) atTop (𝓝 q₁))
    (hQ₂ : Tendsto (fun k => finiteCoverage (Γ₂ k)) atTop (𝓝 q₂))
    (hD₁ : Tendsto (fun k => finiteLoad (Γ₁ k) - finiteCoverage (Γ₁ k))
      atTop (𝓝 d₁))
    (hD₂ : Tendsto (fun k => finiteLoad (Γ₂ k) - finiteCoverage (Γ₂ k))
      atTop (𝓝 d₂))
    (hL₁ : Tendsto (fun k => finiteLoad (Γ₁ k)) atTop (𝓝 ell))
    (hL₂ : Tendsto (fun k => finiteLoad (Γ₂ k)) atTop (𝓝 ell))
    (hq₂ : 0 < q₂) (hqq : q₂ < q₁) (hdd : d₁ < d₂) (hell : 0 < ell) :
    ∃ N, ∀ k ≥ N,
      0 < finiteCoverage (Γ₁ k) ∧ 0 < finiteCoverage (Γ₂ k) ∧
      finiteCoverage (Γ₂ k) < finiteCoverage (Γ₁ k) ∧
      finiteLoad (Γ₁ k) - finiteCoverage (Γ₁ k) <
        finiteLoad (Γ₂ k) - finiteCoverage (Γ₂ k) ∧
      finiteMultiplicity (Γ₁ k) < finiteMultiplicity (Γ₂ k) := by
  have hq₁ : 0 < q₁ := hq₂.trans hqq
  have hmu₁ := actual_multiplicity_limit Γ₁ hQ₁ hL₁ hq₁
  have hmu₂ := actual_multiplicity_limit Γ₂ hQ₂ hL₂ hq₂
  have hmm : ell / q₁ < ell / q₂ :=
    div_lt_div_of_pos_left hell hq₂ hqq
  have hqs := Tendsto.eventually_lt hQ₂ hQ₁ hqq
  have hds := Tendsto.eventually_lt hD₁ hD₂ hdd
  have hms := Tendsto.eventually_lt hmu₁.1 hmu₂.1 hmm
  apply eventually_atTop.mp
  filter_upwards [hmu₁.2, hmu₂.2, hqs, hds, hms] with k h₁ h₂ hq hd hmu
  exact ⟨h₁, h₂, hq, hd, hmu⟩

end FCAppendix.Affine.Multiple07
