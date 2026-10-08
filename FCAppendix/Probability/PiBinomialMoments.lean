import FCAppendix.Probability.PiBinomial
import FCAppendix.Probability.FinitePushforward
import FCAppendix.Probability.BinomialShortfall

namespace FCAppendix.PiBinomial

open MeasureTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

noncomputable def boundedCount (E : Set Ω) (s : Finset ι) (ω : ι → Ω) : Fin (s.card + 1) :=
  ⟨count E s ω, Nat.lt_succ_of_le (count_le E s ω)⟩

omit [Fintype ι] in
theorem measurable_boundedCount (E : Set Ω) (hE : MeasurableSet E) (s : Finset ι) :
    Measurable (boundedCount E s) := by
  apply measurable_to_countable'
  intro r
  have hs : boundedCount E s ⁻¹' {r} = (fun ω => count E s ω) ⁻¹' {r.val} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Fin.ext_iff
  rw [hs]
  exact (measurable_count E hE s) (measurableSet_singleton r.val)

theorem law_boundedCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (s : Finset ι) :
    FiniteLaw.ofMeasure (Measure.pi fun _ : ι => μ) (boundedCount E s)
      (measurable_boundedCount E hE s) =
      IndependentCounts.binomial s.card (μ.real E) measureReal_nonneg measureReal_le_one := by
  apply FiniteLaw.ext
  intro r
  rw [FiniteLaw.ofMeasure_mass, binomial_mass]
  have hs : {ω : ι → Ω | boundedCount E s ω = r} = {ω | count E s ω = r.val} := by
    ext ω
    exact Fin.ext_iff
  rw [hs]
  exact measureReal_count_eq μ E hE s r.val

theorem integral_count_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (s : Finset ι) (f : ℕ → ℝ) :
    (∫ ω : ι → Ω, f (count E s ω) ∂(Measure.pi fun _ : ι => μ)) =
      (IndependentCounts.binomial s.card (μ.real E) measureReal_nonneg measureReal_le_one).expect
        (fun r => f r.val) := by
  rw [← law_boundedCount μ E hE s, FiniteLaw.expect_ofMeasure]
  rfl

theorem integral_shortfall_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (s : Finset ι) (c : ℝ) :
    (∫ ω : ι → Ω, max (c - (count E s ω : ℝ)) 0 ∂(Measure.pi fun _ : ι => μ)) ≤
      max (c - s.card * μ.real E) 0 + Real.sqrt s.card / 2 := by
  rw [integral_count_eq μ E hE s (fun k => max (c - (k : ℝ)) 0)]
  exact IndependentCounts.binomial_shortfall_le_sqrt _ _ _ _ _

theorem integral_normalized_shortfall_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (s : Finset ι) (hs : 0 < s.card)
    (κ ρ ε : ℝ) (hε : 0 ≤ ε) (hp : ρ - ε ≤ μ.real E) :
    (∫ ω : ι → Ω, max ((s.card : ℝ) * κ - (count E s ω : ℝ)) 0
      ∂(Measure.pi fun _ : ι => μ)) / s.card ≤
      ε + |κ - ρ| + 1 / (2 * Real.sqrt s.card) := by
  rw [integral_count_eq μ E hE s (fun k => max ((s.card : ℝ) * κ - k) 0)]
  exact IndependentCounts.binomial_normalized_shortfall_le s.card hs
    (μ.real E) κ ρ ε measureReal_nonneg measureReal_le_one hε hp

end FCAppendix.PiBinomial
