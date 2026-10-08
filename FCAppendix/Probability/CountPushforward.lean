import FCAppendix.Probability.CountLaw

namespace FCAppendix

open MeasureTheory
open scoped BigOperators

namespace CountLaw

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

theorem integrable_sum {ι : Type*} (μ : Measure Ω) (s : Finset ι)
    (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun ω => ∑ i ∈ s, f i ω) μ := by
  exact integrable_finsetSum s hf

theorem integrable_fiber (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Fin (n + 1)) (hK : Measurable K) (r : Fin (n + 1)) :
    Integrable (fun ω => if K ω = r then (1 : ℝ) else 0) μ := by
  have hs : MeasurableSet {ω | K ω = r} := hK (measurableSet_singleton r)
  have h := (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).indicator hs
  convert h using 1 <;> first | rfl | (ext ω; simp [Set.indicator])

theorem integrable_comp (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Fin (n + 1)) (hK : Measurable K) (f : Fin (n + 1) → ℝ) :
    Integrable (fun ω => f (K ω)) μ := by
  classical
  have h := integrable_sum μ Finset.univ
    (fun r ω => (if K ω = r then (1 : ℝ) else 0) * f r)
    (fun r _ => (integrable_fiber μ K hK r).mul_const (f r))
  simpa [ite_mul, eq_comm] using h

noncomputable def ofMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Fin (n + 1)) (hK : Measurable K) : CountLaw n where
  mass r := ∫ ω, (if K ω = r then (1 : ℝ) else 0) ∂μ
  nonneg r := integral_nonneg (fun ω => by split <;> norm_num)
  total := by
    classical
    rw [← integral_finsetSum Finset.univ (fun r _ => integrable_fiber μ K hK r)]
    simp [eq_comm]

theorem expect_ofMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Fin (n + 1)) (hK : Measurable K) (f : Fin (n + 1) → ℝ) :
    (ofMeasure μ K hK).expect f = ∫ ω, f (K ω) ∂μ := by
  classical
  unfold FiniteLaw.expect ofMeasure
  calc
    (∑ r, (∫ ω, (if K ω = r then (1 : ℝ) else 0) ∂μ) * f r) =
        ∑ r, ∫ ω, (if K ω = r then (1 : ℝ) else 0) * f r ∂μ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [integral_mul_const]
    _ = ∫ ω, ∑ r, (if K ω = r then (1 : ℝ) else 0) * f r ∂μ := by
      symm
      exact integral_finsetSum Finset.univ
        (fun r _ => (integrable_fiber μ K hK r).mul_const (f r))
    _ = _ := by simp [ite_mul, eq_comm]

theorem utility_ofMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Fin (n + 1)) (hK : Measurable K)
    (v b g : ℝ) (A G : Schedule n) :
    Integrable (fun ω => userPayoff v b g A.charge G.charge (K ω).val) μ ∧
    (ofMeasure μ K hK).utility v b g A G =
      ∫ ω, userPayoff v b g A.charge G.charge (K ω).val ∂μ := by
  exact ⟨integrable_comp μ K hK (fun r => userPayoff v b g A.charge G.charge r.val),
    expect_ofMeasure μ K hK (fun r => userPayoff v b g A.charge G.charge r.val)⟩

theorem ofMeasure_congr_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K J : Ω → Fin (n + 1)) (hK : Measurable K) (hJ : Measurable J)
    (h : K =ᵐ[μ] J) : ofMeasure μ K hK = ofMeasure μ J hJ := by
  apply FiniteLaw.ext
  intro r
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

end CountLaw
end FCAppendix
