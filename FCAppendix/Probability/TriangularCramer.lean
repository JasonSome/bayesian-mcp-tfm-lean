import FCAppendix.Probability.CramerOptimizer
import FCAppendix.Probability.TriangularCramerBounds
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace FCAppendix.TriangularCramer
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.ExponentialTilt FCAppendix.TriangularCramerBounds
open FCAppendix.CramerOptimizer

theorem unit_support_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    {ν : α → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν a : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hweak : Tendsto ν l (𝓝 μ)) : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1 := by
  have hm (a : α) : (ν a : Measure ℝ) (Icc (0 : ℝ) 1) = 1 := by
    simpa only [measure_univ] using
      (ae_mem_iff_measure_eq measurableSet_Icc.nullMeasurableSet).mp (hν a)
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak (isClosed_Icc (a := (0 : ℝ)) (b := 1))
  simp only [hm, limsup_const] at hh
  apply (ae_mem_iff_measure_eq measurableSet_Icc.nullMeasurableSet).mpr
  rw [measure_univ]
  exact le_antisymm (prob_le_one) hh

theorem tendsto_log_tail_succ
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (Y : ∀ m, Fin (m + 1) → Ω m → ℝ)
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ : ℝ}
    (hr : Tendsto (fun m => r m / (m + 1 : ℕ)) atTop (𝓝 ρ))
    (hlower : essInf id (μ : Measure ℝ) < ρ)
    (hmean : ρ < ∫ x, x ∂(μ : Measure ℝ)) :
    (∀ᶠ m in atTop, 0 < tailProbability P Y r m) ∧
    Tendsto (fun m => log (tailProbability P Y r m) / (m + 1 : ℕ)) atTop
      (𝓝 (-lowerRate μ ρ)) := by
  have hlo (c : ℝ) (hc : c < -lowerRate μ ρ) :
      ∀ᶠ m in atTop, 0 < tailProbability P Y r m ∧
        c ≤ log (tailProbability P Y r m) / (m + 1 : ℕ) := by
    obtain ⟨u, hu, hz, hcu⟩ := exists_tilt_lower_bound μ hμ hlower hmean hc
    have htilt := integral_tilted_mul_self (mem_interior_all μ hμ u)
    have htilt' : (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) =
        deriv (cgf id (μ : Measure ℝ)) u := htilt
    apply eventually_log_lower P Y hY hind hν hμ hlaw hweak hr hu
    · rwa [htilt']
    · rwa [htilt']
  have hpos : ∀ᶠ m in atTop, 0 < tailProbability P Y r m :=
    (hlo (-lowerRate μ ρ - 1) (by linarith)).mono fun _ hm => hm.1
  refine ⟨hpos, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro c hc
    obtain ⟨d, hcd, hd⟩ := exists_between hc
    exact (hlo d hd).mono fun _ hm => hcd.trans_le hm.2
  · intro c hc
    obtain ⟨d, hd, hdc⟩ := exists_between hc
    obtain ⟨u, hu, hdu⟩ := exists_negative_tilt_of_essInf μ hμ hlower hmean
    have he : cgf id (μ : Measure ℝ) u - u * ρ = -lowerRate μ ρ := by
      rw [lowerRate_eq μ hμ hu.le hdu]
      ring
    have hh := eventually_log_upper P Y hY hind hν hμ hlaw hweak hr hpos hu.le
      (he ▸ hd)
    exact hh.mono fun _ hm => hm.trans_lt hdc

theorem tendsto_log_tail
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (Y : ∀ m, Fin m → Ω m → ℝ)
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hbound : ∀ m i, ∀ᵐ ω ∂P m, Y m i ω ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ : ℝ}
    (hr : Tendsto (fun m => r m / m) atTop (𝓝 ρ))
    (hlower : essInf id (μ : Measure ℝ) < ρ)
    (hmean : ρ < ∫ x, x ∂(μ : Measure ℝ)) :
    (∀ᶠ m in atTop, 0 < (P m).real {ω | rowSum (Y m) ω ≤ r m}) ∧
    Tendsto (fun m => log ((P m).real {ω | rowSum (Y m) ω ≤ r m}) / m) atTop
      (𝓝 (-lowerRate μ ρ)) := by
  have hν (m : ℕ) : ∀ᵐ x ∂(ν (m + 1) : Measure ℝ), x ∈ Icc (0 : ℝ) 1 :=
    (hlaw (m + 1) 0).ae_mem_snd measurableSet_Icc (hbound (m + 1) 0)
  have hw := hweak.comp (tendsto_add_atTop_nat 1)
  have hμ := unit_support_of_tendsto hν hw
  have hh := tendsto_log_tail_succ (fun m => P (m + 1)) (fun m => Y (m + 1))
    (fun m => hY (m + 1)) (fun m => hind (m + 1))
    hν hμ (fun m => hlaw (m + 1))
    hw (hr.comp (tendsto_add_atTop_nat 1)) hlower hmean
  constructor
  · obtain ⟨N, hN⟩ := eventually_atTop.mp hh.1
    apply eventually_atTop.mpr
    refine ⟨N + 1, fun m hm => ?_⟩
    cases m with
    | zero => omega
    | succ m => exact hN m (by omega)
  · exact (tendsto_add_atTop_iff_nat 1).mp hh.2

end FCAppendix.TriangularCramer
