import FCAppendix.PayOnce.DeficitLimit
import FCAppendix.PayOnce.EffectiveEmpiricalDemand

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory Filter Topology

theorem tendsto_positive_part_difference_integral
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (X Y : ∀ t, Ω t → ℝ) (hX : ∀ t, Integrable (X t) (P t))
    (hY : ∀ t, Integrable (Y t) (P t)) {D ρ : ℝ}
    (hx : Tendsto (fun t => ∫ z, |X t z-D| ∂P t) atTop (𝓝 0))
    (hy : Tendsto (fun t => ∫ z, |Y t z-ρ| ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ z, max (X t z-Y t z) 0 ∂P t) atTop (𝓝 (max (D-ρ) 0)) := by
  have herr : Tendsto (fun t => ∫ z, |(X t z-Y t z)-(D-ρ)| ∂P t) atTop (𝓝 0) := by
    apply squeeze_zero (fun t => integral_nonneg fun _ => abs_nonneg _) _
      (show Tendsto (fun t => (∫ z, |X t z-D| ∂P t)+(∫ z, |Y t z-ρ| ∂P t)) atTop (𝓝 0) by
        simpa only [add_zero] using hx.add hy)
    intro t
    have hiX := ((hX t).sub (integrable_const D)).abs
    have hiY := ((hY t).sub (integrable_const ρ)).abs
    have hh := integral_mono (((hX t).sub (hY t)).sub (integrable_const (D-ρ))).abs
      (hiX.add hiY) (fun z => by
        change |X t z-Y t z-(D-ρ)| ≤ |X t z-D|+|Y t z-ρ|
        have he : X t z-Y t z-(D-ρ) = (X t z-D)-(Y t z-ρ) := by ring
        rw [he]
        exact abs_sub (X t z-D) (Y t z-ρ))
    simp only [Pi.add_apply] at hh
    rw [integral_add hiX hiY] at hh
    exact hh
  have ht := tendsto_positive_part_integral P (fun t z => X t z-Y t z)
    (fun t => (hX t).sub (hY t)) herr (tendsto_const_nhds (x := (0:ℝ)))
  simpa only [sub_zero] using ht

end FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Set Filter Topology Game CommonList
open PayOnce PayOnce.KernelTailEvent PayOnce.KernelLawConvergence PayOnce.CovarianceConcentration
open PayOnce.CompactifiedBidLaws
open scoped BigOperators

theorem tendsto_dummy_kernel_deficit
    {M C : ℕ → ℕ} {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hM : Tendsto M atTop atTop)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G)) {ρ : ℝ}
    (hload : Tendsto (fun t => ∫ d, |populationMean (dummyProfileMarginal (Γ t) hn d)-ρ|
      ∂userProfileLaw (Γ t)) atTop (𝓝 0)) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun t => ∫ d, populationMean (fun i => max (kernel n (effectiveBid (d i).1.2) L-
      dummyProfileMarginal (Γ t) hn d i) 0) ∂userProfileLaw (Γ t)) atTop
        (𝓝 (max (KernelDemand.demand n (G : Measure ENNReal) L-ρ) 0)) := by
  have hI t : Integrable (profileEffectiveKernelDemand (Γ t) L) (userProfileLaw (Γ t)) := by
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hL).measurable.comp
      (measurable_drawEffectiveBid.comp (measurable_pi_apply i)))
      (fun d => (kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).1)
      (fun d => (kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).2)
  have hP t : Integrable (fun d => populationMean (dummyProfileMarginal (Γ t) hn d)) (userProfileLaw (Γ t)) := by
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ (measurable_dummyProfileMarginal (Γ t) hn i)
      (fun d => (dummyProfileMarginal_bounds (Γ t) hn d i).1)
      (fun d => (dummyProfileMarginal_bounds (Γ t) hn d i).2)
  have ht := KernelDemand.tendsto_positive_part_difference_integral (fun t => userProfileLaw (Γ t))
    (fun t => profileEffectiveKernelDemand (Γ t) L) (fun t d => populationMean (dummyProfileMarginal (Γ t) hn d)) hI hP
    (tendsto_integral_profileEffectiveKernelDemand_error Γ hn hM hweak hL) hload
  apply ht.congr
  intro t
  apply integral_congr_ae
  exact Eventually.of_forall fun d => (profile_effective_kernel_deficit (Γ t) hn hL d).symm

end FCAppendix.Bayes
