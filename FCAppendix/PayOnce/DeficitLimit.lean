import FCAppendix.PayOnce.EmpiricalDemand

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory Filter Topology

theorem tendsto_positive_part_integral
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (X : ∀ t, Ω t → ℝ) (hX : ∀ t, Integrable (X t) (P t))
    {D ρ : ℝ} {c : ℕ → ℝ}
    (herror : Tendsto (fun t => ∫ z, |X t z-D| ∂P t) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 ρ)) :
    Tendsto (fun t => ∫ z, max (X t z-c t) 0 ∂P t) atTop (𝓝 (max (D-ρ) 0)) := by
  let f := fun t z => max (X t z-c t) 0
  have hf t : Integrable (f t) (P t) := by
    have hs := (hX t).sub (integrable_const (c t))
    apply hs.abs.mono' (hs.aemeasurable.max aemeasurable_const).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
  have hI t : Integrable (fun z => |X t z-D|) (P t) := ((hX t).sub (integrable_const _)).abs
  have hbound t : |(∫ z, f t z ∂P t)-max (D-ρ) 0| ≤
      (∫ z, |X t z-D| ∂P t)+|c t-ρ| := by
    have he : (∫ z, f t z ∂P t)-max (D-ρ) 0 = ∫ z, f t z-max (D-ρ) 0 ∂P t := by
      rw [integral_sub (hf t) (integrable_const _)]
      simp only [integral_const, probReal_univ, one_smul]
    rw [he]
    have hnorm : |∫ z, f t z-max (D-ρ) 0 ∂P t| ≤ ∫ z, |f t z-max (D-ρ) 0| ∂P t := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => f t z-max (D-ρ) 0)
    apply hnorm.trans
    have hh := integral_mono (((hf t).sub (integrable_const _)).abs)
      ((hI t).add (integrable_const |c t-ρ|)) (fun z => by
        apply (abs_max_sub_max_le_abs (X t z-c t) (D-ρ) 0).trans
        have he : X t z-c t-(D-ρ) = (X t z-D)+(ρ-c t) := by ring
        rw [he]
        simpa only [Pi.add_apply, abs_sub_comm ρ (c t)] using abs_add_le (X t z-D) (ρ-c t))
    simpa only [Pi.add_apply, Pi.sub_apply, integral_add (hI t) (integrable_const _), integral_const,
      probReal_univ, one_smul] using hh
  have ht : Tendsto (fun t => (∫ z, |X t z-D| ∂P t)+|c t-ρ|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, add_zero] using herror.add ((hc.sub_const ρ).abs)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [ht.eventually_lt_const hε] with t ht
  simpa only [Real.dist_eq] using (hbound t).trans_lt ht

end FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Set Filter Topology Game CommonList
open PayOnce PayOnce.KernelTailEvent PayOnce.KernelLawConvergence PayOnce.CovarianceConcentration
open scoped BigOperators

theorem tendsto_actual_kernel_deficit
    {M C : ℕ → ℕ} {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hcm : ∀ t, C t ≤ M t)
    (hM : Tendsto M atTop atTop)
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = n)
    (hbid : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun t => ∫ d, populationMean (fun i => max (kernel n (d i).1.2.bid L-
      analyticalProfileMarginal (Γ t) hn (hcm t) d i) 0) ∂userProfileLaw (Γ t)) atTop
        (𝓝 (max (KernelDemand.demand n (G : Measure ENNReal) L-ρ) 0)) := by
  have hI t : Integrable (profileKernelDemand (Γ t) L) (userProfileLaw (Γ t)) := by
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hL).measurable.comp
      ((measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))))
      (fun d => (kernel_unit_bounds hn hL (d i).1.2.bid).1)
      (fun d => (kernel_unit_bounds hn hL (d i).1.2.bid).2)
  have ht := KernelDemand.tendsto_positive_part_integral (fun t => userProfileLaw (Γ t))
    (fun t => profileKernelDemand (Γ t) L) hI
    (tendsto_integral_profileKernelDemand_error Γ hn hM hroute hweak hL) hρ
  apply ht.congr
  intro t
  apply integral_congr_ae
  exact (ae_all_profile_bids_pos (Γ t) (hbid t)).mono fun d hd =>
    (profile_kernel_deficit (Γ t) hn (hcm t) hL d hd).symm

end FCAppendix.Bayes
