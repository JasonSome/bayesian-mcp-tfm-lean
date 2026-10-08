import FCAppendix.PayOnce.EffectiveEmpiricalDemand
import FCAppendix.PayOnce.InactiveSaturatedBounds
import FCAppendix.PayOnce.EffectiveFocalTransport

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Set Filter Topology Game CommonList
open PayOnce PayOnce.KernelTailEvent PayOnce.KernelLawConvergence PayOnce.CovarianceConcentration
open PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem inactive_group_deficit_lower
    {k : ℕ} (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hvalue : PositiveValueAtomless Γ) (hatom : PositiveVisibleAtomless Γ)
    (hinactive : InactiveAbstain Γ) (i : Fin m)
    {L ε M : ℝ} (hL : 0 < L) (hε : 0 < ε) (hM : 0 ≤ M) (hnL : ((k+1:ℕ):ℝ)*L ≤ ε) :
    (ε/(ε+M*((k+1:ℕ):ℝ)^2)) * (Γ.F ⊗ₘ Γ.σ).real
      {x : ℝ × JointAction (k+1) | ε ≤ (effectiveBid x.2) ∧ x.1-Γ.g ≤ M} ≤
      ∫ d, max (kernel (k+1) (effectiveBid (d i).1.2) L-
        dummyProfileMarginal Γ (by omega) d i) 0 ∂userProfileLaw Γ := by
  classical
  let hn : 2 ≤ k+1 := by omega
  let E : Set (ℝ × JointAction (k+1)) := {x | ε ≤ (effectiveBid x.2) ∧ x.1-Γ.g ≤ M}
  let γ := ε/(ε+M*((k+1:ℕ):ℝ)^2)
  have hE : MeasurableSet E := (measurableSet_le measurable_const
    ((measurable_effectiveBid (k+1)).comp measurable_snd)).inter
    (measurableSet_le (measurable_fst.sub_const Γ.g) measurable_const)
  let p := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) =>
    DummyKernel.allocation (k+1) c hn z.2 (effectiveBid z.1.2)
  have hp : Measurable p := (DummyKernel.measurable_allocation_joint hn).comp
    ((((measurable_effectiveBid (k+1)).comp measurable_snd).comp measurable_fst).prodMk measurable_snd)
  have hpb z : p z ∈ Icc (0:ℝ) 1 := DummyKernel.allocation_bounds hn _ _
  let f := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) =>
    (Prod.fst ⁻¹' E).indicator (fun z => 1-p z) z
  have hf : Measurable f := (measurable_const.sub hp).indicator (measurable_fst hE)
  have hfb z : f z ∈ Icc (0:ℝ) 1 := by
    by_cases hz : z.1 ∈ E
    · simp only [f, indicator_of_mem (show z ∈ Prod.fst ⁻¹' E from hz)]
      exact ⟨sub_nonneg.mpr (hpb z).2, by linarith [(hpb z).1]⟩
    · simp only [f, indicator_of_notMem (show z ∉ Prod.fst ⁻¹' E from hz)]
      exact ⟨le_rfl, zero_le_one⟩
  have hfi := UnitInterval.integrable ((Γ.F ⊗ₘ Γ.σ).prod (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) f hf
    (fun z => (hfb z).1) (fun z => (hfb z).2)
  have hcond (x : ℝ × JointAction (k+1)) :
      (∫ r, f (x,r) ∂(Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) =
      E.indicator (fun x => 1-∫ r, p (x,r) ∂(Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) x := by
    by_cases hx : x ∈ E
    · have he : (fun r => f (x,r)) = fun r => 1-p (x,r) := by
        funext r
        exact indicator_of_mem (show (x,r) ∈ Prod.fst ⁻¹' E from hx) _
      have hpi : Integrable (fun r => p (x,r)) (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) :=
        UnitInterval.integrable _ _ (hp.comp (measurable_const.prodMk measurable_id))
          (fun r => (hpb (x,r)).1) (fun r => (hpb (x,r)).2)
      rw [he, indicator_of_mem hx, integral_sub (integrable_const _) hpi]
      simp only [integral_const, probReal_univ, one_smul]
    · have he : (fun r => f (x,r)) = 0 := by
        funext r
        exact indicator_of_notMem (show (x,r) ∉ Prod.fst ⁻¹' E from hx) _
      rw [he, indicator_of_notMem hx]
      exact integral_zero _ _
  have hlo : γ*(Γ.F ⊗ₘ Γ.σ).real E ≤ ∫ z, f z ∂((Γ.F ⊗ₘ Γ.σ).prod (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
    rw [integral_prod _ hfi]
    have hi := integral_mono_ae ((integrable_const γ).indicator hE) hfi.integral_prod_left
      ((ae_inactive_mean_marginal_bound Γ hk hc hcm hA hG hu B hB hsym hvalue hatom hinactive i hε hM).mono
        fun x hx => by
          change E.indicator (fun _ => γ) x ≤ ∫ r, f (x,r) ∂(Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))
          rw [hcond]
          by_cases he : x ∈ E
          · rw [indicator_of_mem he, indicator_of_mem he]
            exact RareSuccessSlope.gap_le_one_sub_of_mean_bound hε hM (hx he.1 he.2)
          · rw [indicator_of_notMem he, indicator_of_notMem he])
    simpa only [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_comm] using hi
  have hpres := focalAction_effectiveRivals_measurePreserving Γ i
  have he : (∫ d, f ((d i).1,effectiveRivalBids i d) ∂userProfileLaw Γ) =
      ∫ z, f z ∂((Γ.F ⊗ₘ Γ.σ).prod (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
    rw [← hpres.map_eq]
    exact (integral_map hpres.measurable.aemeasurable hf.aestronglyMeasurable).symm
  rw [← he] at hlo
  apply hlo.trans
  have htarget : Measurable (fun d => max (kernel (k+1) (effectiveBid (d i).1.2) L-
      dummyProfileMarginal Γ hn d i) 0) :=
    (((continuous_kernel_bid hn hL).measurable.comp ((measurable_effectiveBid (k+1)).comp
      (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))))).sub
      (measurable_dummyProfileMarginal Γ hn i)).max measurable_const
  have htargetb d : max (kernel (k+1) (effectiveBid (d i).1.2) L-
      dummyProfileMarginal Γ hn d i) 0 ∈ Icc (0:ℝ) 1 := by
    refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
    linarith [(kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).2,
      (dummyProfileMarginal_bounds Γ hn d i).1]
  apply integral_mono (UnitInterval.integrable _ _ (hf.comp hpres.measurable)
    (fun d => (hfb _).1) (fun d => (hfb _).2))
    (UnitInterval.integrable _ _ htarget (fun d => (htargetb d).1) (fun d => (htargetb d).2))
  intro d
  change f ((d i).1,effectiveRivalBids i d) ≤ max (kernel (k+1) (effectiveBid (d i).1.2) L-dummyProfileMarginal Γ hn d i) 0
  by_cases hd : (d i).1 ∈ E
  · rw [show f ((d i).1,effectiveRivalBids i d) = 1-dummyProfileMarginal Γ hn d i from
      indicator_of_mem (show ((d i).1,effectiveRivalBids i d) ∈ Prod.fst ⁻¹' E from hd) _]
    rw [kernel_of_ge (k+1) hn hL (hnL.trans hd.1)]
    exact le_max_left _ _
  · rw [show f ((d i).1,effectiveRivalBids i d) = 0 from
      indicator_of_notMem (show ((d i).1,effectiveRivalBids i d) ∉ Prod.fst ⁻¹' E from hd) _]
    exact le_max_right _ _

theorem inactive_group_average_deficit_lower
    {k : ℕ} (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hvalue : PositiveValueAtomless Γ) (hatom : PositiveVisibleAtomless Γ)
    (hinactive : InactiveAbstain Γ)
    {L ε M : ℝ} (hL : 0 < L) (hε : 0 < ε) (hM : 0 ≤ M) (hnL : ((k+1:ℕ):ℝ)*L ≤ ε) :
    (ε/(ε+M*((k+1:ℕ):ℝ)^2)) * (Γ.F ⊗ₘ Γ.σ).real
      {x : ℝ × JointAction (k+1) | ε ≤ (effectiveBid x.2) ∧ x.1-Γ.g ≤ M} ≤
      ∫ d, populationMean (fun i => max (kernel (k+1) (effectiveBid (d i).1.2) L-
        dummyProfileMarginal Γ (by omega) d i) 0) ∂userProfileLaw Γ := by
  have hn : 2 ≤ k+1 := by omega
  have hm : 0 < m := hc.trans hcm
  have hfi i : Integrable (fun d => max (kernel (k+1) (effectiveBid (d i).1.2) L-
      dummyProfileMarginal Γ hn d i) 0) (userProfileLaw Γ) := by
    apply UnitInterval.integrable _ _
      ((((continuous_kernel_bid hn hL).measurable.comp ((measurable_effectiveBid (k+1)).comp
        (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))))).sub
        (measurable_dummyProfileMarginal Γ hn i)).max measurable_const)
    · exact fun _ => le_max_right _ _
    · intro d
      change max (kernel (k+1) (effectiveBid (d i).1.2) L-dummyProfileMarginal Γ hn d i) 0 ≤ 1
      apply max_le _ zero_le_one
      linarith [(kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).2,
        (dummyProfileMarginal_bounds Γ hn d i).1]
  rw [integral_populationMean _ _ hfi]
  have hh := div_le_div_of_nonneg_right (Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    inactive_group_deficit_lower Γ hk hc hcm hA hG hu B hB hsym hvalue hatom hinactive i hL hε hM hnL)
    (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel_left₀ _ (by exact_mod_cast hm.ne' : (m:ℝ) ≠ 0), populationMean] using hh

theorem tendsto_inactive_saturated_group_mass_zero
    {M C : ℕ → ℕ} {k : ℕ} (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {ρ : ℝ} (hload : Tendsto (fun t => ∫ d, |populationMean (dummyProfileMarginal (Γ t) (by omega) d)-ρ|
      ∂userProfileLaw (Γ t)) atTop (𝓝 0))
    {L ε R : ℝ} (hL : 0 < L) (hε : 0 < ε) (hR : 0 ≤ R) (hnL : ((k+1:ℕ):ℝ)*L ≤ ε)
    (hD : KernelDemand.demand (k+1) (G : Measure ENNReal) L ≤ ρ) :
    Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ).real
      {x : ℝ × JointAction (k+1) | ε ≤ (effectiveBid x.2) ∧ x.1-(Γ t).g ≤ R}) atTop (𝓝 0) := by
  have hγ := RareSuccessSlope.saturation_gap_pos (n := k+1) hε hR
  have hzero := tendsto_dummy_kernel_deficit_zero Γ (by omega) hM hweak hload hL hD
  have hbound := hzero.div_const (ε/(ε+R*((k+1:ℕ):ℝ)^2))
  simp only [zero_div] at hbound
  apply squeeze_zero (fun t => measureReal_nonneg) _ hbound
  intro t
  apply (le_div_iff₀ hγ).mpr
  simpa only [mul_comm] using inactive_group_average_deficit_lower (Γ t) hk (hc t) (hcm t)
    (hA t) (hG t) (hu t) (B t) (hB t) (hsym t) (hvalue t) (hatom t) (hinactive t) hL hε hR hnL

end FCAppendix.Bayes
