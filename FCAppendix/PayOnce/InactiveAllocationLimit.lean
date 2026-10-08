import FCAppendix.PayOnce.AllocationLimit
import FCAppendix.PayOnce.InactivePositiveRoot

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Set Filter Topology Game CommonList
open PayOnce PayOnce.KernelTailEvent PayOnce.KernelLawConvergence PayOnce.CovarianceConcentration
open PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem profile_effective_kernel_distance (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    {L : ℝ} (hL : 0 < L) (d : UserProfile m n) :
    populationMean (fun i => |kernel n (effectiveBid (d i).1.2) L-
      dummyProfileMarginal Γ hn d i|) =
      |profileEffectiveKernelDemand Γ L d-populationMean (dummyProfileMarginal Γ hn d)| := by
  obtain ⟨T,hT,hp,_⟩ := DummyKernel.profileMarginal_root (c := c) hn (fun i => effectiveBid (d i).1.2)
  have he := KernelDemand.sum_abs_kernel_difference hn (fun i => effectiveBid (d i).1.2) hL hT
  have hpoint i : dummyProfileMarginal Γ hn d i = kernel n (effectiveBid (d i).1.2) T := hp i
  simp_rw [← hpoint] at he
  simp only [profileEffectiveKernelDemand,populationMean,Fintype.card_fin,he]
  rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m)]

theorem tendsto_dummy_kernel_distance_zero
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hM : Tendsto M atTop atTop)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G)) {ρ : ℝ}
    (hload : Tendsto (fun t => ∫ d, |populationMean (dummyProfileMarginal (Γ t) hn d)-ρ|
      ∂userProfileLaw (Γ t)) atTop (𝓝 0))
    {L : ℝ} (hL : 0 < L) (hD : KernelDemand.demand n (G : Measure ENNReal) L = ρ) :
    Tendsto (fun t => ∫ d, populationMean (fun i => |kernel n (effectiveBid (d i).1.2) L-
      dummyProfileMarginal (Γ t) hn d i|) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  let D := KernelDemand.demand n (G : Measure ENNReal) L
  let f := fun t (d : UserProfile (M t) n) i => |kernel n (effectiveBid (d i).1.2) L-
    dummyProfileMarginal (Γ t) hn d i|
  have hfm t i : Measurable (fun d => f t d i) :=
    (((continuous_kernel_bid hn hL).measurable.comp (measurable_drawEffectiveBid.comp (measurable_pi_apply i))).sub
      (measurable_dummyProfileMarginal (Γ t) hn i)).abs
  have hfb t d i : f t d i ∈ Icc (0:ℝ) 1 := by
    refine ⟨abs_nonneg _,abs_le.mpr ⟨?_,?_⟩⟩ <;>
      linarith [(kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).1,
        (kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).2,
        (dummyProfileMarginal_bounds (Γ t) hn d i).1,(dummyProfileMarginal_bounds (Γ t) hn d i).2]
  have hfi t : Integrable (fun d => populationMean (f t d)) (userProfileLaw (Γ t)) :=
    (integrable_finsetSum _ (fun i _ => UnitInterval.integrable _ _ (hfm t i)
      (fun d => (hfb t d i).1) (fun d => (hfb t d i).2))).div_const _
  have hdi t : Integrable (fun d => |profileEffectiveKernelDemand (Γ t) L d-D|) (userProfileLaw (Γ t)) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hL).measurable.comp
      (measurable_drawEffectiveBid.comp (measurable_pi_apply i)))
      (fun d => (kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).1)
      (fun d => (kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).2)
  have hpi t : Integrable (fun d => |populationMean (dummyProfileMarginal (Γ t) hn d)-ρ|) (userProfileLaw (Γ t)) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ (measurable_dummyProfileMarginal (Γ t) hn i)
      (fun d => (dummyProfileMarginal_bounds (Γ t) hn d i).1)
      (fun d => (dummyProfileMarginal_bounds (Γ t) hn d i).2)
  have ht : Tendsto (fun t => (∫ d, |profileEffectiveKernelDemand (Γ t) L d-D| ∂userProfileLaw (Γ t))+
      ∫ d, |populationMean (dummyProfileMarginal (Γ t) hn d)-ρ| ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    simpa only [add_zero] using (tendsto_integral_profileEffectiveKernelDemand_error Γ hn hM hweak hL).add hload
  apply squeeze_zero (fun t => integral_nonneg fun d => div_nonneg
    (Finset.sum_nonneg fun i _ => (hfb t d i).1) (Nat.cast_nonneg _)) _ ht
  intro t
  have hh := integral_mono (hfi t) ((hdi t).add (hpi t)) (fun d => by
    change populationMean (f t d) ≤ |profileEffectiveKernelDemand (Γ t) L d-D|+
      |populationMean (dummyProfileMarginal (Γ t) hn d)-ρ|
    rw [show populationMean (f t d) = |profileEffectiveKernelDemand (Γ t) L d-
      populationMean (dummyProfileMarginal (Γ t) hn d)| from profile_effective_kernel_distance (Γ t) hn hL d]
    have htri := abs_sub_le (profileEffectiveKernelDemand (Γ t) L d) D
      (populationMean (dummyProfileMarginal (Γ t) hn d))
    change D = ρ at hD
    rw [hD] at htri ⊢
    simpa only [abs_sub_comm ρ] using htri)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hdi t) (hpi t)] at hh
  exact hh

theorem payOnce_inactive_price_allocation_limit
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G)) :
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G : Measure ENNReal) L = ρ ∧
      Tendsto (fun t => ∫ d, populationMean (fun i => |kernel (k+1) (effectiveBid (d i).1.2) L-
        dummyProfileMarginal (Γ t) (by omega) d i|) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  obtain ⟨_,L,hL,huniq⟩ := payOnce_inactive_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym
    hvalue hatom hinactive F hF hg hρ hρb hweak
  refine ⟨L,⟨hL.1,hL.2,?_⟩,fun T hT => huniq T ⟨hT.1,hT.2.1⟩⟩
  exact tendsto_dummy_kernel_distance_zero Γ (by omega) hM hweak
    (dummy_profile_marginal_mean_L1 Γ hk hc hcm hM hA hG hu B hB hsym hvalue F hF hg hρ hρb.2.le) hL.1 hL.2

end FCAppendix.Bayes
