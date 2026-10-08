import FCAppendix.PayOnce.EmpiricalDemand
import FCAppendix.PayOnce.ActiveProfileMeans

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Set Filter Topology Game CommonList
open PayOnce PayOnce.KernelTailEvent PayOnce.KernelLawConvergence PayOnce.CovarianceConcentration
open PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_drawEffectiveBid : Measurable (fun d : UserDraw n => effectiveBid d.1.2) :=
  (measurable_effectiveBid n).comp (measurable_snd.comp measurable_fst)

noncomputable def profileEffectiveKernelDemand (_Γ : FiniteGame m n c Seed) (L : ℝ)
    (d : UserProfile m n) : ℝ := populationMean (fun i => kernel n (effectiveBid (d i).1.2) L)

theorem measurable_profileEffectiveKernelDemand (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    {L : ℝ} (hL : 0 < L) : Measurable (profileEffectiveKernelDemand Γ L) :=
  (Finset.measurable_sum _ fun i _ => (continuous_kernel_bid hn hL).measurable.comp
    ((measurable_effectiveBid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))))).div_const _

theorem profile_effective_kernel_deficit (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    {L : ℝ} (hL : 0 < L) (d : UserProfile m n) :
    populationMean (fun i => max (kernel n (effectiveBid (d i).1.2) L-
      dummyProfileMarginal Γ hn d i) 0) =
      max (profileEffectiveKernelDemand Γ L d-populationMean (dummyProfileMarginal Γ hn d)) 0 := by
  obtain ⟨T,hT,hp,_⟩ := DummyKernel.profileMarginal_root (c := c) hn (fun i => effectiveBid (d i).1.2)
  have he := KernelDemand.sum_positive_kernel_deficit hn (fun i => effectiveBid (d i).1.2) hL hT
  have hpoint i : dummyProfileMarginal Γ hn d i = kernel n (effectiveBid (d i).1.2) T := hp i
  simp_rw [← hpoint] at he
  simp only [profileEffectiveKernelDemand,populationMean,Fintype.card_fin,he]
  rw [← sub_div]
  simpa only [zero_div] using (max_div_div_right (Nat.cast_nonneg m)
    ((∑ i, kernel n (effectiveBid (d i).1.2) L)-(∑ i,dummyProfileMarginal Γ hn d i)) 0).symm

theorem tendsto_effective_kernel_mean
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun t => ∫ d : UserDraw n, kernel n (effectiveBid d.1.2) L ∂userLaw (Γ t)) atTop
      (𝓝 (KernelDemand.demand n (G : Measure ENNReal) L)) := by
  let f : BoundedContinuousFunction ENNReal ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun b => compactKernel n b L,
    continuous_compactKernel hn hL⟩
  have he t : (∫ b, f b ∂(CompactifiedBidLaws.bidLaw (Γ t) : Measure ENNReal)) =
      ∫ d : UserDraw n, kernel n (effectiveBid d.1.2) L ∂userLaw (Γ t) := by
    change (∫ b, f b ∂(Measure.map (fun d : UserDraw n => ENNReal.ofReal (effectiveBid d.1.2))
      (userLaw (Γ t)))) = _
    rw [integral_map (show AEMeasurable (fun d : UserDraw n => ENNReal.ofReal (effectiveBid d.1.2)) (userLaw (Γ t)) from
      (ENNReal.measurable_ofReal.comp measurable_drawEffectiveBid).aemeasurable) f.continuous.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun d => by
      simp only [f,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
        compactKernel,ENNReal.ofReal_ne_top,if_false,ENNReal.toReal_ofReal (effectiveBid_nonneg d.1.2)]
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
  simp_rw [he] at hh
  exact hh

theorem tendsto_integral_profileEffectiveKernelDemand_error
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hM : Tendsto M atTop atTop)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun t => ∫ d, |profileEffectiveKernelDemand (Γ t) L d-
      KernelDemand.demand n (G : Measure ENNReal) L| ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  let a := fun t => ∫ d : UserDraw n, kernel n (effectiveBid d.1.2) L ∂userLaw (Γ t)
  have ha : Tendsto a atTop (𝓝 (KernelDemand.demand n (G : Measure ENNReal) L)) :=
    tendsto_effective_kernel_mean Γ hn hweak hL
  have ht := Probability.iid_empiricalMean_L1_tendsto_zero (fun t => userLaw (Γ t))
    (fun _ (d : UserDraw n) => kernel n (effectiveBid d.1.2) L)
    (fun _ => ((continuous_kernel_bid hn hL).measurable.comp measurable_drawEffectiveBid).aestronglyMeasurable)
    1 zero_le_one (fun _ => Eventually.of_forall fun d => by
      rw [abs_of_nonneg (kernel_unit_bounds hn hL (effectiveBid d.1.2)).1]
      exact (kernel_unit_bounds hn hL (effectiveBid d.1.2)).2) M hM
  have ht' : Tendsto (fun t => ∫ d, |profileEffectiveKernelDemand (Γ t) L d-a t| ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    simpa only [profileEffectiveKernelDemand, populationMean, Fintype.card_fin, userProfileLaw, a] using ht
  have hI t (r : ℝ) : Integrable (fun d => |profileEffectiveKernelDemand (Γ t) L d-r|) (userProfileLaw (Γ t)) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hL).measurable.comp
      ((measurable_effectiveBid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))))
      (fun d => (kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).1)
      (fun d => (kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).2)
  apply squeeze_zero (fun t => integral_nonneg fun _ => abs_nonneg _)
    (fun t => ?_) (show Tendsto (fun t => (∫ d, |profileEffectiveKernelDemand (Γ t) L d-a t| ∂userProfileLaw (Γ t))+
      |a t-KernelDemand.demand n (G : Measure ENNReal) L|) atTop (𝓝 0) from by
        simpa only [sub_self, abs_zero, add_zero] using ht'.add ((ha.sub_const (KernelDemand.demand n (G : Measure ENNReal) L)).abs))
  have hh := integral_mono (hI t (KernelDemand.demand n (G : Measure ENNReal) L))
    ((hI t (a t)).add (integrable_const |a t-KernelDemand.demand n (G : Measure ENNReal) L|))
    (fun d => abs_sub_le (profileEffectiveKernelDemand (Γ t) L d) (a t) (KernelDemand.demand n (G : Measure ENNReal) L))
  simpa only [Pi.add_apply, integral_add (hI t (a t)) (integrable_const _),
    integral_const, probReal_univ, one_smul] using hh

theorem tendsto_dummy_kernel_deficit_zero
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hM : Tendsto M atTop atTop)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G)) {ρ : ℝ}
    (hload : Tendsto (fun t => ∫ d, |populationMean (dummyProfileMarginal (Γ t) hn d)-ρ|
      ∂userProfileLaw (Γ t)) atTop (𝓝 0))
    {L : ℝ} (hL : 0 < L) (hD : KernelDemand.demand n (G : Measure ENNReal) L ≤ ρ) :
    Tendsto (fun t => ∫ d, populationMean (fun i => max (kernel n (effectiveBid (d i).1.2) L-
      dummyProfileMarginal (Γ t) hn d i) 0) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  let D := KernelDemand.demand n (G : Measure ENNReal) L
  let f := fun t (d : UserProfile (M t) n) i => max (kernel n (effectiveBid (d i).1.2) L-
    dummyProfileMarginal (Γ t) hn d i) 0
  have hfm t i : Measurable (fun d => f t d i) :=
    (((continuous_kernel_bid hn hL).measurable.comp (measurable_drawEffectiveBid.comp (measurable_pi_apply i))).sub
      (measurable_dummyProfileMarginal (Γ t) hn i)).max measurable_const
  have hfb t d i : f t d i ∈ Icc (0:ℝ) 1 := by
    refine ⟨le_max_right _ _,max_le ?_ zero_le_one⟩
    linarith [(kernel_unit_bounds hn hL (effectiveBid (d i).1.2)).2,
      (dummyProfileMarginal_bounds (Γ t) hn d i).1]
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
    rw [show populationMean (f t d) = max (profileEffectiveKernelDemand (Γ t) L d-
      populationMean (dummyProfileMarginal (Γ t) hn d)) 0 from profile_effective_kernel_deficit (Γ t) hn hL d]
    apply max_le
    · have h1 := le_abs_self (profileEffectiveKernelDemand (Γ t) L d-D)
      have h2 := neg_le_abs (populationMean (dummyProfileMarginal (Γ t) hn d)-ρ)
      change D ≤ ρ at hD
      linarith
    · exact add_nonneg (abs_nonneg _) (abs_nonneg _))
  simp only [Pi.add_apply] at hh
  rw [integral_add (hdi t) (hpi t)] at hh
  exact hh

theorem dummy_profile_marginal_mean_L1
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1))
    (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hvalue : ∀ t, PositiveValueAtomless (Γ t))
    (F : Measure ℝ) (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(M t)) atTop (𝓝 ρ))
    (hρπ : ρ ≤ F.real (Ioi g)) :
    Tendsto (fun t => ∫ d, |populationMean (dummyProfileMarginal (Γ t) (by omega) d)-ρ|
      ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  have hh := dummy_profile_mean_L1 Γ hk hc hcm hM hA hG hu B hB hsym hvalue F hF hg hρ hρπ
  apply hh.congr
  intro t
  apply integral_congr_ae
  filter_upwards [ae_dummy_marginal_active_capacity (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t)] with d hd
  rw [hg t] at hd
  simp only [hd.1]

end FCAppendix.Bayes
