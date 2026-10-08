import FCAppendix.PayOnce.PositiveRoot

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory Set Filter Topology CommonList KernelTailEvent KernelLawConvergence
open scoped BigOperators

theorem sum_abs_kernel_difference {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 2 ≤ n) (b : ι → ℝ) {L T : ℝ} (hL : 0 < L) (hT : 0 < T) :
    (∑ i, |kernel n (b i) L-kernel n (b i) T|) =
      |(∑ i, kernel n (b i) L)-(∑ i, kernel n (b i) T)| := by
  rcases le_total L T with h | h
  · have hh i := kernel_antitone_price hn (b := b i) hL hT h
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (hh _))]
    rw [Finset.sum_sub_distrib, abs_of_nonneg (sub_nonneg.mpr (Finset.sum_le_sum fun i _ => hh i))]
  · have hh i := kernel_antitone_price hn (b := b i) hT hL h
    simp_rw [abs_of_nonpos (sub_nonpos.mpr (hh _))]
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib,
      abs_of_nonpos (sub_nonpos.mpr (Finset.sum_le_sum fun i _ => hh i))]

end FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Set Filter Topology Game CommonList
open PayOnce PayOnce.KernelTailEvent PayOnce.KernelLawConvergence PayOnce.CovarianceConcentration
open scoped BigOperators ProbabilityTheory
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem profile_kernel_distance (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    (hcm : c ≤ m) {L : ℝ} (hL : 0 < L)
    (d : UserProfile m n) (hpos : ∀ i, 0 < (d i).1.2.bid) :
    populationMean (fun i => |kernel n (d i).1.2.bid L-
      analyticalProfileMarginal Γ hn hcm d i|) = |profileKernelDemand Γ L d-(c:ℝ)/m| := by
  obtain ⟨T,hT,hp,hcap⟩ := exists_common_profile_root Γ hn hcm d hpos
  have he := KernelDemand.sum_abs_kernel_difference hn (fun i => (d i).1.2.bid) hL hT
  simp_rw [← hp] at he
  rw [hcap] at he
  simp only [profileKernelDemand, populationMean, Fintype.card_fin, he]
  rw [← sub_div, abs_div]
  simp only [abs_of_nonneg (show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m)]

theorem tendsto_actual_kernel_distance_zero
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hcm : ∀ t, C t ≤ M t)
    (hM : Tendsto M atTop atTop)
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = n)
    (hbid : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    {L : ℝ} (hL : 0 < L) (hD : KernelDemand.demand n (G : Measure ENNReal) L = ρ) :
    Tendsto (fun t => ∫ d, populationMean (fun i => |kernel n (d i).1.2.bid L-
      analyticalProfileMarginal (Γ t) hn (hcm t) d i|) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  have he t : (∫ d, populationMean (fun i => |kernel n (d i).1.2.bid L-
      analyticalProfileMarginal (Γ t) hn (hcm t) d i|) ∂userProfileLaw (Γ t)) =
      ∫ d, |profileKernelDemand (Γ t) L d-(C t:ℝ)/(M t)| ∂userProfileLaw (Γ t) := by
    apply integral_congr_ae
    exact (ae_all_profile_bids_pos (Γ t) (hbid t)).mono fun d hd =>
      profile_kernel_distance (Γ t) hn (hcm t) hL d hd
  simp_rw [he]
  have hI t (r : ℝ) : Integrable (fun d => |profileKernelDemand (Γ t) L d-r|) (userProfileLaw (Γ t)) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hL).measurable.comp
      ((measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))))
      (fun d => (kernel_unit_bounds hn hL (d i).1.2.bid).1)
      (fun d => (kernel_unit_bounds hn hL (d i).1.2.bid).2)
  have ht := tendsto_integral_profileKernelDemand_error Γ hn hM hroute hweak hL
  rw [hD] at ht
  have hu : Tendsto (fun t => (∫ d, |profileKernelDemand (Γ t) L d-ρ| ∂userProfileLaw (Γ t))+
      |ρ-(C t:ℝ)/(M t)|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, add_zero] using ht.add (((tendsto_const_nhds (x := ρ)).sub hρ).abs)
  apply squeeze_zero (fun t => integral_nonneg fun _ => abs_nonneg _) _ hu
  intro t
  have hh := integral_mono (hI t ((C t:ℝ)/(M t)))
    ((hI t ρ).add (integrable_const |ρ-(C t:ℝ)/(M t)|))
    (fun d => abs_sub_le (profileKernelDemand (Γ t) L d) ρ ((C t:ℝ)/(M t)))
  simpa only [Pi.add_apply, integral_add (hI t ρ) (integrable_const _), integral_const,
    probReal_univ, one_smul] using hh

theorem payOnce_price_allocation_limit
    {M C : ℕ → ℕ} {k : ℕ}
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) 1) {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G)) :
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G : Measure ENNReal) L = ρ ∧
      Tendsto (fun t => ∫ d, populationMean (fun i => |kernel (k+1) (d i).1.2.bid L-
        analyticalProfileMarginal (Γ t) (by omega) (hcm t).le d i|) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  obtain ⟨_,L,hL,huniq⟩ := payOnce_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak
  refine ⟨L,⟨hL.1,hL.2,?_⟩,fun T hT => huniq T ⟨hT.1,hT.2.1⟩⟩
  have hv t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hv t) (by simpa only [hF t,hg t] using hactive)
  exact tendsto_actual_kernel_distance_zero Γ (by omega) (fun t => (hcm t).le) hM
    (fun t => (hfull t).mono fun _ hx => hx.2) (fun t => (hfull t).mono fun _ hx => hx.1) hweak hρ hL.1 hL.2

end FCAppendix.Bayes
