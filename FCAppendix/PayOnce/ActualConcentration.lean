import FCAppendix.PayOnce.ProfileConcentration
import FCAppendix.PayOnce.ProfileCovarianceOrder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration
open scoped BigOperators ProbabilityTheory

noncomputable def boundedTypeStatistic (v : ℝ) : ℝ := Real.arctan v / Real.pi + 1/2

theorem boundedTypeStatistic_strictMono : StrictMono boundedTypeStatistic := by
  intro x y hxy
  exact add_lt_add_left (div_lt_div_of_pos_right (Real.arctan_strictMono hxy) Real.pi_pos) _

theorem boundedTypeStatistic_measurable : Measurable boundedTypeStatistic :=
  ((Real.continuous_arctan.div_const Real.pi).add_const (1/2)).measurable

theorem boundedTypeStatistic_bounds (v : ℝ) : boundedTypeStatistic v ∈ Icc (0 : ℝ) 1 := by
  have h1 := (div_lt_div_of_pos_right (Real.neg_pi_div_two_lt_arctan v) Real.pi_pos)
  have h2 := (div_lt_div_of_pos_right (Real.arctan_lt_pi_div_two v) Real.pi_pos)
  have he1 : -(Real.pi/2)/Real.pi = -(1/2 : ℝ) := by field_simp
  have he2 : (Real.pi/2)/Real.pi = (1/2 : ℝ) := by field_simp
  rw [he1] at h1
  rw [he2] at h2
  constructor <;> dsimp only [boundedTypeStatistic] <;> linarith

theorem boundedTypeStatistic_map_atomless (F : Measure ℝ) [NullSingletonClass F] :
    NullSingletonClass (F.map boundedTypeStatistic) := by
  refine ⟨fun x => ?_⟩
  rw [Measure.map_apply boundedTypeStatistic_measurable (measurableSet_singleton x)]
  exact (Set.subsingleton_singleton.preimage boundedTypeStatistic_strictMono.injective).measure_zero F

theorem actual_profile_concentration_of_success_equalization
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hm : ∀ t, 0 < M t) (hcm : ∀ t, C t ≤ M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1))
    (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F)
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = k+1)
    (hbid : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid)
    (bid : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (bid t)) (hpos : ∀ t v, 0 ≤ bid t v)
    (hpure : ∀ t, ∀ᵐ v ∂F, ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid (k+1) (bid t v))
    (hpair : ∀ᵐ z ∂F.prod F, Tendsto (fun t =>
      averageTypeSuccess (Γ t) (bid t) z.2-averageTypeSuccess (Γ t) (bid t) z.1)
      atTop (𝓝 0))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ)) :
    Tendsto (fun t => ∫ d, populationMean (fun i =>
      |analyticalProfileMarginal (Γ t) (by omega) (hcm t) d i-ρ|) ∂userProfileLaw (Γ t))
      atTop (𝓝 0) := by
  let p := fun t => analyticalProfileMarginal (Γ t) (by omega) (hcm t)
  let A := fun t (d : UserProfile (M t) (k+1)) i => boundedTypeStatistic (d i).1.1
  let q := fun t d i => success (k+1) (p t d i)
  have hpm t i : Measurable (fun d => p t d i) := measurable_analyticalProfileMarginal (Γ t) _ _ i
  have hqm t i : Measurable (fun d => q t d i) := (continuous_success (k+1)).measurable.comp (hpm t i)
  have ham t i : Measurable (fun d => A t d i) := boundedTypeStatistic_measurable.comp
    (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))
  have hp' t : ∀ᵐ v ∂(Γ t).F, ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid (k+1) (bid t v) := by
    simpa only [hF t] using hpure t
  have hcov := tendsto_integral_profileTypeCovariance_zero Γ hm hM F hF boundedTypeStatistic
    boundedTypeStatistic_measurable boundedTypeStatistic_bounds bid (fun t => (hmono t).measurable) hpure hpair
  have hcov' : Tendsto (fun t => ∫ d, populationMean (fun i => A t d i*q t d i)-
      populationMean (A t d)*populationMean (q t d) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    apply hcov.congr
    intro t
    apply integral_congr_ae
    have hs := ae_all_iff.mpr (fun i => ae_profile_success_eq_analytical (Γ t) hk (hcm t)
      (hA t) (B t) (hB t) (hsym t) (hroute t) (hbid t) i)
    filter_upwards [hs] with d hd
    simp only [profileTypeCovariance, profileWeightedSuccess, profileMeanType, profileCoverage,
      populationMean, Fintype.card_fin, A, q, p, hd, analyticalProfileMarginal]
  let G := F.map boundedTypeStatistic
  haveI : IsProbabilityMeasure G := Measure.isProbabilityMeasure_map boundedTypeStatistic_measurable.aemeasurable
  haveI : NullSingletonClass G := boundedTypeStatistic_map_atomless F
  have hgap := integral_pair_gap_tendsto_zero (fun t => userProfileLaw (Γ t)) G
    (by simpa using hm) A q ham hqm (fun t d i => boundedTypeStatistic_bounds _)
    (fun t d i => success_mem_unit (analyticalProfileMarginal_bounds (Γ t) _ _ d i))
    (fun t => ae_profile_success_coordered (Γ t) (by omega) (hcm t) (hbid t) (bid t)
      (hmono t) (hpos t) (hp' t) boundedTypeStatistic boundedTypeStatistic_strictMono.monotone)
    (fun t i j hij => by
      have hh := profile_type_pair_measurePreserving (Γ t) boundedTypeStatistic boundedTypeStatistic_measurable hij
      simpa only [hF t, G, A] using hh) hcov'
  have hmgap := integral_pair_marginal_gap_tendsto_zero (fun t => userProfileLaw (Γ t))
    (by omega : 0 < k+1) (by simpa using hm) p hpm
    (fun t d i => analyticalProfileMarginal_bounds (Γ t) _ _ d i) hgap
  apply integral_distance_to_capacity_tendsto_zero (fun t => userProfileLaw (Γ t))
    (by simpa using hm) p hpm (fun t d i => analyticalProfileMarginal_bounds (Γ t) _ _ d i)
    (fun t => (C t : ℝ)/(M t)) hρ _ hmgap
  intro t
  filter_upwards [ae_all_profile_bids_pos (Γ t) (hbid t)] with d hd
  obtain ⟨_, _, _, hcap⟩ := exists_common_profile_root (Γ t) (by omega) (hcm t) d hd
  simpa only [p, Fintype.card_fin, mul_div_cancel₀ _ (by exact_mod_cast (hm t).ne' : (M t : ℝ) ≠ 0)] using hcap

theorem actual_profile_concentration_of_weak_zero
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1))
    (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop
      (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ENNReal)))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ)) :
    Tendsto (fun t => ∫ d, populationMean (fun i =>
      |analyticalProfileMarginal (Γ t) (by omega) (hcm t).le d i-ρ|) ∂userProfileLaw (Γ t))
      atTop (𝓝 0) := by
  have hv t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have ha t : ∀ᵐ v ∂(Γ t).F, (Γ t).g < v := by simpa only [hF t, hg t] using hactive
  choose bid hmono hmeas hbound hprop using fun t =>
    exists_monotone_bid_bestResponse_all (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hv t) (ha t)
  have hpure t : ∀ᵐ v ∂(Γ t).F, ∀ᵐ a ∂(Γ t).σ v,
      a = safeFullBid (k+1) (bid t v) := (hprop t).mono fun _ hx => hx.2.2.2
  have hroute t : ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = k+1 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun ((measurable_routeCount (k+1)).comp measurable_snd) measurable_const)
    filter_upwards [hpure t] with v hvi
    filter_upwards [hvi] with a hai
    simp only [hai, safeFullBid, fullBid, Function.comp_apply]
  have hbid t : ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_lt measurable_const ((measurable_bid (k+1)).comp measurable_snd))
    filter_upwards [hprop t] with v hvi
    filter_upwards [hvi.2.2.2] with a hai
    simp only [hai, safeFullBid, fullBid, max_eq_left (hbound t v).1]
    exact hvi.1
  have hzero := VanishingBidIC.ae_bid_zero_of_actual_weak_zero Γ (by omega) F hF bid
    hmono (fun t v => (hbound t v).1) hpure hroute hweak
  have hpair := ae_pair_average_success_gap_zero Γ (fun t => (hc t).trans (hcm t)) hA hG F hg
    hactive bid (fun t v => (hbound t v).1) (fun t => by
      rw [← hF t]
      exact (hprop t).mono fun _ hx => hx.2.2.1) hzero
  exact actual_profile_concentration_of_success_equalization Γ hk (fun t => (hc t).trans (hcm t))
    (fun t => (hcm t).le) hM hA B hB hsym F hF hroute hbid bid hmono
    (fun t v => (hbound t v).1) (fun t => by simpa only [hF t] using hpure t) hpair hρ

end FCAppendix.Bayes
