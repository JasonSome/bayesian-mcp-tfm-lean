import FCAppendix.PayOnce.ActiveEmpiricalCovariance
import FCAppendix.PayOnce.ActiveTypeStatistic
import FCAppendix.PayOnce.DummyCovarianceOrder

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory

theorem active_profile_success_dispersion_of_weak_zero
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1))
    (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    {g : ℝ} (hg : ∀ t, (Γ t).g = g) (hactive : F (Ioi g) ≠ 0)
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop
      (𝓝 (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ENNReal))) :
    let p := fun t => dummyProfileMarginal (Γ t) (by omega)
    let s := fun t (d : UserProfile (M t) (k+1)) i => if g < (d i).1.1 then (1:ℝ) else 0
    Tendsto (fun t => ∫ d, populationPairMean (fun i j => s t d i*s t d j*
      |success (k+1) (p t d i)-success (k+1) (p t d j)|) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  dsimp only
  have hm t := (hc t).trans (hcm t)
  let hn : 2 ≤ k+1 := by omega
  obtain ⟨bid,hmono,hmeas,_,heff,_,hbest,hpair⟩ :=
    exists_positive_success_equalization_of_weak_zero Γ hk hc hcm hA hG hu B hB hsym hvalue hinactive
      F hF hg hactive hweak
  have hpure t : ∀ᵐ v ∂F, g < v → ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid (k+1) (bid t v) :=
    (hbest t).mono fun _ hv hp => (hv hp).2
  let p := fun t => dummyProfileMarginal (Γ t) hn
  let A := fun t (d : UserProfile (M t) (k+1)) i => activeTypeStatistic g (d i).1.1
  let q := fun t d i => success (k+1) (p t d i)
  have hpm t i : Measurable (fun d => p t d i) := measurable_dummyProfileMarginal (Γ t) hn i
  have hqm t i : Measurable (fun d => q t d i) := (continuous_success (k+1)).measurable.comp (hpm t i)
  have ham t i : Measurable (fun d => A t d i) := (measurable_activeTypeStatistic g).comp
    (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))
  have hcov := tendsto_integral_active_profile_covariance_zero Γ hm hM F hF hg hactive
    boundedTypeStatistic boundedTypeStatistic_measurable boundedTypeStatistic_bounds bid hmeas hpure hpair
  have hmask (v : ℝ) : positiveMask (activeTypeStatistic g v) = (Ioi g).indicator (fun _ => (1:ℝ)) v := by
    simp only [positiveMask_activeTypeStatistic,indicator,mem_Ioi]
  have hprod (v : ℝ) : positiveMask (activeTypeStatistic g v)*activeTypeStatistic g v =
      activeTypeStatistic g v := by
    rw [positiveMask_activeTypeStatistic]
    by_cases hv : g < v
    · rw [if_pos hv,one_mul]
    · rw [if_neg hv,zero_mul,activeTypeStatistic,if_neg hv]
  have hstat (v : ℝ) : activeTypeStatistic g v = (Ioi g).indicator boundedTypeStatistic v := rfl
  have hcov' : Tendsto (fun t => ∫ d,
      populationMean (fun i => positiveMask (A t d i))*
        populationMean (fun i => positiveMask (A t d i)*A t d i*q t d i)-
      populationMean (fun i => positiveMask (A t d i)*A t d i)*
        populationMean (fun i => positiveMask (A t d i)*q t d i) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    apply hcov.congr
    intro t
    apply integral_congr_ae
    have hr := ae_positive_broadcast_or_abstain (Γ t) (hc t) (hcm t) (hA t) (hG t) (hu t)
      (B t) (hB t) (hsym t) (hvalue t) (hinactive t)
    have hbin := ae_profileCountLaw_eq_dummy_binomial (Γ t) hk (hA t) (B t) (hB t) (hsym t) hr
    filter_upwards [hbin] with d hd
    have he (i) : (profileCountLaw (Γ t) d i).success = q t d i := by
      rw [hd i,IndependentCounts.binomial_success]
      rfl
    simp only [profileWeightedCovariance,profileMeanType,profileWeightedSuccess,populationMean,
      Fintype.card_fin,A,he]
    simp_rw [hprod,hmask]
    simp only [hstat]
  let G := F.map (activeTypeStatistic g)
  haveI : IsProbabilityMeasure G := Measure.isProbabilityMeasure_map (measurable_activeTypeStatistic g).aemeasurable
  have hatom (b : ℝ) (hb : 0 < b) : G {b} = 0 :=
    activeTypeStatistic_map_positive_atomless F g (fun v hv => by
      have hh := hvalue 0 v (by simpa only [hg 0] using hv)
      simpa only [hF 0] using hh) hb
  have hgap := integral_positive_pair_gap_tendsto_zero (fun t => userProfileLaw (Γ t)) G hatom
    (by simpa using hm) A q ham hqm
    (fun t d i => activeTypeStatistic_bounds g (d i).1.1)
    (fun t d i => success_mem_unit (dummyProfileMarginal_bounds (Γ t) hn d i))
    (fun t => (ae_dummy_profile_success_coordered (Γ t) hn (bid t) (hmono t) (heff t)
      (activeTypeStatistic g) (activeTypeStatistic_monotone g)).mono fun d hd i j _ _ => hd i j)
    (fun t i j hij => by
      have hh := profile_type_pair_measurePreserving (Γ t) (activeTypeStatistic g) (measurable_activeTypeStatistic g) hij
      simpa only [hF t,G,A] using hh) hcov'
  simpa only [A,positiveMask_activeTypeStatistic,q,p] using hgap

end FCAppendix.Bayes
