import FCAppendix.PayOnce.ActiveProfileMeans
import FCAppendix.PayOnce.ActiveProfileConcentration
import FCAppendix.PayOnce.ActiveMarginalConcentration
import FCAppendix.PayOnce.ActiveCentering

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory

theorem active_profile_allocation_concentration_of_weak_zero
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
    {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g)))
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop
      (𝓝 (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ENNReal))) :
    Tendsto (fun t => ∫ d, populationMean (fun i => (if g < (d i).1.1 then (1:ℝ) else 0)*
      |dummyProfileMarginal (Γ t) (by omega) d i-ρ/F.real (Ioi g)|) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  have hm t := (hc t).trans (hcm t)
  let hn : 2 ≤ k+1 := by omega
  have hπ : 0 < F.real (Ioi g) := hρb.1.trans hρb.2
  have hactive : F (Ioi g) ≠ 0 := (ENNReal.toReal_pos_iff.mp hπ).1.ne'
  have hr : ρ/F.real (Ioi g) ∈ Icc (0:ℝ) 1 :=
    ⟨(div_pos hρb.1 hπ).le,((div_lt_one hπ).mpr hρb.2).le⟩
  let p := fun t => dummyProfileMarginal (Γ t) hn
  let A := fun t (d : UserProfile (M t) (k+1)) i => activeTypeStatistic g (d i).1.1
  let s := fun t (d : UserProfile (M t) (k+1)) i => if g < (d i).1.1 then (1:ℝ) else 0
  have hpm t i : Measurable (fun d => p t d i) := measurable_dummyProfileMarginal (Γ t) hn i
  have ham t i : Measurable (fun d => A t d i) := (measurable_activeTypeStatistic g).comp
    (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))
  have hsm t i : Measurable (fun d => s t d i) := by
    simpa only [Function.comp_def,A,positiveMask_activeTypeStatistic,s] using measurable_positiveMask.comp (ham t i)
  have hsb t d i : s t d i ∈ Icc (0:ℝ) 1 := by
    dsimp only [s]
    split_ifs <;> constructor <;> norm_num
  have hgap := active_profile_success_dispersion_of_weak_zero Γ hk hc hcm hM hA hG hu B hB hsym hvalue
    hinactive F hF hg hactive hweak
  have hmgap := integral_positive_pair_marginal_gap_tendsto_zero (fun t => userProfileLaw (Γ t))
    (by omega : 0 < k+1) (by simpa using hm) A p ham hpm
    (fun t d i => dummyProfileMarginal_bounds (Γ t) hn d i)
    (by simpa only [A,positiveMask_activeTypeStatistic,p] using hgap)
  have hpair : Tendsto (fun t => ∫ d, populationPairMean
      (fun i j => s t d i*s t d j*|p t d i-p t d j|) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    simpa only [A,positiveMask_activeTypeStatistic,s] using hmgap
  have hfrac := active_profile_fraction_L1 Γ hm hM F hF g
  have hload := dummy_profile_mean_L1 Γ hk hc hcm hM hA hG hu B hB hsym hvalue F hF hg hρ hρb.2.le
  exact integral_active_distance_tendsto_zero (fun t => userProfileLaw (Γ t)) (by simpa using hm)
    s p hsm hpm hsb (fun t d i => dummyProfileMarginal_bounds (Γ t) hn d i) hπ hr hfrac hload hpair

end FCAppendix.Bayes
