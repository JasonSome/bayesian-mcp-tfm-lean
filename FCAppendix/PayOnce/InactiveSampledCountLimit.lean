import FCAppendix.PayOnce.DummyProfileTestLimit
import FCAppendix.PayOnce.InactiveFullSequenceAllocation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CovarianceConcentration
open scoped BigOperators
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_sampled_count_limit
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      ∀ j : ℕ, Tendsto (fun t => ∫ d, populationMean (fun i =>
        (profileCountLaw (Γ t) d i).prob (fun r => r.val = j)) ∂userProfileLaw (Γ t)) atTop
          (𝓝 (∫ v, ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) j ∂F)) := by
  obtain ⟨hL,hd,hgap⟩ := payOnce_inactive_profile_marginal_limit Γ hk hc hcm hN hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρ hρb
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hroute t := ae_positive_broadcast_or_abstain (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (hinactive t)
  have hlaw t := ae_profileCountLaw_eq_dummy_binomial (Γ t) hk (hA t) (B t) (hB t) (hsym t)
    (hroute t)
  refine ⟨hL,hd,?_⟩
  intro j
  have ht := dummy_profile_test_limit_of_marginal_gap Γ (by omega) (fun t => by omega)
    F hF hL hgap (fun p => ManyProposers.binomialMass (k+1) p j)
    (ManyProposers.continuous_binomialMass (k+1) j)
    (fun _ hp => ManyProposers.binomialMass_bounds (k+1) j hp)
    (fun _ hp _ hq => ManyProposers.binomialMass_abs_sub_le (k+1) j hp hq)
  apply ht.congr
  intro t
  apply integral_congr_ae
  filter_upwards [hlaw t] with d hd
  simp only [hd,ManyProposers.binomial_prob_eq_binomialMass,dummyProfileMarginal]

end FCAppendix.Bayes
