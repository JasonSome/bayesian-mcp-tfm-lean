import FCAppendix.PayOnce.ProfileTestLimit

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CovarianceConcentration
open scoped BigOperators
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_sampled_count_limit
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) 1) :
    let μW := F.map (fun v => v-g)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      ∀ j : ℕ, Tendsto (fun t => ∫ d, populationMean (fun i =>
        (profileCountLaw (Γ t) d i).prob (fun r => r.val = j)) ∂userProfileLaw (Γ t)) atTop
          (𝓝 (∫ v, ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (v-g)) j ∂F)) := by
  obtain ⟨hL,hd,hgap⟩ := payOnce_profile_marginal_limit Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb
  let L := Limit.capRoot (F.map (fun v => v-g)) (k+1) ρ
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t,hg t] using hactive)
  have hlaw t := ae_profileCountLaw_eq_binomial (Γ t) hk (hcm t).le (hA t) (B t) (hB t) (hsym t)
    ((hfull t).mono fun _ hz => hz.2) ((hfull t).mono fun _ hz => hz.1)
  refine ⟨hL,hd,?_⟩
  intro j
  have ht := profile_test_limit_of_marginal_gap Γ (by omega) (fun t => by omega) (fun t => (hcm t).le)
    F hF hL hgap (fun p => ManyProposers.binomialMass (k+1) p j)
    (ManyProposers.continuous_binomialMass (k+1) j)
    (fun _ hp => ManyProposers.binomialMass_bounds (k+1) j hp)
    (fun _ hp _ hq => ManyProposers.binomialMass_abs_sub_le (k+1) j hp hq)
  apply ht.congr
  intro t
  apply integral_congr_ae
  filter_upwards [hlaw t] with d hd
  simp only [hd,ManyProposers.binomial_prob_eq_binomialMass]

end FCAppendix.Bayes
