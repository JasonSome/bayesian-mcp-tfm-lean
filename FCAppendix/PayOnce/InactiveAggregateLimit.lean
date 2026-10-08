import FCAppendix.PayOnce.InactiveLoadLimit
import FCAppendix.PayOnce.DummyProfileTestLimit
import FCAppendix.PayOnce.InactiveFullSequenceAllocation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CovarianceConcentration
open scoped BigOperators
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_aggregate_limit
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
      0 < Limit.coverage μW (k+1) L ∧
      Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (Limit.coverage μW (k+1) L)) ∧
      Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 ((k+1:ℕ)*ρ)) ∧
      Tendsto (fun t => finiteMultiplicity (Γ t)) atTop
        (𝓝 (((k+1:ℕ):ℝ)*ρ/Limit.coverage μW (k+1) L)) ∧
      1 < ((k+1:ℕ):ℝ)*ρ/Limit.coverage μW (k+1) L := by
  obtain ⟨hL,hd,hgap⟩ := payOnce_inactive_profile_marginal_limit Γ hk hc hcm hN hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρ hρb
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) := (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hroute t := ae_positive_broadcast_or_abstain (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (hinactive t)
  have hlaw t := ae_profileCountLaw_eq_dummy_binomial (Γ t) hk (hA t) (B t) (hB t) (hsym t)
    (hroute t)
  have hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (Limit.coverage μW (k+1) L)) := by
    have ht := dummy_profile_test_limit_of_marginal_gap Γ (by omega) (fun t => by omega)
      F hF hL hgap (success (k+1)) (continuous_success (k+1))
      (fun _ hp => success_mem_unit hp) (fun _ hp _ hq => OwnImpact.success_abs_sub_le (k+1) hp hq)
    have he : (∫ v, success (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) ∂F) = Limit.coverage μW (k+1) L := by
      unfold Limit.coverage
      exact (integral_map hnet.aemeasurable
        ((continuous_success (k+1)).comp (Limit.continuous_pStar (by omega) hL)).aestronglyMeasurable).symm
    rw [he] at ht
    apply ht.congr
    intro t
    apply integral_congr_ae
    filter_upwards [hlaw t] with d hd
    simp only [profileCoverage,populationMean,Fintype.card_fin,hd,IndependentCounts.binomial_success,success,dummyProfileMarginal]
  have hloadlim : Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (((k+1:ℕ):ℝ)*ρ)) :=
    payOnce_inactive_load_limit Γ hk hc hcm ((tendsto_add_atTop_nat 1).comp hN)
      hA hG hu B hB hsym hvalue hinactive F hF hg
      (by simpa only [Nat.cast_add,Nat.cast_one] using hρ) hρb.2
  have hQpos : 0 < Limit.coverage μW (k+1) L :=
    hρb.1.trans_le (by rw [← hd]; exact Limit.demand_le_coverage μW (by omega) hL.le)
  have hstrict : 1 < ((k+1:ℕ):ℝ)*ρ/Limit.coverage μW (k+1) L :=
    (one_lt_div hQpos).mpr (Limit.coverage_lt_capacity μW (by omega) hL.le hρb.1 hd)
  exact ⟨hL,hd,hQpos,hQ,hloadlim,hloadlim.div hQ hQpos.ne',hstrict⟩

end FCAppendix.Bayes
