import FCAppendix.Ample.RankCompactness
import FCAppendix.Ample.CommonDeficitRate
import FCAppendix.Ample.RankSourceParticipation
import FCAppendix.Ample.RankUsedRate
import FCAppendix.Ample.RankGapExhaustion

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
namespace FreeBaseAmpleSequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
    {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g rho : ℝ}
    (h : FreeBaseAmpleSequence M C Γ B F g rho)
    {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)

include h in
private theorem rank_participation :
    (∀ᶠ t in atTop, positiveRouteMass (Γ t) (fun _ => True) = F.real (Ioi g)) ∧
    (∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      0 < x.2.routeCount → 0 < x.2.bid) ∧
    (∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      (0 < x.2.bid ∧ 0 < x.2.routeCount) ↔ (Γ t).g < x.1) := by
  exact actual_rank_participation Γ F g h.common_values h.common_fee h.proposers_pos
    (h.eventually_finite_guards.mono fun _ ht => ⟨by omega, ht.2.1⟩)
    h.ppi h.visible_atomless h.feasible_continuations h.users h.abstention h.reject_zero

include h hp in

theorem exists_rank_limit :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ nu : ℕ → Measure ℝ,
      RankLimit (fun t => Γ (psi t)) pi (F.real (Ioi g)) nu := by
  exact exists_rank_limit_from_participation Γ h.visible_atomless hp
    h.rank_participation.1 h.rank_participation.2.1

theorem contactGain_lower_first_member {k j : ℕ}
    (hk : k ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    {theta : ℝ} (ht : 0 ≤ theta) :
    (k : ℝ)/n*(exp theta-1) ≤ contactGain n k j theta := by
  exact contactGain_first_member hk hj ht

theorem rank_objective_strict {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi (F.real (Ioi g)) nu)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    {u v theta : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hv : v ≤ F.real (Ioi g)) (ht : 0 < theta) :
    rivalObjective n rho k (rankTail nu (F.real (Ioi g)) u) theta <
      rivalObjective n rho k (rankTail nu (F.real (Ioi g)) v) theta := by
  exact hr.objective_strict hk hu huv hv ht

include h hp in

theorem used_rank_optimizer {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi (F.real (Ioi g)) nu)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, 0 < u ∧ u < F.real (Ioi g) ∧
      0 < rankTail nu (F.real (Ioi g)) u k ∧
      ∃ theta > 0,
        rivalObjective n rho k (rankTail nu (F.real (Ioi g)) u) theta =
          rivalRate n rho k (rankTail nu (F.real (Ioi g)) u) := by
  have hmean := (h.route_limit_accounting hp).2.2.2.2
  filter_upwards [hr.used_optimizer h.active_le_one h.ratio_lt_one hmean hk] with u hu
  obtain ⟨theta, ht, heq, _⟩ := hu.2.2.2
  exact ⟨hu.1, hu.2.1, hu.2.2.1, theta, ht, heq⟩

include h hp in

theorem used_rank_rate_ge {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi (F.real (Ioi g)) nu) {J : ℝ}
    (hc : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J) {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, J ≤ rivalRate n rho k (rankTail nu (F.real (Ioi g)) u) := by
  letI := h.probability
  exact hr.used_rate_ge_actual F g h.common_values h.common_fee h.users h.abstention
    h.ppi h.free h.visible_atomless h.feasible_continuations h.population_grows
    h.capacity_ratio h.rank_participation.1 h.active_le_one h.ratio_lt_one
    (h.route_limit_accounting hp).2.2.2.2 hc.all_rate hk

include h hp in

theorem used_rank_chernoff_gap {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi (F.real (Ioi g)) nu) {J : ℝ}
    (hc : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J) {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, ∃ theta ≥ 0,
      J < rivalObjective n rho k (rankTail nu (F.real (Ioi g)) u) theta := by
  exact hr.chernoff_gap_of_rate_ge h.active_le_one h.ratio_lt_one hc.mean_slack hk
    (h.used_rank_rate_ge hp hr hc hk)

include h hp in

theorem used_failure_small_with_rank_limit {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi (F.real (Ioi g)) nu) {z : ℝ} (hz : 0 < z) :
    ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => actualFailure (Γ t) x.2 / actualDeficit (Γ t) z) := by
  letI := h.probability
  obtain ⟨J, hc⟩ := h.common_rate_of_route_limit hp
  have hD := hc.deficit_rate z hz
  apply hr.failure_small_of_good_cuts F g h.common_values h.common_fee rfl h.active_pos
    h.rank_participation.2.2 hD.1
    (fun k u => ∃ theta ≥ 0,
      J < rivalObjective n rho k (rankTail nu (F.real (Ioi g)) u) theta)
    (fun k hk => h.used_rank_chernoff_gap hp hr hc hk)
  intro k hk u hu0 huh hu
  obtain ⟨theta, ht, hgap⟩ := hu
  exact hr.fixed_cut_failure_small h.population_grows h.capacity_ratio h.ppi
    h.visible_atomless h.feasible_continuations hD hk ⟨hu0.le, huh⟩ ht hgap

include h hp in

theorem used_failure_small_of_route_limit {z : ℝ} (hz : 0 < z) :
    ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => actualFailure (Γ t) x.2 / actualDeficit (Γ t) z) := by
  apply probZero_subsequence_principle
  intro phi hphi
  let hphiSeq := h.along phi hphi.tendsto_atTop
  have hpPhi : RouteLimit (fun t => Γ (phi t)) pi :=
    fun j hj => (hp j hj).comp hphi.tendsto_atTop
  obtain ⟨psi, hpsi, nu, hr⟩ := hphiSeq.exists_rank_limit hpPhi
  refine ⟨psi, hpsi, ?_⟩
  exact (hphiSeq.along psi hpsi.tendsto_atTop).used_failure_small_with_rank_limit
    (fun j hj => (hpPhi j hj).comp hpsi.tendsto_atTop) hr hz

end FreeBaseAmpleSequence
end FCAppendix.Bayes
