import FCAppendix.Ample.BoundaryCommonRate
import FCAppendix.Ample.BoundaryRankUsedRate
import FCAppendix.Ample.RankSourceParticipation
import FCAppendix.Ample.RankCompactness
import FCAppendix.Ample.RankGapExhaustion

noncomputable section
namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators
open Ample Ample.CompletionDraft Ample.DownstreamNormalizationCore

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
namespace FreeBaseBoundarySequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
    {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g : ℝ}
    (h : FreeBaseBoundarySequence M C Γ B F g)

include h

private theorem rank_participation :
    (∀ᶠ t in atTop, positiveRouteMass (Γ t) (fun _ => True) = F.real (Ioi g)) ∧
    (∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      0 < x.2.routeCount → 0 < x.2.bid) ∧
    (∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      (0 < x.2.bid ∧ 0 < x.2.routeCount) ↔ (Γ t).g < x.1) := by
  exact actual_rank_participation Γ F g h.common_values h.common_fee
    (by have := h.proposers_two; omega)
    (h.eventually_finite_guards.mono fun _ ht => ⟨by omega, ht.2.1⟩)
    h.ppi h.visible_atomless h.feasible_continuations h.users h.abstention h.reject_zero

theorem exists_rank_limit {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ nu : ℕ → Measure ℝ,
      RankLimit (fun t => Γ (psi t)) pi (F.real (Ioi g)) nu := by
  exact exists_rank_limit_from_participation Γ h.visible_atomless hp
    h.rank_participation.1 h.rank_participation.2.1

theorem used_allContact_bounds {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi (F.real (Ioi g)) nu)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, 0 < u ∧ u < F.real (Ioi g) ∧
      0 < allContactTail n k nu (F.real (Ioi g)) u ∧
      allContactTail n k nu (F.real (Ioi g)) u < pi n := by
  letI := h.probability
  have hc := h.common_rate hp
  have hle := hr.used_allContact_le_actual F g h.common_values h.common_fee
    h.users h.abstention h.ppi h.free h.visible_atomless h.feasible_continuations
    h.population_grows h.strict_shortage h.rank_participation.1 hc.broadcast_pos hc.all_rate hk
  filter_upwards [hr.used_allContact_positive hk, hr.used_allContact_lt_of_le hk hle]
    with u hpos hlt
  exact ⟨hpos.1, hpos.2.1, hpos.2.2, hlt⟩

theorem used_failure_small_with_rank_limit {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi (F.real (Ioi g)) nu)
    {z : ℝ} (hz : 0 < z) :
    ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => actualFailure (Γ t) x.2 / actualDeficit (Γ t) z) := by
  letI := h.probability
  have hc := h.common_rate hp
  have hD := hc.deficit_rate z hz
  apply hr.failure_small_of_good_cuts F g h.common_values h.common_fee rfl h.active_pos
    h.rank_participation.2.2 hD.1
    (fun k u => allContactTail n k nu (F.real (Ioi g)) u < pi n)
    (fun k hk => (h.used_allContact_bounds hp hr hk).mono fun _ hu => hu.2.2.2)
  intro k hk u hu0 huh hu
  exact hr.boundary_fixed_cut_failure_small h.population_grows h.capacity_ratio
    h.strict_shortage h.ppi h.visible_atomless h.feasible_continuations
    hc.broadcast_pos hc.broadcast_lt_one.le hD hk ⟨hu0.le, huh⟩ hu

theorem used_failure_small {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {z : ℝ} (hz : 0 < z) :
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

end FreeBaseBoundarySequence
end FCAppendix.Bayes.CompletionDraft
