import FCAppendix.Ample.BoundaryService
import FCAppendix.Ample.BoundaryCommonRate
import FCAppendix.Ample.BoundaryUsedRanks
import FCAppendix.Ample.BoundaryNormalization
import FCAppendix.Ample.BoundaryRouteIdentification
import FCAppendix.Ample.RouteIdentificationAssemblyTools
import FCAppendix.Ample.NoShortageHalving

noncomputable section
namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.CompletionDraft Ample.DownstreamNormalizationCore
open FCAppendix.Bayes.RouteIdentificationDetails

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g : ℝ}

def boundaryUnconditionalMass (n : ℕ) (h : ℝ) (j : ℕ) : ℝ :=
  if j=0 then 1-h else boundaryMass n h j

namespace FreeBaseBoundarySequence
variable (h : FreeBaseBoundarySequence M C Γ B F g)
include h

theorem prefix_equalities {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ∀ k ∈ Finset.Icc 1 n, pi k/(n.choose k : ℝ) = pi n := by
  exact h.boundary_prefix_equalities hp he hz

theorem identify_route_limit {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    (∀ k ∈ Finset.Icc 1 n, pi k = boundaryMass n (F.real (Ioi g)) k) ∧
    -log (pi n) = log ((2 ^ n - 1)/F.real (Ioi g)) := by
  have hr := h.common_rate hp
  have hn : 1 ≤ n := by have := h.proposers_two; omega
  have hid := identify_boundary_from_prefix_rates hn h.active_pos
    hr.broadcast_pos pi hr.mass (h.prefix_equalities hp he hz)
  exact ⟨hid.2.2.1, hid.2.1⟩

theorem boundary_chosen_tendsto {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ∀ j ∈ Finset.Icc 1 n, Tendsto (fun t => actualRouteMass (Γ t) j)
      atTop (𝓝 (boundaryMass n (F.real (Ioi g)) j)) := by
  intro j hj
  apply coordinate_subsequence_principle (fun t => actualRouteMass (Γ t) j)
    (boundaryMass n (F.real (Ioi g)) j)
  intro phi hphi
  obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
  let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
  have hid := hs.identify_route_limit hp he hz
  refine ⟨psi, hpsi, ?_⟩
  simpa only [hid.1 j hj] using hp j
    (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)

theorem boundary_inactive_atom :
    Tendsto (fun t => actualRouteMass (Γ t) 0) atTop (𝓝 (1-F.real (Ioi g))) := by
  have hh := h.participation.const_sub 1
  apply hh.congr'
  exact Eventually.of_forall fun t => (route_zero_eq_one_sub_positive_sum (Γ t)).symm

theorem boundary_route_limit {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    RouteLimit Γ (boundaryUnconditionalMass n (F.real (Ioi g))) := by
  intro j hj
  by_cases hj0 : j=0
  · subst j
    simpa [boundaryUnconditionalMass] using h.boundary_inactive_atom
  · have hj' : j ∈ Finset.Icc 1 n := by
      apply Finset.mem_Icc.mpr
      have hh := Finset.mem_Icc.mp hj
      omega
    simpa only [boundaryUnconditionalMass, if_neg hj0] using h.boundary_chosen_tendsto he hz j hj'

theorem boundary_chosen_realized_limits {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    (∀ j ∈ Finset.Icc 0 n, Tendsto (fun t => actualInclusionMass (Γ t) j)
      atTop (𝓝 (boundaryUnconditionalMass n (F.real (Ioi g)) j))) ∧
    (∀ j ∈ Finset.Icc 0 n, Tendsto (fun t => actualPopulationInclusionMass (Γ t) j)
      atTop (𝓝 (boundaryUnconditionalMass n (F.real (Ioi g)) j))) := by
  have hp := h.boundary_route_limit he hz
  obtain ⟨kc, hkc, hce⟩ := h.acceptance.count_error
  obtain ⟨kp, hkp, hpe⟩ := h.acceptance.population_count_error
  have hclim : Tendsto (fun t => (n : ℝ)*exp (-kc*(M t : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (exp_neg_population_tendsto_zero h.population_grows hkc).const_mul (n : ℝ)
  have hplim : Tendsto (fun t => (n : ℝ)*exp (-kp*(M t : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (exp_neg_population_tendsto_zero h.population_grows hkp).const_mul (n : ℝ)
  constructor
  · intro j hj
    exact squeeze_count_error (hp j hj) hclim
      (hce.mono fun t ht => ht j)
  · intro j hj
    exact squeeze_count_error (hp j hj) hplim
      (hpe.mono fun t ht => ht j)

theorem boundary_coverage_tendsto {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (F.real (Ioi g))) := by
  have hc := (h.boundary_chosen_realized_limits he hz).2 0
    (Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le n⟩)
  simp [boundaryUnconditionalMass] at hc
  have hh := hc.const_sub 1
  simp only [sub_sub_cancel] at hh
  apply hh.congr'
  filter_upwards [h.population_grows.eventually_ge_atTop 1] with t ht
  exact (finite_coverage_eq_one_sub_population_zero (Γ t) (by omega)).symm

theorem boundary_load_tendsto {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    Tendsto (fun t => finiteLoad (Γ t)) atTop
      (𝓝 (F.real (Ioi g)*((n : ℝ)*2^(n-1))/(2^n-1))) := by
  have hc := (h.boundary_chosen_realized_limits he hz).2
  have hh : Tendsto (fun t => finiteLoad (Γ t)) atTop
      (𝓝 (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*boundaryMass n (F.real (Ioi g)) j)) := by
    apply load_limit_from_population_counts Γ
      (by filter_upwards [h.population_grows.eventually_ge_atTop 1] with t ht; omega)
    intro j hj
    have hj0 : j ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
    simpa only [boundaryUnconditionalMass, if_neg hj0] using hc j
      (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)
  rwa [sum_Icc_one_eq_sum_range, boundaryMass_load] at hh

theorem boundary_all_rate {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    HasPopulationRate M (fun t => actualAllFailure (Γ t))
      (log ((2^n-1)/F.real (Ioi g))) := by
  constructor
  · apply eventually_of_subsequence_eventually (fun t => 0 < actualAllFailure (Γ t))
    intro phi hphi
    obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
    let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
    exact ⟨psi, hpsi, (hs.common_rate hp).all_rate.1⟩
  · apply coordinate_subsequence_principle
      (fun t => populationLogRate (M t) (actualAllFailure (Γ t)))
      (log ((2^n-1)/F.real (Ioi g)))
    intro phi hphi
    obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
    let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
    have hr := hs.common_rate hp
    have hid := hs.identify_route_limit hp he hz
    exact ⟨psi, hpsi, by simpa only [Function.comp_apply, hid.2] using hr.all_rate.2⟩

theorem boundary_deficit_rate {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) (w : ℝ) (hw : 0 < w) :
    HasPopulationRate M (fun t => actualDeficit (Γ t) w)
      (log ((2^n-1)/F.real (Ioi g))) := by
  constructor
  · apply eventually_of_subsequence_eventually (fun t => 0 < actualDeficit (Γ t) w)
    intro phi hphi
    obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
    let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
    exact ⟨psi, hpsi, ((hs.common_rate hp).deficit_rate w hw).1⟩
  · apply coordinate_subsequence_principle
      (fun t => populationLogRate (M t) (actualDeficit (Γ t) w))
      (log ((2^n-1)/F.real (Ioi g)))
    intro phi hphi
    obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
    let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
    have hr := hs.common_rate hp
    have hid := hs.identify_route_limit hp he hz
    exact ⟨psi, hpsi, by simpa only [Function.comp_apply, hid.2] using (hr.deficit_rate w hw).2⟩

theorem boundary_compact_rate {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ∀ lo hi, 0 < lo → lo ≤ hi → ∀ eps > 0,
    ∀ᶠ t in atTop, ∀ w ∈ Icc lo hi,
      |populationLogRate (M t) (actualDeficit (Γ t) w) -
        log ((2^n-1)/F.real (Ioi g))| < eps := by
  intro lo hi hlo hhi eps heps
  apply eventually_of_subsequence_eventually
    (fun t => ∀ w ∈ Icc lo hi, |populationLogRate (M t) (actualDeficit (Γ t) w) -
      log ((2^n-1)/F.real (Ioi g))| < eps)
  intro phi hphi
  obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
  let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
  have hr := hs.common_rate hp
  have hid := hs.identify_route_limit hp he hz
  refine ⟨psi, hpsi, ?_⟩
  have hh := hr.compact_rate lo hi hlo hhi eps heps
  simpa only [Function.comp_apply, ← hid.2, sub_neg_eq_add] using hh

theorem boundary_normalization_full {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ActualNormalizationConclusion Γ g ell z := by
  constructor
  · intro w hw
    apply coordinate_subsequence_principle
      (fun t => actualDeficit (Γ t) w/actualDeficit (Γ t) z) 1
    intro phi hphi
    obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
    let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
    exact ⟨psi, hpsi, (hs.normalization hp he hz).pointwise w hw⟩
  · intro lo hi hlo hhi eps heps
    apply eventually_of_subsequence_eventually
      (fun t => ∀ w ∈ Icc lo hi,
        |actualDeficit (Γ t) w/actualDeficit (Γ t) z-1| < eps)
    intro phi hphi
    obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
    let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
    exact ⟨psi, hpsi, (hs.normalization hp he hz).compact lo hi hlo hhi eps heps⟩
  · apply probZero_subsequence_principle (fun t => activeDrawLaw (Γ t))
      (fun t x => actualDeficit (Γ t) (x.1-g)/actualDeficit (Γ t) z-1)
    intro phi hphi
    obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
    let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
    exact ⟨psi, hpsi, (hs.normalization hp he hz).random_deficit⟩
  · apply probZero_subsequence_principle (fun t => activeDrawLaw (Γ t))
      (fun t x => (x.2.routeCount : ℝ)*x.2.bid/actualDeficit (Γ t) z-1)
    intro phi hphi
    obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
    let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
    exact ⟨psi, hpsi, (hs.normalization hp he hz).bid_tiers⟩

end FreeBaseBoundarySequence

structure UpperBoundaryConclusion
    (M C : ℕ → ℕ) (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (F : Measure ℝ) (g ell z : ℝ) : Prop where
  chosen : ∀ j ∈ Finset.Icc 1 n, Tendsto
    (fun t => actualRouteMass (Γ t) j) atTop
    (𝓝 (boundaryMass n (F.real (Ioi g)) j))
  canonical_realized : ∀ j ∈ Finset.Icc 1 n, Tendsto
    (fun t => actualInclusionMass (Γ t) j) atTop
    (𝓝 (boundaryMass n (F.real (Ioi g)) j))
  realized : ∀ j ∈ Finset.Icc 1 n, Tendsto
    (fun t => actualPopulationInclusionMass (Γ t) j) atTop
    (𝓝 (boundaryMass n (F.real (Ioi g)) j))
  coverage : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (F.real (Ioi g)))
  multiplicity : Tendsto (fun t => finiteMultiplicity (Γ t)) atTop
    (𝓝 ((n : ℝ)*2^(n-1)/(2^n-1)))
  deficit_rate : HasPopulationRate M (fun t => actualDeficit (Γ t) z)
    (log ((2^n-1)/F.real (Ioi g)))
  normalized : ActualNormalizationConclusion Γ g ell z

theorem upper_boundary_completion_path
    (h : FreeBaseBoundarySequence M C Γ B F g)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    UpperBoundaryConclusion M C Γ F g ell z := by
  have hcnt := h.boundary_chosen_realized_limits he hz
  have hQ := h.boundary_coverage_tendsto he hz
  have hL := h.boundary_load_tendsto he hz
  refine ⟨h.boundary_chosen_tendsto he hz, ?_, ?_, hQ, ?_,
    h.boundary_deficit_rate he hz z (he.1.trans_lt hz), h.boundary_normalization_full he hz⟩
  · intro j hj
    have hj0 : j ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
    simpa only [boundaryUnconditionalMass, if_neg hj0] using hcnt.1 j
      (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)
  · intro j hj
    have hj0 : j ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
    simpa only [boundaryUnconditionalMass, if_neg hj0] using hcnt.2 j
      (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)
  · have hh := hL.div hQ h.active_pos.ne'
    change Tendsto (fun t => finiteMultiplicity (Γ t)) atTop
      (𝓝 ((F.real (Ioi g)*((n : ℝ)*2^(n-1))/(2^n-1))/F.real (Ioi g))) at hh
    convert hh using 1
    field_simp [h.active_pos.ne']

theorem upper_boundary_conditioning_positive
    (h : FreeBaseBoundarySequence M C Γ B F g)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ∀ᶠ t in atTop,
      0 < (∑ j ∈ Finset.Icc 1 n, actualRouteMass (Γ t) j) ∧
      0 < 1-actualInclusionMass (Γ t) 0 ∧ 0 < finiteCoverage (Γ t) := by
  have hc0 := (h.boundary_chosen_realized_limits he hz).1 0
    (Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le n⟩)
  simp [boundaryUnconditionalMass] at hc0
  have hcanonical : Tendsto (fun t => 1-actualInclusionMass (Γ t) 0)
      atTop (𝓝 (F.real (Ioi g))) := by
    simpa only [sub_sub_cancel] using hc0.const_sub 1
  filter_upwards [h.participation.eventually_const_lt h.active_pos,
    hcanonical.eventually_const_lt h.active_pos,
    (h.boundary_coverage_tendsto he hz).eventually_const_lt h.active_pos]
    with t hchosen hcanon hpopulation
  exact ⟨hchosen, hcanon, hpopulation⟩

theorem upper_boundary_conditional_binomial
    (h : FreeBaseBoundarySequence M C Γ B F g)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ∀ j ∈ Finset.Icc 1 n,
      let b := (ProbabilityTheory.binomial n ⟨1/2, by norm_num⟩).real {j}/
        (1-(ProbabilityTheory.binomial n ⟨1/2, by norm_num⟩).real {0})
      Tendsto (fun t => actualRouteMass (Γ t) j/
        (∑ k ∈ Finset.Icc 1 n, actualRouteMass (Γ t) k)) atTop (𝓝 b) ∧
      Tendsto (fun t => actualPopulationInclusionMass (Γ t) j/finiteCoverage (Γ t))
        atTop (𝓝 b) := by
  intro j hj b
  have H := upper_boundary_completion_path h he hz
  have hn : 1 ≤ n := by have := h.proposers_two; omega
  have heq := boundaryMass_conditional_binomial hn h.active_pos j hj
  constructor
  · have hh := (H.chosen j hj).div h.participation h.active_pos.ne'
    rw [heq] at hh
    exact hh
  · have hh := (H.realized j hj).div H.coverage h.active_pos.ne'
    rw [heq] at hh
    exact hh

theorem upper_boundary_conditional_binomial_all_counts
    (h : FreeBaseBoundarySequence M C Γ B F g)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ∀ j ∈ Finset.Icc 1 n,
      let b := (ProbabilityTheory.binomial n ⟨1/2, by norm_num⟩).real {j}/
        (1-(ProbabilityTheory.binomial n ⟨1/2, by norm_num⟩).real {0})
      Tendsto (fun t => actualRouteMass (Γ t) j/
        (∑ k ∈ Finset.Icc 1 n, actualRouteMass (Γ t) k)) atTop (𝓝 b) ∧
      Tendsto (fun t => actualInclusionMass (Γ t) j/
        (1-actualInclusionMass (Γ t) 0)) atTop (𝓝 b) ∧
      Tendsto (fun t => actualPopulationInclusionMass (Γ t) j/finiteCoverage (Γ t))
        atTop (𝓝 b) := by
  intro j hj b
  have hpair := upper_boundary_conditional_binomial h he hz j hj
  have hc := (h.boundary_chosen_realized_limits he hz).1
  have hc0 := hc 0 (Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le n⟩)
  simp [boundaryUnconditionalMass] at hc0
  have hden : Tendsto (fun t => 1-actualInclusionMass (Γ t) 0)
      atTop (𝓝 (F.real (Ioi g))) := by
    simpa only [sub_sub_cancel] using hc0.const_sub 1
  have hj0 : j ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
  have hcj : Tendsto (fun t => actualInclusionMass (Γ t) j) atTop
      (𝓝 (boundaryMass n (F.real (Ioi g)) j)) := by
    simpa only [boundaryUnconditionalMass, if_neg hj0] using hc j
      (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)
  have hn : 1 ≤ n := by have := h.proposers_two; omega
  have heq := boundaryMass_conditional_binomial hn h.active_pos j hj
  refine ⟨hpair.1, ?_, hpair.2⟩
  have hh := hcj.div hden h.active_pos.ne'
  rw [heq] at hh
  exact hh

theorem upper_boundary_complete_source
    (h : FreeBaseBoundarySequence M C Γ B F g)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    UpperBoundaryConclusion M C Γ F g ell z ∧
    RouteLimit Γ (boundaryUnconditionalMass n (F.real (Ioi g))) ∧
    (∀ j ∈ Finset.Icc 0 n, Tendsto (fun t => actualInclusionMass (Γ t) j)
      atTop (𝓝 (boundaryUnconditionalMass n (F.real (Ioi g)) j))) ∧
    (∀ j ∈ Finset.Icc 0 n, Tendsto (fun t => actualPopulationInclusionMass (Γ t) j)
      atTop (𝓝 (boundaryUnconditionalMass n (F.real (Ioi g)) j))) ∧
    Tendsto (fun t => finiteLoad (Γ t)) atTop
      (𝓝 (F.real (Ioi g)*((n : ℝ)*2^(n-1))/(2^n-1))) ∧
    HasPopulationRate M (fun t => actualAllFailure (Γ t))
      (log ((2^n-1)/F.real (Ioi g))) ∧
    (∀ w > 0, HasPopulationRate M (fun t => actualDeficit (Γ t) w)
      (log ((2^n-1)/F.real (Ioi g)))) ∧
    (∀ lo hi, 0 < lo → lo ≤ hi → ∀ eps > 0, ∀ᶠ t in atTop,
      ∀ w ∈ Icc lo hi, |populationLogRate (M t) (actualDeficit (Γ t) w)-
        log ((2^n-1)/F.real (Ioi g))| < eps) := by
  have hc := h.boundary_chosen_realized_limits he hz
  exact ⟨upper_boundary_completion_path h he hz, h.boundary_route_limit he hz,
    hc.1, hc.2, h.boundary_load_tendsto he hz, h.boundary_all_rate he hz,
    h.boundary_deficit_rate he hz, h.boundary_compact_rate he hz⟩

end FCAppendix.Bayes.CompletionDraft
