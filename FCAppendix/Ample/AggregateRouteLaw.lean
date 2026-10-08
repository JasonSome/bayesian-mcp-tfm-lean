import FCAppendix.Ample.RouteIdentification
import FCAppendix.Ample.PositiveBaseMain
import FCAppendix.Ample.PayOnceComparison
import FCAppendix.Ample.ActualAggregateTransfer
import FCAppendix.Ample.ActualRouteCompactness

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

namespace FreeBaseAmpleSequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g rho : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g rho)

include h

theorem route_coordinates_tendsto {q : ℕ → ℝ}
    (hq : IsRouteSolution n rho (F.real (Ioi g)) q) :
    ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun t => actualRouteMass (Γ t) j) atTop (𝓝 (q j)) := by
  letI := h.probability
  obtain ⟨ell, he⟩ := exists_activeEndpoint F g h.active_pos
  intro j hj
  apply coordinate_subsequence_principle (fun t => actualRouteMass (Γ t) j) (q j)
  intro phi hphi
  obtain ⟨psi, hpsi, p, hp⟩ := finite_route_compactness Γ phi hphi
  let hs := (h.along phi hphi.tendsto_atTop).along psi hpsi.tendsto_atTop
  have hpSol := hs.limit_isRouteSolution hp he (show ell<ell+1 by linarith)
  have heq := IsRouteSolution.unique h.ratio_lt_one hpSol hq j hj
  refine ⟨psi, hpsi, ?_⟩
  simpa only [heq] using hp j (by simp only [Finset.mem_Icc] at *; omega)

theorem route_identification :
    ∃ pi : ℕ → ℝ, RouteLimit Γ pi ∧ pi 0 = 1-F.real (Ioi g) ∧
      IsRouteSolution n rho (F.real (Ioi g)) pi ∧
      ∀ q, IsRouteSolution n rho (F.real (Ioi g)) q →
        ∀ j ∈ Finset.Icc 1 n, q j = pi j := by
  obtain ⟨q, hq, _⟩ := h.unique_algebraic_route_system
  let pi := fun j => if j=0 then 1-F.real (Ioi g) else q j
  have hpos := h.route_coordinates_tendsto hq
  have hzero : Tendsto (fun t => actualRouteMass (Γ t) 0) atTop
      (𝓝 (1-F.real (Ioi g))) := zero_route_limit h
  have hp : RouteLimit Γ pi := by
    intro j hj
    by_cases hj0 : j=0
    · simpa [pi, hj0] using hzero
    · have hj' : j ∈ Finset.Icc 1 n := by simp only [Finset.mem_Icc] at *; omega
      simpa [pi, hj0] using hpos j hj'
  letI := h.probability
  obtain ⟨ell, he⟩ := exists_activeEndpoint F g h.active_pos
  have hpi := h.limit_isRouteSolution hp he (show ell<ell+1 by linarith)
  exact ⟨pi, hp, by simp [pi], hpi,
    fun q hq j hj => IsRouteSolution.unique h.ratio_lt_one hq hpi j hj⟩

theorem chosen_realized_limits {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) :
    (∀ j ∈ Finset.Icc 0 n,
      Tendsto (fun t => actualInclusionMass (Γ t) j) atTop (𝓝 (pi j))) ∧
    (∀ j ∈ Finset.Icc 0 n,
      Tendsto (fun t => actualPopulationInclusionMass (Γ t) j) atTop (𝓝 (pi j))) := by
  obtain ⟨kappa, hkappa, hcopy⟩ := h.uniform_exponential
  have he : Tendsto (fun t => (n : ℝ)*exp (-kappa*(M t : ℝ))) atTop (𝓝 0) := by
    simpa using (exp_neg_population_tendsto_zero h.population_grows hkappa).const_mul (n : ℝ)
  have herrors := chosen_realized_copy_error h hcopy
  constructor <;> intro j hj
  · exact squeeze_count_error (hp j hj) he (herrors j).1
  · exact squeeze_count_error (hp j hj) he (herrors j).2

theorem load_tendsto_route_mean {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) :
    Tendsto (fun t => finiteLoad (Γ t)) atTop
      (𝓝 (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j)) := by
  have hcounts := (h.chosen_realized_limits hp).2
  have hs := tendsto_finsetSum (Finset.Icc 1 n) (fun j hj =>
    (hcounts j (by simp only [Finset.mem_Icc] at *; omega)).const_mul (j : ℝ))
  apply hs.congr'
  filter_upwards [h.population_grows.eventually_ge_atTop 1] with t ht
  exact (load_as_finite_count_sum (Γ t) (by omega : 0 < M t)).symm

theorem route_mean_strict_bounds {pi : ℕ → ℝ}
    (hs : IsRouteSolution n rho (F.real (Ioi g)) pi) :
    1 < (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j) / F.real (Ioi g) ∧
    (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j) / F.real (Ioi g) <
      (n : ℝ)*rho / F.real (Ioi g) := by
  have hd : 0 < ∑ j ∈ Finset.Icc 1 n, ((j : ℝ)-1)*pi j := by
    apply Finset.sum_pos'
    · intro j hj
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      exact mul_nonneg (by linarith) (hs.pos j hj).le
    · refine ⟨2, by simp [h.two_proposers], ?_⟩
      simpa using hs.pos 2 (by simp [h.two_proposers])
  have heq : (∑ j ∈ Finset.Icc 1 n, ((j : ℝ)-1)*pi j) =
      (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j)-F.real (Ioi g) := by
    rw [← hs.mass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  constructor
  · apply (one_lt_div h.active_pos).2
    rw [heq] at hd
    linarith
  · exact (div_lt_div_iff_of_pos_right h.active_pos).2 hs.mean

theorem all_supported_service :
    ∀ w > 0, ∀ eps > 0, ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ a : JointAction n,
      (problem (Γ t) i).BestResponse (w+g) a →
      1-((problem (Γ t) i).outcome a).success < eps ∧ a.bid < eps := by
  exact h.all_identity_service_from_envelope

omit h in
structure InteriorAggregateConclusion (pi : ℕ → ℝ) (J : ℝ) : Prop where
  route_limit : RouteLimit Γ pi
  inactive_atom : pi 0 = 1-F.real (Ioi g)
  solution : IsRouteSolution n rho (F.real (Ioi g)) pi
  unique : ∀ q, IsRouteSolution n rho (F.real (Ioi g)) q →
    ∀ j ∈ Finset.Icc 1 n, q j = pi j
  inclusion_limit : ∀ j ∈ Finset.Icc 0 n,
    Tendsto (fun t => actualPopulationInclusionMass (Γ t) j) atTop (𝓝 (pi j))
  coverage_limit : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (F.real (Ioi g)))
  load_limit : Tendsto (fun t => finiteLoad (Γ t)) atTop
    (𝓝 (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j))
  multiplicity_limit : Tendsto (fun t => finiteMultiplicity (Γ t)) atTop
    (𝓝 ((∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j)/F.real (Ioi g)))
  multiplicity_bounds :
    1 < (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j)/F.real (Ioi g) ∧
    (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j)/F.real (Ioi g) < n*rho/F.real (Ioi g)
  common_rate : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
    (rho := rho) pi J
  normalization : ∀ ell z, IsActiveEndpoint F g ell → ell<z →
    ActualNormalizationConclusion Γ g ell z

theorem interior_aggregate_route_law :
    ∃ pi J, InteriorAggregateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J := by
  obtain ⟨pi, hp, hz, hsol, huniq⟩ := h.route_identification
  obtain ⟨J, hc⟩ := h.common_rate_of_route_limit hp
  have hload := h.load_tendsto_route_mean hp
  have hcoverage := h.coverage_tendsto
  refine ⟨pi, J, hp, hz, hsol, huniq, (h.chosen_realized_limits hp).2,
    hcoverage, hload, ?_, h.route_mean_strict_bounds hsol, hc, ?_⟩
  · exact hload.div hcoverage h.active_pos.ne'
  · intro ell z he hz
    exact h.normalization_of_route_limit hp he hz

theorem interior_complete_source :
    ∃ pi J, InteriorAggregateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J ∧
      (∀ j ∈ Finset.Icc 0 n,
        Tendsto (fun t => actualInclusionMass (Γ t) j) atTop (𝓝 (pi j))) ∧
      (∀ w > 0, ∀ eps > 0, ∀ᶠ t in atTop, ∀ i : Fin (M t), ∀ a : JointAction n,
        (problem (Γ t) i).BestResponse (w+g) a →
          1-((problem (Γ t) i).outcome a).success < eps ∧ a.bid < eps) := by
  obtain ⟨pi, J, H⟩ := h.interior_aggregate_route_law
  exact ⟨pi, J, H, (h.chosen_realized_limits H.route_limit).1, h.all_supported_service⟩

end FreeBaseAmpleSequence

theorem ample_free_base_strict_comparison
    {k : ℕ} {M C : ℕ → ℕ}
    (Γppi Γonce : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (Bppi : ∀ t, PosteriorSystem (Γppi t)) (Bonce : ∀ t, PosteriorSystem (Γonce t))
    (F : Measure ℝ) (g rho : ℝ)
    (hppi : FreeBaseAmpleSequence M C Γppi Bppi F g rho)
    (honce : InactiveSequenceAssumptions M C Γonce Bonce F g rho) :
    ∃ pi J Qonce,
      FreeBaseAmpleSequence.InteriorAggregateConclusion (M := M) (Γ := Γppi)
        (F := F) (g := g) (rho := rho) pi J ∧
      Tendsto (fun t => finiteCoverage (Γonce t)) atTop (𝓝 Qonce) ∧
      Tendsto (fun t => finiteLoad (Γonce t)) atTop (𝓝 (((k+1:ℕ):ℝ)*rho)) ∧
      Tendsto (fun t => finiteMultiplicity (Γonce t)) atTop
        (𝓝 (((k+1:ℕ):ℝ)*rho/Qonce)) ∧
      Qonce < F.real (Ioi g) ∧
      (∑ j ∈ Finset.Icc 1 (k+1), (j : ℝ)*pi j)/F.real (Ioi g) <
        ((k+1:ℕ):ℝ)*rho/F.real (Ioi g) ∧
      ((k+1:ℕ):ℝ)*rho/F.real (Ioi g) < ((k+1:ℕ):ℝ)*rho/Qonce := by
  letI := hppi.probability
  obtain ⟨pi, J, hppiOut⟩ := hppi.interior_aggregate_route_law
  let Qonce := PayOnce.Limit.coverage (F.map (fun v => max (v-g) 0)) (k+1)
    (PayOnce.Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) rho)
  obtain ⟨hQ, _, hQlt, hL, hmu, hstrict⟩ :=
    payOnce_ample_comparison Γonce Bonce F g rho honce
  exact ⟨pi, J, Qonce, hppiOut, hQ, hL, hmu, hQlt,
    hppiOut.multiplicity_bounds.2, hstrict⟩

end FCAppendix.Bayes
