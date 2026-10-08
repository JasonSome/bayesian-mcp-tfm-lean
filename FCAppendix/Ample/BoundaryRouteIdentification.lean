import FCAppendix.Ample.BoundaryRouteIdentificationFinite
import FCAppendix.Ample.BoundaryNormalization

noncomputable section
namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.CompletionDraft Ample.DownstreamNormalizationCore
open FCAppendix.Bayes.RouteIdentificationDetails

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g : ℝ}

namespace FreeBaseBoundarySequence
variable (h : FreeBaseBoundarySequence M C Γ B F g)
include h

lemma boundary_active_mass_pos_each : ∀ t, 0 < (Γ t).F.real (Ioi (Γ t).g) := by
  intro t
  simpa only [h.common_values t, h.common_fee t] using h.active_pos

lemma boundary_route_limit_valid {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) :
    ValidLaw n pi := by
  have hr := h.common_rate hp
  refine ⟨?_, hr.mass.le.trans h.active_le_one⟩
  intro j hj
  exact hr.nonneg j (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)

theorem boundary_prefix_coefficient_le {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    pi k / (n.choose k : ℝ) ≤ pi n := by
  have hr := h.common_rate hp
  have hn := h.normalization hp he hz
  have hz0 : 0 < z := he.1.trans_lt hz
  have hD : (0 : ℝ) < n.choose k := by
    exact_mod_cast Nat.choose_pos (Finset.mem_Icc.mp hk).2
  by_contra hnot
  have hlt : pi n * (n.choose k : ℝ) < pi k := by
    exact (lt_div_iff₀ hD).mp (lt_of_not_ge hnot)
  obtain ⟨q, hqlo, hqhi⟩ := exists_between hlt
  have hq : 0 < q := (mul_pos hr.broadcast_pos hD).trans hqlo
  have hqm := actual_positive_route_mass_tendsto Γ
    (fun t => actualDeficit (Γ t) z) h.abstention h.boundary_active_mass_pos_each
    hn.bid_tiers (hr.deficit_rate z hz0).1 hp hk
  have hfinite : ∀ᶠ t in atTop,
      (q/(n.choose k : ℝ))^(M t-1) ≤ actualAllFailure (Γ t) := by
    filter_upwards [h.eventually_finite_guards, hqm.eventually_const_lt hqhi]
      with t ht hqt
    exact positive_class_all_failure_lower (Γ t) (by omega) ht.2.2
      (h.ppi t) (h.free t) (h.visible_atomless t) (h.feasible_continuations t)
      (h.users t) (h.abstention t) hk hq hqt
  have hupper : ∀ᶠ t in atTop,
      populationLogRate (M t) (actualAllFailure (Γ t)) ≤
        -(((M t-1 : ℕ) : ℝ)/(M t : ℝ))*log (q/(n.choose k : ℝ)) := by
    filter_upwards [hfinite, h.population_grows.eventually_ge_atTop 1]
      with t ht hmt
    have hh := populationLogRate_anti (by omega : 0 < M t)
      (pow_pos (div_pos hq hD) (M t-1)) ht
    have heq : populationLogRate (M t) ((q/(n.choose k : ℝ))^(M t-1)) =
        -(((M t-1 : ℕ) : ℝ)/(M t : ℝ))*log (q/(n.choose k : ℝ)) := by
      unfold populationLogRate
      rw [Real.log_pow]
      ring
    rwa [heq] at hh
  have hupperlim : Tendsto (fun t =>
      -(((M t-1 : ℕ) : ℝ)/(M t : ℝ))*log (q/(n.choose k : ℝ)))
      atTop (𝓝 (-log (q/(n.choose k : ℝ)))) := by
    simpa only [neg_one_mul] using
      (rival_fraction_tendsto_one M h.population_grows).neg.mul_const
        (log (q/(n.choose k : ℝ)))
  have hle := le_of_tendsto_of_tendsto hr.all_rate.2 hupperlim hupper
  have hqD : pi n < q/(n.choose k : ℝ) := (lt_div_iff₀ hD).mpr hqlo
  have hlog := Real.strictMonoOn_log hr.broadcast_pos (div_pos hq hD) hqD
  linarith

theorem boundary_off_tier_failure_small {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 (n-1))
    {x : ℝ} (hxlo : 1/((k : ℝ)+1) < x) (hxhi : x < 1/(k : ℝ))
    (hgap : pi k/(n.choose k : ℝ) < pi n) :
    Tendsto (fun t => actualFailure (Γ t)
      (scaledRouteAction k (by have := Finset.mem_Icc.mp hk; omega)
        (x*actualDeficit (Γ t) z))/actualDeficit (Γ t) z) atTop (𝓝 0) := by
  have hkn : k ≤ n := by have := Finset.mem_Icc.mp hk; omega
  have hk' : k ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, hkn⟩
  have hr := h.common_rate hp
  have hn := h.normalization hp he hz
  have hz0 : 0 < z := he.1.trans_lt hz
  have hscale := hr.deficit_rate z hz0
  have hx : 0 < x := (by positivity : 0 < 1/((k : ℝ)+1)).trans hxlo
  let b : ℕ → ℝ := fun t => x*actualDeficit (Γ t) z
  let μ : ℕ → FiniteLaw (Finset (Fin n)) := fun t => visibleLaw (Γ t) (b t)
  let a : ℝ := pi k/(n.choose k : ℝ)
  let J : ℝ := -log (pi n)
  let p : ℕ → ℝ := fun t => Shortage.congestionProb (μ t) (M t-1) (C t) (selected n k)
  have hconv := actual_off_tier_marked_law Γ (fun t => actualDeficit (Γ t) z)
    h.abstention h.boundary_active_mass_pos_each hn.bid_tiers hscale.1 hp
    (Finset.mem_Icc.mp hk).1 hxlo hxhi
  have hmass : Tendsto (fun t => Shortage.allMass (μ t) (selected n k))
      atTop (𝓝 a) :=
    visible_prefix_allMass_tendsto Γ b hk'
      (prefixLaw_valid (h.boundary_route_limit_valid hp) k) hconv
  have ha : 0 ≤ a := div_nonneg
    (hr.nonneg k (Finset.mem_Icc.mpr ⟨Nat.zero_le k, hkn⟩)) (Nat.cast_nonneg _)
  have hexp : ∃ d : ℝ, J < d ∧ ∀ᶠ t in atTop, p t ≤ exp (-d*(M t : ℝ)) := by
    by_cases ha0 : a = 0
    · have hzero : Tendsto (fun t => Shortage.allMass (μ t) (selected n k))
          atTop (𝓝 0) := by simpa only [ha0] using hmass
      have hs := boundary_contact_zero_mass μ M C (selected n k)
        h.population_grows h.capacity_ratio h.strict_shortage hzero
      exact ⟨J+1, by linarith, hs (J+1)⟩
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hpa : HasPopulationRate M p (-log a) :=
        boundary_contact_logRate μ M C (selected n k) h.population_grows
          h.capacity_ratio h.strict_shortage hap hmass
      have hJa : J < -log a := by
        have hh := Real.strictMonoOn_log hap hr.broadcast_pos hgap
        dsimp [J]
        linarith
      obtain ⟨d, hJd, hda⟩ := exists_between hJa
      exact ⟨d, hJd, population_rate_eventual_upper h.population_grows hpa hda⟩
  obtain ⟨d, hJd, hd⟩ := hexp
  have hactual : ∀ᶠ t in atTop,
      actualFailure (Γ t) (scaledRouteAction k hkn (b t)) = p t := by
    filter_upwards [h.eventually_finite_guards, hscale.1] with t hmt hct
    have hb : 0 < b t := mul_pos hx hct
    have hab : (scaledRouteAction k hkn (b t)).bid = b t := scaledRouteAction_bid hkn hb.le
    have heq := actual_failure_shortage (Γ t) (by omega) (h.ppi t)
      (h.visible_atomless t) (h.feasible_continuations t)
      (scaledRouteAction k hkn (b t)) (by rw [hab]; exact hb)
    simpa only [hab, scaledRouteAction_routeCount, p, μ] using heq
  apply exponential_upper_div_scale_zero h.population_grows hJd
    (Eventually.of_forall fun t => (actualMenu (Γ t)).failure_nonneg _)
    (by
      filter_upwards [hactual, hd] with t ht hdt
      change actualFailure (Γ t) (scaledRouteAction k hkn (b t)) ≤ _
      rw [ht]
      exact hdt) hscale

theorem boundary_prefix_equalities {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)
    {ell z : ℝ} (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    ∀ k ∈ Finset.Icc 1 n, pi k/(n.choose k : ℝ) = pi n := by
  intro k hk
  by_cases hkn : k = n
  · subst k
    simp only [Nat.choose_self, Nat.cast_one, div_one]
  have hklt : k < n := lt_of_le_of_ne (Finset.mem_Icc.mp hk).2 hkn
  have hk' : k ∈ Finset.Icc 1 (n-1) := by
    apply Finset.mem_Icc.mpr
    have hh := Finset.mem_Icc.mp hk
    omega
  apply le_antisymm (h.boundary_prefix_coefficient_le hp he hz hk)
  by_contra hnot
  have hgap : pi k/(n.choose k : ℝ) < pi n := lt_of_not_ge hnot
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hrec : 1/((k : ℝ)+1) < 1/(k : ℝ) := by
    exact one_div_lt_one_div_of_lt hkR (by linarith)
  obtain ⟨x, hxlo, hxhi⟩ := exists_between hrec
  have hx : 0 < x := (one_div_pos.mpr (by linarith)).trans hxlo
  have hkx : (k : ℝ)*x < 1 := by
    have hh := (lt_div_iff₀ hkR).mp hxhi
    nlinarith
  have hr := h.common_rate hp
  have hn := h.normalization hp he hz
  exact affordable_cut_contradiction Γ (Finset.mem_Icc.mp hk).2 hx hkx hz
    (he.1.trans hz.le)
    (by filter_upwards [h.eventually_finite_guards] with t ht; omega)
    h.ppi h.free hn (hr.deficit_rate z (he.1.trans_lt hz)).1
    (h.boundary_off_tier_failure_small hp he hz hk' hxlo hxhi hgap)

end FreeBaseBoundarySequence
end FCAppendix.Bayes.CompletionDraft
