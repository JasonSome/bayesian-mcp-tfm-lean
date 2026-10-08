import FCAppendix.Ample.RouteIdentificationOccupiedEdge
import FCAppendix.Ample.ActualNormalization

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

include h hp in
lemma route_limit_marginal_lt : contactMarginal n pi < rho := by
  have hh := (h.route_limit_accounting hp).2.2.2.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.proposers_pos
  unfold contactMarginal
  apply (div_lt_iff₀ hnR).2
  simpa only [mul_comm] using hh

include h in
lemma active_mass_pos_each : ∀ t, 0 < (Γ t).F.real (Ioi (Γ t).g) := by
  intro t
  simpa only [h.common_values t, h.common_fee t] using h.active_pos

include h hp in

theorem off_tier_prefix_law {ell z : ℝ}
    (hnorm : ActualNormalizationConclusion Γ g ell z)
    (hC : ∀ᶠ t in atTop, 0 < actualDeficit (Γ t) z)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 (n-1)) {x : ℝ}
    (hxlo : 1/((k : ℝ)+1) < x) (hxhi : x < 1/(k : ℝ)) :
    ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun t => visibleClassMass (Γ t) (x*actualDeficit (Γ t) z) j)
        atTop (𝓝 (prefixLaw pi k j)) := by
  exact actual_off_tier_marked_law Γ (fun t => actualDeficit (Γ t) z)
    h.abstention h.active_mass_pos_each hnorm.bid_tiers hC hp
    (Finset.mem_Icc.mp hk).1 hxlo hxhi

include h hp in

theorem rank_tier_localization {ell z : ℝ}
    (hnorm : ActualNormalizationConclusion Γ g ell z)
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi (F.real (Ioi g)) nu) :
    ∀ k ∈ Finset.Icc 1 n,
      nu k = volume.restrict (Ioc (rankLowerEdge n k pi)
        (rankLowerEdge n k pi + pi k)) := by
  have hh := h.route_limit_accounting hp
  have hk1 : 1 ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨le_rfl, h.proposers_pos⟩
  have hscale := eventually_scale_pos_of_actual_tiers Γ
    (fun t => actualDeficit (Γ t) z) h.abstention h.active_mass_pos_each
    hnorm.bid_tiers hp hk1 hh.2.2.2.1
  exact actual_rank_tier_localization Γ (fun t => actualDeficit (Γ t) z)
    h.abstention h.active_mass_pos_each hnorm.bid_tiers hscale hp hr hh.2.2.1

include h hp in

theorem occupied_prefix_ge {ell z J : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z)
    (hc : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) (hpk : 0 < pi k) :
    J ≤ prefixRate n rho k pi := by
  obtain ⟨psi, hpsi, nu, hr⟩ := h.exists_rank_limit hp
  let hs := h.along psi hpsi.tendsto_atTop
  have hps : RouteLimit (fun t => Γ (psi t)) pi :=
    fun j hj => (hp j hj).comp hpsi.tendsto_atTop
  have hns := hs.normalization_of_route_limit hps he hz
  have hcs := common_rate_along hc psi hpsi.tendsto_atTop
  exact RouteIdentificationDetails.occupied_edge_rate_ge hr
    (hs.route_limit_accounting hps).2.1 hcs.mass h.active_le_one
    (hs.route_limit_marginal_lt hps) h.ratio_lt_one
    (hs.rank_tier_localization hps hns hr) hk hpk
    (hs.used_rank_rate_ge hps hr hcs hk)

include h hp in

theorem off_tier_failure_small {ell z J : ℝ}
    (hnorm : ActualNormalizationConclusion Γ g ell z) (hz : 0 < z)
    (hc : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 (n-1))
    {x theta : ℝ} (hxlo : 1/((k : ℝ)+1) < x) (hxhi : x < 1/(k : ℝ))
    (ht : 0 ≤ theta) (hgap : J < prefixObjective n rho k pi theta) :
    Tendsto (fun t => actualFailure (Γ t)
      (scaledRouteAction k (by have := Finset.mem_Icc.mp hk; omega)
        (x*actualDeficit (Γ t) z)) / actualDeficit (Γ t) z) atTop (𝓝 0) := by
  have hkn : k ≤ n := by have := Finset.mem_Icc.mp hk; omega
  have hx : 0 < x := (by positivity : 0 < 1/((k : ℝ)+1)).trans hxlo
  have hC := hc.deficit_rate z hz
  have hconv := h.off_tier_prefix_law hp hnorm hC.1 hk hxlo hxhi
  let d : ℝ := (J + prefixObjective n rho k pi theta)/2
  have hJd : J < d := by dsimp [d]; linarith
  have hdo : d < rivalObjective n rho k (prefixLaw pi k) theta := by
    rw [← prefixObjective_eq_rival hkn]
    dsimp [d]
    linarith
  have hcgr := eventually_event_bound_of_chernoff hkn
    (fun t => visibleClassMass_valid (Γ t) (x*actualDeficit (Γ t) z))
    (prefixLaw_valid (h.route_limit_valid hp) k) hconv h.population_grows
    h.capacity_ratio ht hdo
  have hupper : ∀ᶠ t in atTop, actualFailure (Γ t)
      (scaledRouteAction k hkn (x*actualDeficit (Γ t) z)) ≤ exp (-d*(M t : ℝ)) := by
    filter_upwards [h.eventually_finite_guards, hC.1, hcgr] with t hmt hct hcg
    have hm : 0 < M t := by omega
    have hb : 0 < (scaledRouteAction k hkn (x*actualDeficit (Γ t) z)).bid := by
      rw [scaledRouteAction_bid hkn (mul_pos hx hct).le]
      exact mul_pos hx hct
    have heq := actualFailure_eq_congestProb (Γ t) hm (h.ppi t)
      (h.visible_atomless t) (h.feasible_continuations t)
      (scaledRouteAction k hkn (x*actualDeficit (Γ t) z)) hb
    rw [heq, scaledRouteAction_routeCount,
      scaledRouteAction_bid hkn (mul_pos hx hct).le]
    exact hcg
  exact exponential_upper_div_scale_zero h.population_grows hJd
    (Eventually.of_forall (fun t => (actualMenu (Γ t)).failure_nonneg _)) hupper hC

include h hp in

theorem occupied_prefix_eq {ell z J : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z)
    (hc : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) (hpk : 0 < pi k) :
    prefixRate n rho k pi = J := by
  by_cases hkn : k = n
  · subst k
    rw [prefixRate_self_eq_fullRate hc.mass, ← hc.rate_eq]
  have hk' : k ∈ Finset.Icc 1 (n-1) := by
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  apply le_antisymm _ (h.occupied_prefix_ge hp he hz hc hk hpk)
  by_contra hnot
  have hg : J < prefixRate n rho k pi := lt_of_not_ge hnot
  obtain ⟨theta, ht, hopt⟩ := finite_optimizer_prefix hk (h.route_limit_valid hp)
    h.ratio_lt_one (h.route_limit_marginal_lt hp) hpk
  have hgap : J < prefixObjective n rho k pi theta := by rwa [hopt]
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by have := (Finset.mem_Icc.mp hk).1; omega)
  obtain ⟨x, hxlo, hxhi⟩ := exists_between
    (one_div_lt_one_div_of_lt hkR (by linarith : (k : ℝ) < (k : ℝ)+1))
  have hx : 0 < x := (by positivity : 0 < 1/((k : ℝ)+1)).trans hxlo
  have hkx : (k : ℝ)*x < 1 := by
    have hh := (lt_div_iff₀ hkR).mp hxhi
    simpa only [mul_comm] using hh
  have hn := h.normalization_of_route_limit hp he hz
  have hz0 := he.1.trans_lt hz
  have hm : ∀ᶠ t in atTop, 0 < M t := by
    filter_upwards [h.eventually_finite_guards] with t ht; omega
  exact affordable_cut_contradiction Γ (Finset.mem_Icc.mp hk).2 hx hkx hz hz0.le
    hm h.ppi h.free hn (hc.deficit_rate z hz0).1
    (h.off_tier_failure_small hp hn hz0 hc hk' hxlo hxhi ht.le hgap)

include h hp in

theorem missing_class_finite_witness {J : ℝ}
    (hc : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J)
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r < k) (hk : k ≤ n)
    (hpr : 0 < pi r) (hzero : ∀ j ∈ Finset.Icc (r+1) k, pi j = 0)
    (hrate : prefixRate n rho r pi = J) :
    ∃ theta ≥ 0, J < prefixObjective n rho k pi theta := by
  have hrmem : r ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hr, hrk.le.trans hk⟩
  obtain ⟨s, hs, hopt⟩ := finite_optimizer_prefix hrmem (h.route_limit_valid hp)
    h.ratio_lt_one (h.route_limit_marginal_lt hp) hpr
  exact strict_larger_constraint_finite_witness hr hrk hk
    (h.route_limit_accounting hp).2.1 hc.singleton_pos hzero hs (hopt.trans hrate)

include h hp in

theorem all_classes_positive {ell z J : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z)
    (hc : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J) :
    ∀ k ∈ Finset.Icc 1 n, 0 < pi k := by
  intro k hk
  by_contra hnot
  have hnonneg := (h.route_limit_accounting hp).2.1
  have hpk : pi k = 0 := le_antisymm (le_of_not_gt hnot) (hnonneg k hk)
  have hk_ne_one : k ≠ 1 := by
    intro hh; subst k; exact hc.singleton_pos.ne' hpk
  have hk_ne_n : k ≠ n := by
    intro hh; subst k; exact hc.broadcast_pos.ne' hpk
  have hk1 : 1 < k := by have := Finset.mem_Icc.mp hk; omega
  have hkn : k < n := by have := Finset.mem_Icc.mp hk; omega
  obtain ⟨r, hr, hrk, hpr, hzero⟩ := last_occupied_before hnonneg hc.singleton_pos
    hk1 (Finset.mem_Icc.mp hk).2 hpk
  have hrmem : r ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hr, by omega⟩
  have hrate := h.occupied_prefix_eq hp he hz hc hrmem hpr
  obtain ⟨theta, ht, hgap⟩ := h.missing_class_finite_witness hp hc hr hrk
    (Finset.mem_Icc.mp hk).2 hpr hzero hrate
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨x, hxlo, hxhi⟩ := exists_between
    (one_div_lt_one_div_of_lt hkR (by linarith : (k : ℝ) < (k : ℝ)+1))
  have hx : 0 < x := (by positivity : 0 < 1/((k : ℝ)+1)).trans hxlo
  have hkx : (k : ℝ)*x < 1 := by
    have hh := (lt_div_iff₀ hkR).mp hxhi
    simpa only [mul_comm] using hh
  have hn := h.normalization_of_route_limit hp he hz
  have hz0 := he.1.trans_lt hz
  have hm : ∀ᶠ t in atTop, 0 < M t := by
    filter_upwards [h.eventually_finite_guards] with t ht; omega
  exact affordable_cut_contradiction Γ (Finset.mem_Icc.mp hk).2 hx hkx hz hz0.le
    hm h.ppi h.free hn (hc.deficit_rate z hz0).1
    (h.off_tier_failure_small hp hn hz0 hc
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hxlo hxhi ht hgap)

include h hp in

theorem limit_isRouteSolution {ell z : ℝ}
    (he : IsActiveEndpoint F g ell) (hz : ell < z) :
    IsRouteSolution n rho (F.real (Ioi g)) pi := by
  obtain ⟨J, hc⟩ := h.common_rate_of_route_limit hp
  have hpos := h.all_classes_positive hp he hz hc
  refine ⟨hpos, hc.mass, hc.mean_slack, ?_⟩
  intro k hk
  exact (h.occupied_prefix_eq hp he hz hc hk (hpos k hk)).trans hc.rate_eq

include h in

theorem unique_algebraic_route_system :
    ∃ q, IsRouteSolution n rho (F.real (Ioi g)) q ∧
      ∀ q', IsRouteSolution n rho (F.real (Ioi g)) q' →
        ∀ j ∈ Finset.Icc 1 n, q' j = q j := by
  exact existsUnique_isRouteSolution h.proposers_pos h.ratio_lt_one
    h.active_pos h.active_le_one h.ample

end FreeBaseAmpleSequence
end FCAppendix.Bayes
