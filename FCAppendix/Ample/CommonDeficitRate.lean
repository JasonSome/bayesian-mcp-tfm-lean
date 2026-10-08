import FCAppendix.Ample.CommonRateAM3
import FCAppendix.Ample.StrictSlack

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators ENNReal
open Ample
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g rho : ℝ}

namespace FreeBaseAmpleSequence
variable (h : FreeBaseAmpleSequence M C Γ B F g rho)
  {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)

include h in
lemma eventually_commonRate_rows :
    ∀ᶠ t in atTop,
      (∀ j, 1≤j → visibleClassMass (Γ t) 0 j=actualRouteMass (Γ t) j) ∧
      actualRouteMass (Γ t) 0=1-F.real (Ioi g) ∧
      positiveRouteMass (Γ t) (fun _ => True)=F.real (Ioi g) := by
  filter_upwards [h.eventually_finite_guards] with t ht
  simpa only [h.common_values t,h.common_fee t] using commonRate_primitive_row (Γ t)
    (by omega) h.proposers_pos ht.2.1 (h.ppi t) (h.visible_atomless t)
    (h.feasible_continuations t) (h.users t) (h.abstention t) (h.reject_zero t)

include h hp in
lemma visible_zero_tendsto : ∀ j ∈ Finset.Icc 1 n,
    Tendsto (fun t => visibleClassMass (Γ t) 0 j) atTop (𝓝 (pi j)) := by
  intro j hj
  apply (hp j (Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hj).2⟩)).congr'
  filter_upwards [h.eventually_commonRate_rows] with t ht
  exact (ht.1 j (Finset.mem_Icc.mp hj).1).symm

include hp in
lemma route_limit_nonneg : ∀ j ∈ Finset.Icc 0 n, 0≤pi j := by
  intro j hj
  exact ge_of_tendsto (hp j hj) (Eventually.of_forall fun _ => measureReal_nonneg)

include h hp in
lemma route_limit_total : (∑ j ∈ Finset.Icc 1 n, pi j)=F.real (Ioi g) := by
  have hs := tendsto_finsetSum (Finset.Icc 1 n) (h.visible_zero_tendsto hp)
  have he : (fun t => ∑ j ∈ Finset.Icc 1 n, visibleClassMass (Γ t) 0 j) =ᶠ[atTop]
      (fun _ => F.real (Ioi g)) := by
    filter_upwards [h.eventually_commonRate_rows] with t ht
    rw [← positiveRouteMass_sum_classes]
    exact ht.2.2
  exact tendsto_nhds_unique (hs.congr' he) tendsto_const_nhds

include h hp in
lemma route_limit_valid : ValidLaw n pi where
  nonneg j hj := route_limit_nonneg hp j
    (Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hj).2⟩)
  total_le := by rw [h.route_limit_total hp]; exact h.active_le_one

include h hp in
lemma contact_marginal_tendsto :
    Tendsto (fun t => contactMarginal n (visibleClassMass (Γ t) 0)) atTop
      (𝓝 (contactMarginal n pi)) := by
  exact (tendsto_finsetSum (Finset.Icc 1 n) (fun j hj =>
    (h.visible_zero_tendsto hp j hj).mul_const (j:ℝ))).div_const (n:ℝ)

include h hp in

theorem route_limit_accounting :
    pi 0 = 1 - F.real (Ioi g) ∧
    (∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j) ∧
    (∑ j ∈ Finset.Icc 1 n, pi j) = F.real (Ioi g) ∧
    0 < pi 1 ∧ (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * pi j) < n * rho := by
  obtain ⟨a₁,a₂,eta,hs⟩ := h.strict_slack
  have hz : pi 0=1-F.real (Ioi g) := by
    apply tendsto_nhds_unique
      ((hp 0 (by simp)).congr' (h.eventually_commonRate_rows.mono fun t ht => ht.2.1))
      tendsto_const_nhds
  have hs₁ : a₁≤pi 1 := ge_of_tendsto (hp 1 (Finset.mem_Icc.mpr ⟨Nat.zero_le _, h.proposers_pos⟩))
    (hs.eventual.mono fun _ ht => ht.1)
  have hm : contactMarginal n pi≤rho-eta := by
    apply le_of_tendsto (h.contact_marginal_tendsto hp)
    filter_upwards [hs.eventual,h.eventually_exact_participation] with t ht he
    rw [← he.2]
    exact ht.2.2.2.2
  have hm' : (∑ j ∈ Finset.Icc 1 n, (j:ℝ)*pi j)<n*rho := by
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr h.proposers_pos
    have hstrict : contactMarginal n pi<rho := by linarith [hs.margin_pos]
    have hh := (div_lt_iff₀ hnR).mp hstrict
    simpa only [contactMarginal,mul_comm] using hh
  exact ⟨hz,(h.route_limit_valid hp).nonneg,h.route_limit_total hp,
    hs.singleton_pos.trans_le hs₁,hm'⟩

include h hp in
lemma route_limit_contact_slack : contactMarginal n pi<rho := by
  have hh := (h.route_limit_accounting hp).2.2.2.2
  apply (div_lt_iff₀ (Nat.cast_pos.mpr h.proposers_pos)).mpr
  simpa only [mul_comm] using hh

include h hp in
lemma singleton_mass_tendsto :
    Tendsto (fun t => positiveRouteMass (Γ t) (fun k => k=1)) atTop (𝓝 (pi 1)) := by
  simpa only [positiveRouteMass_class_eq _ (by omega : 1≤1)] using
    h.visible_zero_tendsto hp 1 (Finset.mem_Icc.mpr ⟨le_rfl,h.proposers_pos⟩)

include h hp in

theorem full_objectives_bounded :
    ∀ theta : ℝ, 0 ≤ theta →
      fullObjective n rho (F.real (Ioi g)) pi theta ≤ binaryKL rho (pi 1/n) := by
  have ha := h.route_limit_accounting hp
  have hq : pi 1/n<rho := by
    have hs : pi 1≤∑ j ∈ Finset.Icc 1 n, (j:ℝ)*pi j := by
      simpa only [Nat.cast_one,one_mul] using Finset.single_le_sum
        (fun j hj => mul_nonneg (Nat.cast_nonneg j) (ha.2.1 j hj))
        (Finset.mem_Icc.mpr ⟨le_rfl,h.proposers_pos⟩)
    apply (div_lt_iff₀ (Nat.cast_pos.mpr h.proposers_pos)).mpr
    nlinarith [ha.2.2.2.2]
  have hr := commonRate_singleton_event_rate h.proposers_pos h.population_grows h.capacity_ratio
    (fun t => ⟨positiveRouteMass_nonneg (Γ t) _,positiveRouteMass_le_one (Γ t) _⟩)
    (h.singleton_mass_tendsto hp) ha.2.2.2.1 h.ratio_pos h.ratio_lt_one hq
  intro theta ht
  by_contra hnot
  have hgap : binaryKL rho (pi 1/n)<fullObjective n rho (F.real (Ioi g)) pi theta :=
    lt_of_not_ge hnot
  obtain ⟨L,hJL,hLF⟩ := exists_between hgap
  obtain ⟨U,hLU,hUF⟩ := exists_between hLF
  have hlo := hr.eventually_lower_exp h.population_grows hJL
  have hup := eventually_event_bound_of_chernoff le_rfl
    (fun t => visibleClassMass_valid (Γ t) 0) (h.route_limit_valid hp)
    (h.visible_zero_tendsto hp) h.population_grows h.capacity_ratio ht
    (by rw [commonRate_fullObjective_eq ha.2.2.1]; exact hUF)
  apply commonRate_no_exponent_cross
    (p := fun t => congestProb n (M t-1) (C t) 1
      (singletonOnly (positiveRouteMass (Γ t) (fun k => k=1))))
    (q := fun t => actualAllFailure (Γ t)) h.population_grows hLU
  filter_upwards [hlo,hup,h.eventually_finite_guards] with t hl hu hg
  have hm : 0<M t := by omega
  refine ⟨hl,commonRate_AM3_lower (Γ t) hm h.proposers_pos hg.2.1 hg.2.2
    (h.ppi t) (h.free t) (h.visible_atomless t) (h.feasible_continuations t)
    (h.users t) (h.abstention t),?_⟩
  rw [actualAllFailure_eq_congestProb (Γ t) hm]
  simpa only [neg_mul,mul_neg,mul_comm] using hu

include h hp in

theorem largest_occupied_ge_capacity {r : ℕ}
    (hr : r ∈ Finset.Icc 1 n) (hpr : 0 < pi r)
    (htop : ∀ j ∈ Finset.Icc (r+1) n, pi j=0) : n*rho≤(r:ℝ) := by
  by_contra hnot
  obtain ⟨theta,ht,hgt⟩ := commonRate_objective_unbounded (h.route_limit_valid hp)
    (h.route_limit_total hp) hr hpr htop (lt_of_not_ge hnot) (binaryKL rho (pi 1/n))
  exact (not_lt_of_ge (h.full_objectives_bounded hp theta ht)) hgt

include h hp in

theorem broadcast_pos : 0 < pi n := by
  classical
  letI := h.probability
  have ha := h.route_limit_accounting hp
  have hpi := h.route_limit_valid hp
  have hslack := h.route_limit_contact_slack hp
  by_contra hnot
  have hzero : pi n=0 := le_antisymm (le_of_not_gt hnot)
    (hpi.nonneg n (Finset.mem_Icc.mpr ⟨h.proposers_pos,le_rfl⟩))
  obtain ⟨r,hr,hpr,htop⟩ := commonRate_largest_positive h.proposers_pos hpi.nonneg ha.2.2.2.1
  have hrho := h.largest_occupied_ge_capacity hp hr hpr htop
  let k := n-1
  have hk : 1≤k := by dsimp [k]; have := h.two_proposers; omega
  have hkn : k<n := by dsimp [k]; have := h.proposers_pos; omega
  have hkn1 : k+1=n := by dsimp [k]; omega
  have hpartial : ∃ j ∈ Finset.Icc 1 n, 0<pi j ∧ (k:ℝ)*rho<(min k j:ℕ) :=
    ⟨r,hr,hpr,commonRate_partial_open (by omega) hkn h.ratio_pos h.ratio_lt_one hrho⟩
  obtain ⟨theta,ht,hgap⟩ := strict_added_constraint_of_law hk (by omega : k+1≤n)
    hpi hslack ha.2.2.2.1 hpartial
  rw [hkn1,commonRate_fullObjective_eq ha.2.2.1] at hgap
  let Jp := rivalRate n rho k pi
  let gap := fullObjective n rho (F.real (Ioi g)) pi theta-Jp
  have hgap0 : 0<gap := sub_pos.mpr hgap
  let a := exp (-gap/4)
  have ha0 : 0<a := exp_pos _
  have ha1 : a<1 := exp_lt_one_iff.mpr (by linarith)
  have hloga : log a=-gap/4 := log_exp _
  let L := Jp+gap/2
  let U := Jp+3*gap/4
  have hLU : L<U := by dsimp [L,U]; linarith
  have hUF : U<fullObjective n rho (F.real (Ioi g)) pi theta := by
    dsimp [U,gap]; linarith
  have htmpl : HasPopulationRate M (fun t => congestProb n (M t-1) (C t) k pi) Jp :=
    ample_event_rate hk hkn.le (fun _ => hpi) hpi (fun _ _ => tendsto_const_nhds)
      h.population_grows h.capacity_ratio hslack hpartial
  have hlow := (htmpl.rival_pow_mul h.population_grows ha0).eventually_lower_exp
    h.population_grows (show Jp-log a<L by rw [hloga]; dsimp [L]; linarith)
  have hup := eventually_event_bound_of_chernoff le_rfl
    (fun t => visibleClassMass_valid (Γ t) 0) hpi (h.visible_zero_tendsto hp)
    h.population_grows h.capacity_ratio ht (by rw [commonRate_fullObjective_eq ha.2.2.1]; exact hUF)
  obtain ⟨d,hd,hdh,hwidth⟩ := commonRate_domination_width (pi := pi) h.active_pos ha1
  obtain ⟨e,H,he,_,htight⟩ := exists_compact_positive_band F g (show 0<d/4 by linarith)
  have hsmall := (hp n (by simp)).eventually_lt_const (show pi n<d/4 by rw [hzero]; linarith)
  have hclose := commonRate_coordinate_lower (h.visible_zero_tendsto hp) hd
  have hex : ∀ᶠ t in atTop,
      exp (-(M t:ℝ)*L) ≤ actualAllFailure (Γ t) ∧
      actualAllFailure (Γ t) ≤ exp (-(M t:ℝ)*U) := by
    filter_upwards [hlow,hup,hsmall,hclose,h.eventually_commonRate_rows,
      h.eventually_finite_guards] with t hlo hhi hsm hcl hrw hguards
    have hm : 0<M t := by omega
    obtain ⟨w,act,hw,_,hbr,hb,_,hknAct,hbot⟩ := commonRate_select_nonbroadcast (Γ t)
      (h.visible_atomless t) (h.users t) (h.abstention t) ⟨0,hm⟩ hd hdh he hrw.2.2
      (by simpa only [h.common_values t,h.common_fee t] using htight) hsm
    have hdom := commonRate_bottom_domination (Γ t) hpi ha.2.2.1 ha1.le
      hwidth hrw.2.2 hcl hb.le hbot
    have hdprod := commonRate_congest_domination (N := M t-1) (c := C t)
      (k := k) hpi ha0.le hdom
    have hmono := commonRate_congest_antitone (N := M t-1) (c := C t)
      (visibleClassMass_valid (Γ t) act.bid) (show act.routeCount≤k by dsimp [k]; omega)
    have hfail : exp (-(M t:ℝ)*L)≤actualFailure (Γ t) act := by
      rw [actualFailure_eq_congestProb (Γ t) hm (h.ppi t) (h.visible_atomless t)
        (h.feasible_continuations t) act hb]
      exact hlo.trans (hdprod.trans hmono)
    have ham := actual_AM1 (Γ t) hm (h.ppi t) (h.free t) (h.visible_atomless t)
      (h.feasible_continuations t) h.proposers_pos hw act hbr
    refine ⟨hfail.trans ham.2.1,?_⟩
    rw [actualAllFailure_eq_congestProb (Γ t) hm]
    simpa only [neg_mul,mul_neg,mul_comm] using hhi
  apply commonRate_no_exponent_cross (p := fun t => actualAllFailure (Γ t))
    (q := fun t => actualAllFailure (Γ t)) h.population_grows hLU
  exact hex.mono fun _ ht => ⟨ht.1,le_rfl,ht.2⟩

structure CommonRateConclusion (pi : ℕ → ℝ) (J : ℝ) : Prop where
  zero_mass : pi 0 = 1 - F.real (Ioi g)
  singleton_pos : 0 < pi 1
  broadcast_pos : 0 < pi n
  mass : (∑ j ∈ Finset.Icc 1 n, pi j) = F.real (Ioi g)
  mean_slack : (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * pi j) < n * rho
  rate_eq : J = fullRate n rho (F.real (Ioi g)) pi
  rate_pos : 0 < J
  optimizer : ∃ theta > 0, fullObjective n rho (F.real (Ioi g)) pi theta = J ∧
    (∀ s ≥ 0, fullObjective n rho (F.real (Ioi g)) pi s ≤ J) ∧
    (∀ s ≥ 0, fullObjective n rho (F.real (Ioi g)) pi s = J → s = theta)
  all_rate : HasPopulationRate M (fun t => actualAllFailure (Γ t)) J
  deficit_rate : ∀ w > 0, HasPopulationRate M (fun t => actualDeficit (Γ t) w) J
  compact_rate : ∀ lo hi, 0 < lo → lo ≤ hi → ∀ eps > 0,
    ∀ᶠ t in atTop, ∀ w ∈ Icc lo hi,
      |populationLogRate (M t) (actualDeficit (Γ t) w) - J| < eps

include h hp in
lemma full_template_rate : HasPopulationRate M
    (fun t => congestProb n (M t-1) (C t) n pi)
    (fullRate n rho (F.real (Ioi g)) pi) := by
  have htop : ∃ j ∈ Finset.Icc 1 n, 0<pi j ∧ (n:ℝ)*rho<(min n j:ℕ) := by
    refine ⟨n,Finset.mem_Icc.mpr ⟨h.proposers_pos,le_rfl⟩,h.broadcast_pos hp,?_⟩
    simp only [min_self]
    nlinarith [(Nat.cast_pos.mpr h.proposers_pos : (0:ℝ)<n),h.ratio_lt_one]
  have hh := ample_event_rate h.proposers_pos le_rfl
    (fun _ => h.route_limit_valid hp) (h.route_limit_valid hp)
    (fun _ _ => tendsto_const_nhds) h.population_grows h.capacity_ratio
    (h.route_limit_contact_slack hp) htop
  rw [commonRate_fullRate_eq (h.route_limit_total hp)] at hh
  exact hh

include h hp in
lemma actual_full_rate : HasPopulationRate M (fun t => actualAllFailure (Γ t))
    (fullRate n rho (F.real (Ioi g)) pi) := by
  have htop : ∃ j ∈ Finset.Icc 1 n, 0<pi j ∧ (n:ℝ)*rho<(min n j:ℕ) := by
    refine ⟨n,Finset.mem_Icc.mpr ⟨h.proposers_pos,le_rfl⟩,h.broadcast_pos hp,?_⟩
    simp only [min_self]
    nlinarith [(Nat.cast_pos.mpr h.proposers_pos : (0:ℝ)<n),h.ratio_lt_one]
  have hh : HasPopulationRate M
      (fun t => congestProb n (M t-1) (C t) n (visibleClassMass (Γ t) 0))
      (rivalRate n rho n pi) := ample_event_rate h.proposers_pos le_rfl
    (fun t => visibleClassMass_valid (Γ t) 0) (h.route_limit_valid hp)
    (h.visible_zero_tendsto hp) h.population_grows h.capacity_ratio
    (h.route_limit_contact_slack hp) htop
  rw [commonRate_fullRate_eq (h.route_limit_total hp)] at hh
  apply hh.congr
  filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
  exact (actualAllFailure_eq_congestProb (Γ t) ht).symm

include h hp in

theorem deficit_reverse_exponent (J : ℝ)
    (hJ : J = fullRate n rho (F.real (Ioi g)) pi) {z : ℝ} (hz : 0<z) :
    ∀ eps>0, ∀ᶠ t in atTop,
      exp (-(M t:ℝ)*(J+eps)) ≤ actualDeficit (Γ t) z := by
  letI := h.probability
  subst J
  exact commonRate_bottom_deficit_lower Γ F g h.common_values h.common_fee h.population_grows
    h.ppi h.free h.visible_atomless h.feasible_continuations h.users h.abstention
    (h.route_limit_valid hp) h.active_pos (h.route_limit_total hp)
    (h.eventually_commonRate_rows.mono fun _ ht => ht.2.2)
    (h.visible_zero_tendsto hp) (h.full_template_rate hp) hz

include h hp in

theorem common_rate_of_route_limit :
    ∃ J, CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g)
      (rho := rho) pi J := by
  have ha := h.route_limit_accounting hp
  let J := fullRate n rho (F.real (Ioi g)) pi
  obtain ⟨hJ,hopt⟩ := commonRate_full_optimizer h.proposers_pos (h.route_limit_valid hp)
    ha.2.2.1 (h.route_limit_contact_slack hp) h.ratio_lt_one (h.broadcast_pos hp)
  have hall := h.actual_full_rate hp
  have hdef : ∀ w>0, HasPopulationRate M (fun t => actualDeficit (Γ t) w) J := by
    intro w hw
    apply commonRate_log_sandwich h.population_grows hw hall
    · filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
      exact actualDeficit_le_allFailure (Γ t) ht (h.ppi t) (h.free t)
        (h.visible_atomless t) (h.feasible_continuations t) hw.le
    · exact h.deficit_reverse_exponent hp J rfl hw
  refine ⟨J,ha.1,ha.2.2.2.1,h.broadcast_pos hp,ha.2.2.1,ha.2.2.2.2,
    rfl,hJ,hopt,hall,hdef,?_⟩
  intro lo hi hlo hhi
  exact commonRate_compact_log Γ h.population_grows hlo hhi (hdef lo hlo)

theorem common_rate_along
    {J : ℝ}
    (hr : CommonRateConclusion (M := M) (Γ := Γ) (F := F) (g := g) (rho := rho) pi J)
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) :
    CommonRateConclusion (M := M ∘ phi) (Γ := fun t => Γ (phi t))
      (F := F) (g := g) (rho := rho) pi J := by
  refine ⟨hr.zero_mass,hr.singleton_pos,hr.broadcast_pos,hr.mass,hr.mean_slack,
    hr.rate_eq,hr.rate_pos,hr.optimizer,?_,?_,?_⟩
  · exact hr.all_rate.along phi hphi
  · intro w hw
    exact (hr.deficit_rate w hw).along phi hphi
  · intro lo hi hlo hhi eps heps
    exact hphi.eventually (hr.compact_rate lo hi hlo hhi eps heps)

end FreeBaseAmpleSequence
end FCAppendix.Bayes
