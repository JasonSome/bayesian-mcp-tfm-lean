import FCAppendix.Ample.BoundaryService
import FCAppendix.Ample.BoundaryActualContact
import FCAppendix.Ample.CommonRateAM3

noncomputable section
namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators
open Ample Ample.CompletionDraft
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g : ℝ}

namespace FreeBaseBoundarySequence
variable (h : FreeBaseBoundarySequence M C Γ B F g)
  {pi : ℕ → ℝ} (hp : RouteLimit Γ pi)

include h in
lemma eventually_commonRate_rows :
    ∀ᶠ t in atTop,
      (∀ j, 1≤j → visibleClassMass (Γ t) 0 j=actualRouteMass (Γ t) j) ∧
      actualRouteMass (Γ t) 0=1-F.real (Ioi g) ∧
      positiveRouteMass (Γ t) (fun _ => True)=F.real (Ioi g) := by
  filter_upwards [h.eventually_finite_guards] with t ht
  simpa only [h.common_values t,h.common_fee t] using commonRate_primitive_row (Γ t)
    (by omega) (by have := h.proposers_two; omega) ht.2.1 (h.ppi t)
    (h.visible_atomless t) (h.feasible_continuations t) (h.users t)
    (h.abstention t) (h.reject_zero t)

include h hp in
lemma visible_zero_tendsto : ∀ j ∈ Finset.Icc 1 n,
    Tendsto (fun t => visibleClassMass (Γ t) 0 j) atTop (𝓝 (pi j)) := by
  intro j hj
  apply (hp j (Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hj).2⟩)).congr'
  filter_upwards [h.eventually_commonRate_rows] with t ht
  exact (ht.1 j (Finset.mem_Icc.mp hj).1).symm

include h hp in

lemma boundary_route_accounting :
    (∀ j ∈ Finset.Icc 0 n, 0≤pi j) ∧
    (∑ j ∈ Finset.Icc 1 n, pi j)=F.real (Ioi g) ∧ 0<pi 1 := by
  have ha := h.acceptance
  obtain ⟨a,ha0,hfloor⟩ := ha.singleton_floor
  have hnonneg : ∀ j ∈ Finset.Icc 0 n, 0≤pi j := by
    intro j hj
    exact ge_of_tendsto (hp j hj) (Eventually.of_forall fun _ => measureReal_nonneg)
  have hs := tendsto_finsetSum (Finset.Icc 1 n) (fun j hj =>
    hp j (Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hj).2⟩))
  have hs1 : a≤pi 1 := ge_of_tendsto
    (hp 1 (Finset.mem_Icc.mpr ⟨by omega,by have := h.proposers_two; omega⟩)) hfloor
  exact ⟨hnonneg,tendsto_nhds_unique hs ha.participation,ha0.trans_le hs1⟩

include h hp in
lemma route_limit_valid : ValidLaw n pi where
  nonneg j hj := (h.boundary_route_accounting hp).1 j
    (Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hj).2⟩)
  total_le := by rw [(h.boundary_route_accounting hp).2.1]; exact h.active_le_one

include h hp in
lemma singleton_mass_tendsto :
    Tendsto (fun t => positiveRouteMass (Γ t) (fun k => k=1)) atTop (𝓝 (pi 1)) := by
  simpa only [positiveRouteMass_class_eq _ (by omega : 1≤1)] using
    h.visible_zero_tendsto hp 1
      (Finset.mem_Icc.mpr ⟨le_rfl,by have := h.proposers_two; omega⟩)

include h hp in

lemma lowest_singleton_rate : HasPopulationRate M
    (fun t => congestProb n (M t-1) (C t) 1
      (singletonOnly (positiveRouteMass (Γ t) (fun k => k=1)))) (-log (pi 1/n)) := by
  have hn : 0<n := by have := h.proposers_two; omega
  let pseq := fun t => positiveRouteMass (Γ t) (fun k => k=1)
  let mu := fun t => contactLaw n (singletonOnly (pseq t))
    (singletonOnly_valid hn (positiveRouteMass_nonneg (Γ t) _) (positiveRouteMass_le_one (Γ t) _))
  have hp1 : 0<pi 1 := (h.boundary_route_accounting hp).2.2
  have hmass : Tendsto (fun t => Shortage.allMass (mu t) (selected n 1)) atTop
      (𝓝 (pi 1/n)) := by
    simpa only [mu,Shortage.allMass_contactLaw_one hn,singletonOnly_marginal hn] using
      (h.singleton_mass_tendsto hp).div_const (n:ℝ)
  have hr : HasPopulationRate M
      (fun t => Shortage.congestionProb (mu t) (M t-1) (C t) (selected n 1))
      (-log (pi 1/n)) := boundary_contact_logRate mu M C (selected n 1)
    h.population_grows h.capacity_ratio h.strict_shortage
    (div_pos hp1 (Nat.cast_pos.mpr hn)) hmass
  simpa only [mu,pseq,Shortage.congestionProb_contactLaw] using hr

include h hp in

lemma full_superexponential_of_broadcast_zero (hzero : pi n=0) :
    Superexponential M (fun t => actualAllFailure (Γ t)) := by
  have hn : 0<n := by have := h.proposers_two; omega
  let mu := fun t => contactLaw n (visibleClassMass (Γ t) 0) (visibleClassMass_valid (Γ t) 0)
  have hmass : Tendsto (fun t => Shortage.allMass (mu t) (selected n n)) atTop (𝓝 0) := by
    simpa only [mu,selected_self,Shortage.allMass_contactLaw_univ hn,hzero] using
      h.visible_zero_tendsto hp n (Finset.mem_Icc.mpr ⟨hn,le_rfl⟩)
  have hr := boundary_contact_zero_mass mu M C (selected n n) h.population_grows
    h.capacity_ratio h.strict_shortage hmass
  intro R
  filter_upwards [hr R,h.population_grows.eventually_gt_atTop 0] with t ht hm
  rw [actualAllFailure_eq_congestProb (Γ t) hm]
  simpa only [mu,Shortage.congestionProb_contactLaw] using ht

include h hp in

theorem broadcast_mass_from_lowest_singleton : 0<pi n := by
  have hn : 0<n := by have := h.proposers_two; omega
  have hnonneg := (h.boundary_route_accounting hp).1 n (by simp)
  by_contra hnot
  have hzero : pi n=0 := le_antisymm (le_of_not_gt hnot) hnonneg
  let J := -log (pi 1/n)
  have hlow := (h.lowest_singleton_rate hp).eventually_lower_exp h.population_grows
    (show J<J+1 by linarith)
  have hhigh := h.full_superexponential_of_broadcast_zero hp hzero (J+2)
  apply commonRate_no_exponent_cross (M := M)
    (p := fun t => congestProb n (M t-1) (C t) 1
      (singletonOnly (positiveRouteMass (Γ t) (fun k => k=1))))
    (q := fun t => actualAllFailure (Γ t)) h.population_grows
    (show J+1<J+2 by linarith)
  filter_upwards [hlow,hhigh,h.eventually_finite_guards] with t hl hh ht
  refine ⟨hl,commonRate_AM3_lower (Γ t) (by omega) hn ht.2.1 ht.2.2
    (h.ppi t) (h.free t) (h.visible_atomless t) (h.feasible_continuations t)
    (h.users t) (h.abstention t),?_⟩
  simpa only [neg_mul,mul_neg,mul_comm] using hh

include h hp in

theorem broadcast_lt_one_from_singleton : pi n<1 := by
  classical
  have ha := h.boundary_route_accounting hp
  have hn : 0<n := by have := h.proposers_two; omega
  have hne : (1:ℕ)≠n := by have := h.proposers_two; omega
  have hsub : ({1,n} : Finset ℕ) ⊆ Finset.Icc 1 n := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_Icc.mpr ⟨le_rfl,hn⟩
    · have he : j=n := Finset.mem_singleton.mp hj
      subst j
      exact Finset.mem_Icc.mpr ⟨hn,le_rfl⟩
  have hs : (∑ j ∈ ({1,n} : Finset ℕ), pi j) ≤ ∑ j ∈ Finset.Icc 1 n, pi j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ =>
      ha.1 j (Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hj).2⟩))
  have hs' : pi 1+pi n≤F.real (Ioi g) := by simpa [hne,ha.2.1] using hs
  linarith [ha.2.2,h.active_le_one]

structure RateConclusion (pi : ℕ → ℝ) : Prop where
  nonneg : ∀ j ∈ Finset.Icc 0 n, 0 ≤ pi j
  mass : ∑ j ∈ Finset.Icc 1 n, pi j = F.real (Ioi g)
  singleton_pos : 0 < pi 1
  broadcast_pos : 0 < pi n
  broadcast_lt_one : pi n < 1
  all_rate : HasPopulationRate M (fun t => actualAllFailure (Γ t)) (-log (pi n))
  deficit_rate : ∀ w > 0,
    HasPopulationRate M (fun t => actualDeficit (Γ t) w) (-log (pi n))
  compact_rate : ∀ lo hi, 0 < lo → lo ≤ hi → ∀ eps > 0,
    ∀ᶠ t in atTop, ∀ w ∈ Icc lo hi,
      |populationLogRate (M t) (actualDeficit (Γ t) w) + log (pi n)| < eps

include h hp in
lemma actual_full_boundary_rate :
    HasPopulationRate M (fun t => actualAllFailure (Γ t)) (-log (pi n)) := by
  have hn : 0<n := by have := h.proposers_two; omega
  let mu := fun t => contactLaw n (visibleClassMass (Γ t) 0) (visibleClassMass_valid (Γ t) 0)
  have hmass : Tendsto (fun t => Shortage.allMass (mu t) (selected n n)) atTop
      (𝓝 (pi n)) := by
    simpa only [mu,selected_self,Shortage.allMass_contactLaw_univ hn] using
      h.visible_zero_tendsto hp n (Finset.mem_Icc.mpr ⟨hn,le_rfl⟩)
  have hr : HasPopulationRate M
      (fun t => Shortage.congestionProb (mu t) (M t-1) (C t) (selected n n))
      (-log (pi n)) := boundary_contact_logRate mu M C (selected n n) h.population_grows
    h.capacity_ratio h.strict_shortage (h.broadcast_mass_from_lowest_singleton hp) hmass
  apply hr.congr
  filter_upwards [h.population_grows.eventually_gt_atTop 0] with t hm
  rw [actualAllFailure_eq_congestProb (Γ t) hm]
  exact Shortage.congestionProb_contactLaw _ _ _ _ _

include h hp in
lemma full_template_rate : HasPopulationRate M
    (fun t => congestProb n (M t-1) (C t) n pi) (-log (pi n)) := by
  have hn : 0<n := by have := h.proposers_two; omega
  let mu := contactLaw n pi (h.route_limit_valid hp)
  have hmass : Tendsto (fun _ : ℕ => Shortage.allMass mu (selected n n)) atTop (𝓝 (pi n)) := by
    simpa only [mu,selected_self,Shortage.allMass_contactLaw_univ hn] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => pi n) atTop (𝓝 (pi n)))
  have hr : HasPopulationRate M
      (fun t => Shortage.congestionProb mu (M t-1) (C t) (selected n n))
      (-log (pi n)) := boundary_contact_logRate (fun _ => mu) M C (selected n n)
    h.population_grows h.capacity_ratio h.strict_shortage
    (h.broadcast_mass_from_lowest_singleton hp) hmass
  simpa only [mu,Shortage.congestionProb_contactLaw] using hr

include h hp in

lemma boundary_bottom_band_common_rate :
    (∀ w>0, HasPopulationRate M (fun t => actualDeficit (Γ t) w) (-log (pi n))) ∧
    (∀ lo hi, 0<lo → lo≤hi → ∀ eps>0, ∀ᶠ t in atTop, ∀ w ∈ Icc lo hi,
      |populationLogRate (M t) (actualDeficit (Γ t) w)+log (pi n)|<eps) := by
  letI := h.probability
  have hall := h.actual_full_boundary_rate hp
  have hdef : ∀ w>0, HasPopulationRate M (fun t => actualDeficit (Γ t) w) (-log (pi n)) := by
    intro w hw
    apply commonRate_log_sandwich h.population_grows hw hall
    · filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
      exact actualDeficit_le_allFailure (Γ t) ht (h.ppi t) (h.free t)
        (h.visible_atomless t) (h.feasible_continuations t) hw.le
    · exact commonRate_bottom_deficit_lower Γ F g h.common_values h.common_fee
        h.population_grows h.ppi h.free h.visible_atomless h.feasible_continuations
        h.users h.abstention (h.route_limit_valid hp) h.active_pos
        (h.boundary_route_accounting hp).2.1
        (h.eventually_commonRate_rows.mono fun _ ht => ht.2.2)
        (h.visible_zero_tendsto hp) (h.full_template_rate hp) hw
  refine ⟨hdef,?_⟩
  intro lo hi hlo hhi
  simpa only [sub_neg_eq_add] using commonRate_compact_log Γ h.population_grows hlo hhi (hdef lo hlo)

include h in

theorem common_rate {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) :
    RateConclusion (M := M) (Γ := Γ) (F := F) (g := g) pi := by
  have ha := h.boundary_route_accounting hp
  have hd := h.boundary_bottom_band_common_rate hp
  exact ⟨ha.1,ha.2.1,ha.2.2,h.broadcast_mass_from_lowest_singleton hp,
    h.broadcast_lt_one_from_singleton hp,h.actual_full_boundary_rate hp,hd.1,hd.2⟩

theorem common_rate_along
    (hr : RateConclusion (M := M) (Γ := Γ) (F := F) (g := g) pi)
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) :
    RateConclusion (M := M ∘ phi) (Γ := fun t => Γ (phi t)) (F := F) (g := g) pi := by
  refine ⟨hr.nonneg,hr.mass,hr.singleton_pos,hr.broadcast_pos,hr.broadcast_lt_one,?_,?_,?_⟩
  · exact hr.all_rate.along phi hphi
  · intro w hw
    exact (hr.deficit_rate w hw).along phi hphi
  · intro lo hi hlo hhi eps heps
    exact hphi.eventually (hr.compact_rate lo hi hlo hhi eps heps)

theorem RateConclusion.rate_pos
    (hr : RateConclusion (M := M) (Γ := Γ) (F := F) (g := g) pi) : 0 < -log (pi n) :=
  neg_pos.mpr (log_neg hr.broadcast_pos hr.broadcast_lt_one)

end FreeBaseBoundarySequence
end FCAppendix.Bayes.CompletionDraft
