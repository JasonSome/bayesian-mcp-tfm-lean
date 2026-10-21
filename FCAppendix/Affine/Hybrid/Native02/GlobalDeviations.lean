import FCAppendix.Affine.Hybrid.NativeLowIncentives
import FCAppendix.Affine.Hybrid.Native02.OriginalPopulation
import FCAppendix.Affine.Hybrid.Native02.ExceptionalMenus

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Existence.Distributional

theorem partition_bid {d L U R b : ℝ} (_hdL : d<L) (_hLU : L ≤ U) (_hUR : U<R) :
    b ≤ d ∨ (d<b ∧ b<L) ∨ b∈ Icc L U ∨ (U<b ∧ b<R) ∨ R ≤ b := by
  by_cases hd : b ≤ d
  · exact Or.inl hd
  by_cases hL : b<L
  · exact Or.inr (Or.inl ⟨lt_of_not_ge hd,hL⟩)
  by_cases hU : b ≤ U
  · exact Or.inr (Or.inr (Or.inl ⟨le_of_not_gt hL,hU⟩))
  by_cases hR : b<R
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨lt_of_not_ge hU,hR⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (le_of_not_gt hR))))

theorem routes_zero_one_two (a : JointAction 2) :
    a.routeCount=0 ∨ a.routeCount=1 ∨ a.routeCount=2 := by
  have h:=a.routeCount_le
  omega

theorem raw_above_floor_payoff_le {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (hg : G.g=0)
    (i : Fin m) (v R : ℝ) (a : JointAction 2) (hR : R≤ a.bid) :
    (problem G i).payoff v a≤ max (v-R) 0 := by
  have h := ((problem G i).outcome a).utility_le_bid_net_success v a.bid G.g
    G.A G.G a.bid_nonneg G.g_nonneg
  change (problem G i).payoff v a≤ _ at h
  rw [hg,sub_zero] at h
  by_cases hva : v≤ a.bid
  · exact (NativeLowIncentives.payoff_nonpos_of_value_le_bid G hg i v a hva).trans
      (le_max_right _ _)
  · have hp : 0≤ v-a.bid := sub_nonneg.mpr (le_of_not_ge hva)
    have hm := mul_le_of_le_one_right hp ((problem G i).outcome a).success_le_one
    exact h.trans (hm.trans ((sub_le_sub_left hR v).trans (le_max_left _ _)))

theorem max_floor_menu_lt {v R u : ℝ} (h0 : 0<u) (hR : v-R<u) :
    max (v-R) 0<u := max_lt hR h0

theorem all_joint_actions_of_finite_bounds {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (hg : G.g=0)
    (i : Fin m) (v d L U R : ℝ) (hdL : d<L) (hLU : L ≤ U) (hUR : U<R)
    (star : JointAction 2) (hstar : 0 ≤ (problem G i).payoff v star)
    (hlow : ∀ a : JointAction 2,a.bid ≤ d→
      (problem G i).payoff v a ≤ (problem G i).payoff v star)
    (hbox1 : ∀ a : JointAction 2,a.routeCount=1→ a.bid∈ Icc L U→
      (problem G i).payoff v a ≤ (problem G i).payoff v star)
    (hbox2 : ∀ a : JointAction 2,a.routeCount=2→ a.bid∈ Icc L U→
      (problem G i).payoff v a ≤ (problem G i).payoff v star)
    (hex1 : ∀ a : JointAction 2,a.routeCount=1→ d<a.bid→ a.bid<R→ a.bid∉Icc L U→
      (problem G i).payoff v a ≤ (problem G i).payoff v star)
    (hex2 : ∀ a : JointAction 2,a.routeCount=2→ d<a.bid→ a.bid<R→ a.bid∉Icc L U→
      (problem G i).payoff v a ≤ (problem G i).payoff v star)
    (hupper1 : ∀ a : JointAction 2,a.routeCount=1→ R ≤ a.bid→
      (problem G i).payoff v a ≤ (problem G i).payoff v star)
    (hupper2 : ∀ a : JointAction 2,a.routeCount=2→ R ≤ a.bid→
      (problem G i).payoff v a ≤ (problem G i).payoff v star) :
    (problem G i).BestResponse v star := by
  intro a
  by_cases hvalue : v ≤ a.bid
  · exact (NativeLowIncentives.payoff_nonpos_of_value_le_bid G hg i v a hvalue).trans hstar
  rcases routes_zero_one_two a with hz|h1|h2
  · exact (NativeLowIncentives.payoff_nonpos_of_zero_routes G i v a hz).trans hstar
  · rcases partition_bid (b:=a.bid) hdL hLU hUR with hlo|hleft|hbox|hright|hup
    · exact hlow a hlo
    · exact hex1 a h1 hleft.1 (hleft.2.trans_le (hLU.trans hUR.le))
        (fun hb=>(not_lt.mpr hb.1) hleft.2)
    · exact hbox1 a h1 hbox
    · exact hex1 a h1 (hdL.trans_le (hLU.trans hright.1.le)) hright.2
        (fun hb=>(not_lt.mpr hb.2) hright.1)
    · exact hupper1 a h1 hup
  · rcases partition_bid (b:=a.bid) hdL hLU hUR with hlo|hleft|hbox|hright|hup
    · exact hlow a hlo
    · exact hex2 a h2 hleft.1 (hleft.2.trans_le (hLU.trans hUR.le))
        (fun hb=>(not_lt.mpr hb.1) hleft.2)
    · exact hbox2 a h2 hbox
    · exact hex2 a h2 (hdL.trans_le (hLU.trans hright.1.le)) hright.2
        (fun hb=>(not_lt.mpr hb.2) hright.1)
    · exact hupper2 a h2 hup

theorem compact_strict_margin {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {f g : X→ℝ} (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hstrict : ∀ x∈ K,g x<f x) :
    ∃eps>0,∀ x∈ K,g x+eps ≤ f x := by
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne (hf.sub hg)
  rw [isMinOn_iff] at hmin
  refine ⟨f x-g x,sub_pos.mpr (hstrict x hx),?_⟩
  intro y hy
  have hh:=hmin y hy
  change f x-g x ≤ f y-g y at hh
  linarith

theorem strict_order_of_uniform_errors {x y u w eps delta : ℝ}
    (hgap : w+delta ≤ u) (hinc : |x-u| ≤ eps) (hdev : y ≤ w+eps)
    (hsmall : 2*eps<delta) : y<x := by
  have hlo := (abs_le.mp hinc).1
  linarith

theorem eventually_strict_order_of_uniform_errors
    {X A : Type*} {K : Set X} {Inc : ℕ→ X→ A→ℝ} {Dev : ℕ→ X→ A→ℝ}
    {u w : X→ℝ} {good : ℕ→ X→ A→ Prop} {eps : ℕ→ℝ} {delta : ℝ}
    (hdelta : 0<delta) (heps : Tendsto eps atTop (𝓝 0))
    (hgap : ∀ v∈ K,w v+delta ≤ u v)
    (hfinite : ∀ᶠm in atTop,∀ v∈ K,∀ a,good m v a→
      |Inc m v a-u v| ≤ eps m ∧ Dev m v a ≤ w v+eps m) :
    ∀ᶠm in atTop,∀ v∈ K,∀ a,good m v a→ Dev m v a<Inc m v a := by
  have he : Tendsto (fun m=>2*eps m) atTop (𝓝 0) := by
    simpa only [mul_zero] using heps.const_mul 2
  filter_upwards [hfinite,he.eventually (Iio_mem_nhds hdelta)] with m hm hsmall
  intro v hv a ha
  exact strict_order_of_uniform_errors (hgap v hv) (hm v hv a ha).1
    (hm v hv a ha).2 hsmall

theorem active_box_IC_of_joint_numeric_IC
    {m c : ℕ} {vlo vhi L U : ℝ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (i : Fin m) (hL : 0 ≤ L)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu)
    (numeric : ActiveValue vlo vhi×ActiveBaseBid L U→ℝ)
    (hIC : ∀ᵐx ∂(pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)),
      ∀ b : ActiveBaseBid L U,numeric (x.1,b) ≤ numeric x)
    (htransport : ∀ v : ActiveValue vlo vhi,∀ b : ActiveBaseBid L U,
      (problem G i).payoff v.1 (activeBroadcast hL b)=numeric (v,b)) :
    ∀ᵐx ∂(pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)),
      ∀ b : ActiveBaseBid L U,(problem G i).payoff x.1.1 (activeBroadcast hL b) ≤
        (problem G i).payoff x.1.1 (activeBroadcast hL x.2) := by
  filter_upwards [hIC] with x hx
  intro b
  rw [htransport,htransport]
  exact hx b

end FCAppendix.Affine.Hybrid.Native02
