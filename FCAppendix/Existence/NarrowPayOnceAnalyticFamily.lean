import FCAppendix.Existence.NarrowPayOnceDerivativeBounds
import FCAppendix.Existence.NarrowPayOnceSurplus

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory

structure AnalyticEquilibrium (n R c : ℕ) (w0 kappa eps delta C slopeLo slopeHi : ℝ)
    (nu : Measure (Icc (w0-delta) (w0+delta))) [IsProbabilityMeasure nu] where
  control : FiniteScoreControl n R c w0 kappa eps delta
  bid : control.strategyBand
  strictMono : StrictMono bid.val
  stationary : ∀v : control.valueBand,finiteExpectedScore (R:=R) n c nu bid.val v (bid.val v)=0
  globalOptimal : ∀(v : control.valueBand) (z : ℝ),0<z →
    finiteExpectedUtility (R:=R) n c nu bid.val v z≤
      finiteExpectedUtility (R:=R) n c nu bid.val v (bid.val v)
  bid_lt_value : ∀v : control.valueBand,bid.val v<(v:ℝ)
  utility_pos : ∀v : control.valueBand,0<finiteExpectedUtility (R:=R) n c nu bid.val v (bid.val v)
  reference_distance : ∀v : control.valueBand,|bid.val v-referenceBid n R c w0|≤C*delta
  bidExtension : ℝ→ℝ
  extension_agrees : ∀v : control.valueBand,bidExtension v=bid.val v
  extension_c1 : ∀w∈control.openValueBand,ContDiffAt ℝ 1 bidExtension w
  derivative_lower : ∀w∈control.openValueBand,slopeLo≤deriv bidExtension w
  derivative_upper : ∀w∈control.openValueBand,deriv bidExtension w ≤ slopeHi

namespace AnalyticEquilibrium
variable {n R c : ℕ} {w0 kappa eps delta C slopeLo slopeHi : ℝ}
    {nu : Measure (Icc (w0-delta) (w0+delta))} [IsProbabilityMeasure nu]
    (E : AnalyticEquilibrium n R c w0 kappa eps delta C slopeLo slopeHi nu)

theorem bid_pos (v : E.control.valueBand) : 0<E.bid.val v :=
  E.control.lower_pos.trans_le (E.bid.property v).1

theorem bid_law_atomless [NullSingletonClass nu] : NullSingletonClass (nu.map E.bid.val) := by
  constructor
  intro z
  rw [Measure.map_apply E.bid.val.continuous.measurable (measurableSet_singleton z)]
  apply Set.Subsingleton.measure_zero _ nu
  intro x hx y hy
  apply E.strictMono.injective
  exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm

end AnalyticEquilibrium

theorem exists_uniform_analytic_family {n : ℕ} (hn : 2≤n) {w0 lo hi : ℝ}
    (hw0 : 0<w0) (hlo : 0<lo) (hlohi : lo≤hi) (hhi : hi<1) :
    ∃kappa eps deltaStar C slopeLo slopeHi : ℝ,
      0<kappa ∧ 0<eps ∧ 0<deltaStar ∧ 0<C ∧ 0<slopeLo ∧ 0<slopeHi ∧ deltaStar≤w0/2 ∧
      ∀(R c : ℕ),1≤c → c≤R → density R c∈Icc lo hi →
      ∀delta∈Icc (0:ℝ) deltaStar,
      ∀(nu : Measure (Icc (w0-delta) (w0+delta))) [IsProbabilityMeasure nu],
      Nonempty (AnalyticEquilibrium n R c w0 kappa eps delta C slopeLo slopeHi nu) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  obtain ⟨kappa,eps,deltaLocal,hk,he,hd,hδw,heps,hlocal⟩ :=
    exists_uniform_small_finiteScoreControl hn hw0 hlo hlohi hhi
      (fun kappa=>(1-hi)*kappa/(16*(n:ℝ))) (fun kappa hk=>by positivity)
  obtain ⟨M,hM,hcurv⟩ := exists_uniform_curvature_upper hn hw0 hlo hhi
  obtain ⟨deltaGlobal,hdG,hglobal⟩ := exists_uniform_global_window hn hw0 hlo hhi hk he
  let deltaStar := min deltaLocal deltaGlobal
  let T := (n:ℝ)*firstJetBound n (kappa/2)
  let C := 2*T/kappa
  let slopeLo := valueSlopeFloor n kappa w0 hi/(M+kappa/3)
  let slopeHi := T/(2*kappa/3)
  have hT : 0<T := by dsimp [T,firstJetBound]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  have hlo' : 0<slopeLo := div_pos (valueSlopeFloor_pos hn hk hw0 hhi) (by positivity)
  have hhi' : 0<slopeHi := by dsimp [slopeHi]; positivity
  refine ⟨kappa,eps,deltaStar,C,slopeLo,slopeHi,hk,he,lt_min hd hdG,hC,hlo',hhi',
    (min_le_left _ _).trans hδw,?_⟩
  intro R c hc hcR hrho delta hdelta nu _
  let U := hlocal R c hc hcR hrho delta ⟨hdelta.1,hdelta.2.trans (min_le_left _ _)⟩
  obtain ⟨beta,hroot,_hunique⟩ := U.exists_unique_stationary nu
  let f := U.smoothReply nu beta.val beta.val.continuous beta.property
  refine ⟨{
    control := U
    bid := beta
    strictMono := U.stationary_strictMono nu beta hroot
    stationary := hroot
    globalOptimal := ?_
    bid_lt_value := U.stationary_bid_lt_value nu beta hroot
    utility_pos := U.stationary_utility_pos nu beta hroot
    reference_distance := ?_
    bidExtension := f
    extension_agrees := ?_
    extension_c1 := ?_
    derivative_lower := ?_
    derivative_upper := ?_
  }⟩
  · exact hglobal R c delta U hrho (hdelta.2.trans (min_le_right _ _)) nu beta hroot
  · exact U.stationary_displacement nu beta hroot
  · exact U.smoothReply_eq_stationary nu beta.val beta.val.continuous beta.property hroot
  · exact U.contDiffAt_smoothReply nu beta.val beta.val.continuous beta.property
  · intro w hw
    exact (U.deriv_smoothReply_bounds nu beta.val beta.val.continuous beta.property hhi hM hrho.2 heps
      (hcurv R c hc hcR hrho) w hw).1
  · intro w hw
    exact (U.deriv_smoothReply_bounds nu beta.val beta.val.continuous beta.property hhi hM hrho.2 heps
      (hcurv R c hc hcR hrho) w hw).2

end FCAppendix.Existence.NarrowPayOnce
