import FCAppendix.Affine.Hybrid.PopulationLaw
import FCAppendix.Affine.LowBody.HiddenRoute
import FCAppendix.Affine.LowBody.ExactReferenceSurplus

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes

namespace NativeLowIncentives

def broadcast (b : ℝ) (hb : 0 ≤ b) : JointAction 2:=⟨b,hb,2,le_rfl⟩

theorem payoff_nonpos_of_value_le_bid {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (hg : Gamma.g=0) (i : Fin m) (v : ℝ)
    (a : JointAction 2) (hbv : v ≤ a.bid) : (problem Gamma i).payoff v a ≤ 0 := by
  have hh:=((problem Gamma i).outcome a).utility_le_bid_net_success v a.bid Gamma.g
    Gamma.A Gamma.G a.bid_nonneg Gamma.g_nonneg
  change (problem Gamma i).payoff v a ≤ _ at hh
  rw [hg,sub_zero] at hh
  exact hh.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith)
    ((problem Gamma i).outcome a).success_nonneg)

theorem payoff_nonpos_of_zero_routes {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (i : Fin m) (v : ℝ)
    (a : JointAction 2) (hk : a.routeCount=0) : (problem Gamma i).payoff v a ≤ 0 := by
  have hl:=load_le_routeCount_mul_success Gamma i a
  rw [hk,Nat.cast_zero,zero_mul] at hl
  have hs : ((problem Gamma i).outcome a).success=0:=
    le_antisymm (((problem Gamma i).outcome a).success_le_load.trans hl)
      ((problem Gamma i).outcome a).success_nonneg
  have hh:=((problem Gamma i).outcome a).utility_le_bid_net_success v a.bid Gamma.g
    Gamma.A Gamma.G a.bid_nonneg Gamma.g_nonneg
  change (problem Gamma i).payoff v a ≤ _ at hh
  simpa only [hs,mul_zero] using hh

theorem best_response {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1)) {d ξ η : ℝ}
    (hξ : 0<ξ) (hξh : ξ ≤ 1/2) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Gamma.A=Schedule.affine 2 η hη0 hη1) (hg : Gamma.g=0)
    (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowBody.LowValue d))
    (w b : LowBody.LowValue d) (hw : 0<w.1) (hb : 0<b.1)
    (hIC : ∀y : ℝ,0 ≤ y → LowBody.exactExpectedPayoff N d ξ c categories G (w.1,y) ≤
      LowBody.exactExpectedPayoff N d ξ c categories G (w.1,b.1))
    (hpositive : ∀a : JointAction 2,a.routeCount=2→0<a.bid→a.bid ≤ d→
      (problem Gamma i).payoff w.1 a=LowBody.exactExpectedPayoff N d ξ c categories G (w.1,a.bid))
    (hzero : ∀a : JointAction 2,a.routeCount=2→a.bid=0→∀(y : ℝ)(hy : 0<y),y ≤ d→
      (problem Gamma i).payoff w.1 a ≤ (problem Gamma i).payoff w.1 (broadcast y hy.le)+2*y)
    (hell : 0<(CommonList.iid categories N).prob (LowBody.LocalUnderflow c 0))
    (hsmall : (CommonList.iid categories N).prob (LowBody.BothUnderflow c) ≤
      (CommonList.iid categories N).prob (LowBody.LocalUnderflow c 0)/4)
    (hdup : ∀a : JointAction 2,a.routeCount=2→a.bid ≤ w.1→
      ((problem Gamma i).outcome a).duplicates ≤
        (CommonList.iid categories N).prob (LowBody.BothUnderflow c)) :
    (problem Gamma i).BestResponse w.1 (lowBroadcast b) := by
  let star:=lowBroadcast b
  let ref:=broadcast (w.1/2) (by linarith : 0 ≤ w.1/2)
  have href : (problem Gamma i).payoff w.1 ref=
      LowBody.exactExpectedPayoff N d ξ c categories G (w.1,w.1/2):=
    hpositive ref rfl (by dsimp [ref,broadcast]; linarith) (by dsimp [ref,broadcast]; linarith [w.property.2])
  have hstar : (problem Gamma i).payoff w.1 star=
      LowBody.exactExpectedPayoff N d ξ c categories G (w.1,b.1):=
    hpositive star rfl hb b.property.2
  have hcompare : w.1*((CommonList.iid categories N).prob (LowBody.LocalUnderflow c 0)-
      (CommonList.iid categories N).prob (LowBody.BothUnderflow c))/2 ≤
      (problem Gamma i).payoff w.1 ref:=by
    rw [href]
    simpa only [div_mul_eq_mul_div] using
      LowBody.exactExpectedPayoff_half_bid_lower (N:=N) hξ hξh hw c categories G
  have hstarpos : 0<(problem Gamma i).payoff w.1 star:=by
    have hh:=hIC (w.1/2) (by linarith)
    rw [←hstar,←href] at hh
    have hp:=mul_pos hw (show 0<(CommonList.iid categories N).prob (LowBody.LocalUnderflow c 0)-
      (CommonList.iid categories N).prob (LowBody.BothUnderflow c) by linarith)
    linarith
  have htwo : ∀a : JointAction 2,a.routeCount=2→
      (problem Gamma i).payoff w.1 a ≤ (problem Gamma i).payoff w.1 star := by
    intro a hk
    by_cases hv : w.1 ≤ a.bid
    · exact (payoff_nonpos_of_value_le_bid Gamma hg i _ a hv).trans hstarpos.le
    · have had : a.bid ≤ d:=(le_of_not_ge hv).trans w.property.2
      by_cases ha : 0<a.bid
      · rw [hpositive a hk ha had,hstar]
        exact hIC a.bid a.bid_nonneg
      · have ha0 : a.bid=0:=le_antisymm (le_of_not_gt ha) a.bid_nonneg
        apply le_of_forall_pos_le_add
        intro eps heps
        let y:=min (w.1/2) (eps/2)
        have hy : 0<y:=lt_min (by linarith) (by linarith)
        have hyd : y ≤ d:=(min_le_left _ _).trans (by linarith [w.property.2])
        have hz:=hzero a hk ha0 y hy hyd
        have heq:=hpositive (broadcast y hy.le) rfl hy hyd
        have hyy:=hIC y hy.le
        rw [heq] at hz
        rw [hstar]
        change (problem Gamma i).payoff w.1 a ≤ LowBody.exactExpectedPayoff N d ξ c categories G (w.1,y)+2*y at hz
        have hey : 2*y ≤ eps:=by dsimp [y]; linarith [min_le_right (w.1/2) (eps/2)]
        linarith
  intro a
  by_cases hk2 : a.routeCount=2
  · exact htwo a hk2
  · by_cases hk1 : a.routeCount=1
    · exact (LowBody.native_broadcast_optimum_strictly_beats_one_route Gamma hη0 hη1 hA hg i hw
        hell ((CommonList.iid categories N).prob_nonneg _) hsmall star ref rfl hcompare htwo
        (fun a ha hav=>hdup (LowBody.addSecondRoute a) rfl hav) a hk1).le
    · have hk0 : a.routeCount=0:=by have hh:=a.routeCount_le; omega
      exact (payoff_nonpos_of_zero_routes Gamma i _ a hk0).trans hstarpos.le

end NativeLowIncentives
end FCAppendix.Affine.Hybrid
