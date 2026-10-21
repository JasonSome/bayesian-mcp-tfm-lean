import FCAppendix.Affine.Hybrid.NativeLowPositive
import FCAppendix.Affine.Hybrid.NativeLowBounds

set_option maxHeartbeats 2400000
noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes LowBody Classical
open NativeContinuation
open Existence.Distributional
variable {N c : ℕ} {d U η : ℝ}

theorem population_low_joint_best_response (hd:0 ≤ d) (hdU:d ≤ U)
    (s a h : ℝ) (hs:0 ≤ s) (ha:0 ≤ a) (hh:0 ≤ h) (hsum:s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hη0:0 ≤ η) (hη1:η<1)
    (L : ActualAtomlessLowLimit N d ((1-η)/2) c (categoryLaw s a h hs ha hh hsum Gref) mu)
    (PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hactive:∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<((1+η)/2)*x.2.bid ∧
      x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper:∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),U<x.2.bid ∧ x.2.routeCount=1)
    (hell:0<(CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0))
    (hsmall:(CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0)/4)
    (i : Fin (N+1)) :
    let P:=populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) PA PH
    let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
    ∀ᵐx ∂(L.joint.1 : Measure (LowValue d×LowValue d)),
      (problem Gamma i).BestResponse x.1.1 (lowBroadcast x.2):=by
  dsimp only
  let ξ:=(1-η)/2
  have hξ:0<ξ:=by dsimp [ξ];linarith
  have hξh:ξ ≤ 1/2:=by dsimp [ξ];linarith
  letI:=L.compact_atomless
  let P:=populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) PA PH
  let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
  let G:ProbabilityMeasure (LowValue d):=L.joint.1.map measurable_snd.aemeasurable
  let row:UserProfile (N+1) 2→Fin N→RowRival:=fun profile j=>nativeRowRival Gamma d U (profile (i.succAbove j))
  have hrow:Measurable row:=measurable_pi_lambda _ (fun j=>
    (measurable_nativeRowRival Gamma d U).comp (measurable_pi_apply (i.succAbove j)))
  have hκ:((1+η)/2) ≤ 1:=by linarith
  have hac:∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<((1+η)/2)*x.2.bid ∧ d<x.2.bid ∧
      x.2.bid ≤ U ∧ x.2.routeCount=2:=by
    filter_upwards [hactive] with x hx
    exact ⟨hx.1,hx.1.trans_le (by nlinarith [mul_nonneg (sub_nonneg.mpr hκ) x.2.bid_nonneg]),hx.2⟩
  have hp:∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),lowActionGuard d U ((1+η)/2) x.2:=
    population_lowActionGuard hdU s a h mu L.joint PA PH hac hupper
  have hprofiles:=profile_lowActionGuard (N:=N) (c:=c) P hη0 hη1 hp
  have hphysical:(userLaw Gamma).map (nativeRowRival Gamma d U)=rivalLaw s a h (realLowBidLaw L.joint.1 : Measure ℝ):=
    native_population_row hdU s a h hs ha hh hsum mu L.joint PA PH
      (hac.mono (fun _ hx=>⟨hx.2.1,hx.2.2.1⟩)) (hupper.mono (fun _ hx=>hx.1)) η hη0 hη1
  have hlaw:(userProfileLaw Gamma).map row=
      Measure.pi (fun _ : Fin N=>rivalLaw s a h (realLowBidLaw L.joint.1 : Measure ℝ)):=
    deleted_rival_rows_law Gamma i (nativeRowRival Gamma d U)
      (measurable_nativeRowRival Gamma d U) _ hphysical
  have hdup:∀act : JointAction 2,act.routeCount=2 → act.bid ≤ d →
      ((problem Gamma i).outcome act).duplicates ≤
        (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c):=by
    intro act hk hbd
    have hbound:=native_duplicates_le_underflow_of_guard P hη0 hη1 hd hdU hprofiles i row hrow
      (fun _=>rfl) _ hlaw act hk hbd
    rw [rowBothUnderflow_probability s a h hs ha hh hsum
      (realLowBidLaw L.joint.1 : Measure ℝ) N c,
      categoryLaw_eq_low_law s a h hs ha hh hsum (realLowBidLaw L.joint.1 : Measure ℝ) Gref] at hbound
    exact hbound
  filter_upwards [L.all_bid_IC hξ hξh,L.value_positive,L.bid_positive] with x hIC hw hb
  apply NativeLowIncentives.best_response Gamma i hξ hξh hη0 hη1.le rfl rfl
    (categoryLaw s a h hs ha hh hsum Gref) G x.1 x.2 hw hb hIC
  · intro act hk hpos hbd
    exact population_positive_broadcast_payoff hd hdU s a h hs ha hh hsum Gref mu L.joint
      PA PH hη0 hη1 hactive hupper i x.1.1 act hk hpos hbd
  · intro act hk hz y hy hyd
    exact native_zero_envelope_of_guard P hη0 hη1 hdU hprofiles i x.1.1 x.1.property.1 act hk hz y hy hyd
  · exact hell
  · exact hsmall
  · intro act hk hbval
    exact hdup act hk (hbval.trans x.1.property.2)

lemma measurableEmbedding_lowJointPoint (d : ℝ) :
    MeasurableEmbedding (fun x : LowValue d×LowValue d=>(x.1.1,lowBroadcast x.2)):=by
  apply (measurable_fst.subtype_val.prodMk ((measurable_lowBroadcast d).comp measurable_snd)).measurableEmbedding
  intro x y hxy
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hxy)
  · exact Subtype.ext (congrArg (fun p : ℝ×JointAction 2=>p.2.bid) hxy)

theorem population_low_actual_best_response (hd:0 ≤ d) (hdU:d ≤ U)
    (s a h : ℝ) (hs:0 ≤ s) (ha:0 ≤ a) (hh:0 ≤ h) (hsum:s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hη0:0 ≤ η) (hη1:η<1)
    (L : ActualAtomlessLowLimit N d ((1-η)/2) c (categoryLaw s a h hs ha hh hsum Gref) mu)
    (PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hactive:∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<((1+η)/2)*x.2.bid ∧
      x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper:∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),U<x.2.bid ∧ x.2.routeCount=1)
    (hell:0<(CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0))
    (hsmall:(CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0)/4)
    (i : Fin (N+1)) :
    let P:=populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) PA PH
    let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
    ∀ᵐx ∂(lowJoint mu L.joint : Measure (ℝ×JointAction 2)),(problem Gamma i).BestResponse x.1 x.2:=by
  dsimp only
  change ∀ᵐx ∂(L.joint.1 : Measure (LowValue d×LowValue d)).map
    (fun x=>(x.1.1,lowBroadcast x.2)),_
  apply (measurableEmbedding_lowJointPoint d).ae_map_iff.mpr
  exact population_low_joint_best_response hd hdU s a h hs ha hh hsum Gref mu hη0 hη1 L
    PA PH hactive hupper hell hsmall i

end FCAppendix.Affine.Hybrid
