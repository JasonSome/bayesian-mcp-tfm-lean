import FCAppendix.Affine.Hybrid.NativeLowPopulation

set_option maxHeartbeats 2200000
noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes LowBody Classical
open NativeContinuation
open Existence.Distributional
variable {N c : ℕ} {d U η : ℝ}

lemma compact_bid_real_law (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowValue d) mu) :
    realLowLaw ((pi.1.map measurable_snd.aemeasurable : ProbabilityMeasure (LowValue d)) : Measure (LowValue d))=
      (realLowBidLaw pi.1 : Measure ℝ):=by
  change ((pi.1 : Measure (LowValue d×LowValue d)).map Prod.snd).map Subtype.val=_
  rw [Measure.map_map measurable_subtype_coe measurable_snd]
  rfl

theorem population_positive_broadcast_payoff (hd:0 ≤ d) (hdU:d ≤ U)
    (s a h : ℝ) (hs:0 ≤ s) (ha:0 ≤ a) (hh:0 ≤ h) (hsum:s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowValue d) mu)
    [NullSingletonClass ((pi.1.map measurable_snd.aemeasurable : ProbabilityMeasure (LowValue d)) : Measure (LowValue d))]
    (PA PH : ProbabilityMeasure (ℝ×JointAction 2)) (hη0:0 ≤ η) (hη1:η<1)
    (hactive:∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<((1+η)/2)*x.2.bid ∧
      x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper:∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),U<x.2.bid ∧ x.2.routeCount=1)
    (i : Fin (N+1)) (w : ℝ) (act : JointAction 2) (hk:act.routeCount=2)
    (hb:0<act.bid) (hbd:act.bid ≤ d) :
    let P:=populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
    let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
    (problem Gamma i).payoff w act=
      exactExpectedPayoff N d ((1-η)/2) c (categoryLaw s a h hs ha hh hsum Gref)
        (pi.1.map measurable_snd.aemeasurable) (w,act.bid):=by
  dsimp only
  let ξ:=(1-η)/2
  have hξ:0<ξ:=by dsimp [ξ];linarith
  have hξ1:ξ<1:=by dsimp [ξ];linarith
  let P:=populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
  let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
  let C:=contextPolicy (m:=N+1) ξ hξ hξ1 c
  let G:ProbabilityMeasure (LowValue d):=pi.1.map measurable_snd.aemeasurable
  let row:UserProfile (N+1) 2→Fin N→RowRival:=fun z j=>nativeRowRival Gamma d U (z (i.succAbove j))
  have hrow:Measurable row:=measurable_pi_lambda _ (fun j=>
    (measurable_nativeRowRival Gamma d U).comp (measurable_pi_apply (i.succAbove j)))
  have hac:∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<(1-ξ)*x.2.bid ∧ d<x.2.bid ∧
      x.2.bid ≤ U ∧ x.2.routeCount=2:=by
    filter_upwards [hactive] with x hx
    have hrec:d<(1-ξ)*x.2.bid:=by dsimp [ξ];nlinarith [hx.1]
    have hbigger:(1-ξ)*x.2.bid ≤ x.2.bid:=by
      nlinarith [mul_nonneg hξ.le x.2.bid_nonneg]
    exact ⟨hrec,hrec.trans_le hbigger,hx.2⟩
  have hp:∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),lowActionGuard d U (1-ξ) x.2:=
    population_lowActionGuard hdU s a h mu pi PA PH hac hupper
  have hprofiles:=profile_lowActionGuard (N:=N) (c:=c) P hη0 hη1 hp
  have hphysical:(userLaw Gamma).map (nativeRowRival Gamma d U)=rivalLaw s a h (realLowLaw (G : Measure (LowValue d))):=by
    rw [compact_bid_real_law mu pi]
    exact native_population_row hdU s a h hs ha hh hsum mu pi PA PH
      (hac.mono (fun _ hx=>⟨hx.2.1,hx.2.2.1⟩)) (hupper.mono (fun _ hx=>hx.1)) η hη0 hη1
  have hlaw:(userProfileLaw Gamma).map row=
      Measure.pi (fun _ : Fin N=>rivalLaw s a h (realLowLaw (G : Measure (LowValue d)))):=
    deleted_rival_rows_law Gamma i (nativeRowRival Gamma d U)
      (measurable_nativeRowRival Gamma d U) _ hphysical
  have hgeneric:∀ᵐz ∂userProfileLaw Gamma,rowCopyGeneric (1-ξ) act.bid (row z):=by
    apply (ae_map_iff hrow.aemeasurable (measurableSet_rowCopyGeneric (1-ξ) act.bid)).mp
    rw [hlaw]
    exact ae_iid_rowCopyGeneric (sub_pos.mpr hξ1) (ne_of_gt hb) s a h hs ha hh hsum (G : Measure (LowValue d))
  have hgame:C.nativeGame Gamma U=Gamma:=rfl
  have hidentity:∀ᵐprofile ∂userProfileLaw Gamma,
      (∫seed,nativeRealizedPayoff Gamma i w act ((profile,seed),Equiv.refl (Fin 2))
        ∂Measure.pi (fun _ : Fin 2=>Gamma.seedLaw))=literalRowPayoff ξ c w (act.bid,row profile):=by
    filter_upwards [hprofiles,hgeneric] with profile hp hgen
    let z:=Function.update profile i ((w,act),Equiv.refl (Fin 2))
    have hzguard:=inserted_low_guard hdU profile hp i w act hk hbd (Equiv.refl (Fin 2))
    have hz:z∈classifiedProfiles (N+1) U:=fun k=>(hzguard k).1
    have hzrow:collapsedDeletedRow d U z i=row profile:=by
      funext j
      simp only [collapsedDeletedRow,z,Function.update_of_ne (Fin.succAbove_ne i j)]
      rfl
    have havg:(∫seed,nativeRealizedPayoff Gamma i w act ((profile,seed),Equiv.refl (Fin 2))
        ∂Measure.pi (fun _ : Fin 2=>Gamma.seedLaw))=
        (∫seed,purePayoff (1-ξ) w (fun k=>entryBid ((actualContext U z).1 k))
          (select ξ hξ hξ1 c 0 (actualContext U z) (seed 0),
            select ξ hξ hξ1 c 1 (actualContext U z) (seed 1)) i
          ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval))):=by
      apply integral_congr_ae
      apply ae_of_all
      intro seed
      have hh:=native_broadcast_realized_context_payoff Gamma hη0 hη1 rfl rfl i w act
        (hbd.trans hdU) profile seed (Equiv.refl (Fin 2)) hz
      dsimp only at hh
      rw [hgame] at hh
      exact hh
    rw [havg]
    have hbid:(z i).1.2.bid=act.bid:=by simp only [z,Function.update_self]
    have hout:=native_focal_context_low_payoff ξ hξ hξ1 c hd hdU z hz i
      (by rw [hbid];exact hbd) (by rw [hbid];exact hb)
      (active_order_of_profile_guard z hzguard) w
    rw [hbid,hzrow] at hout
    exact hout hgen
  rw [broadcast_payoff_of_row_identity Gamma i w act hk hξ hξ1 row hrow _ hlaw hidentity]
  exact integral_literalRowPayoff_eq_exact hξ hξ1 s a h hs ha hh hsum Gref G w act.bid

end FCAppendix.Affine.Hybrid
