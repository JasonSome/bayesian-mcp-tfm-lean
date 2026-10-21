import FCAppendix.Affine.Hybrid.NativeLowPopulation
import FCAppendix.Affine.Hybrid.NativeZeroProfile
import FCAppendix.Affine.Hybrid.NativeAnyDuplicate

set_option maxHeartbeats 2200000
noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes LowBody Classical
open NativeContinuation
open scoped BigOperators
variable {N c : ℕ} {d U η : ℝ}

lemma integrable_native_seed_average {m : ℕ}
    (Gamma : FiniteGame m 2 c unitInterval) (i : Fin m) (w : ℝ) (act : JointAction 2) :
    Integrable (fun profile=>∫seed,nativeRealizedPayoff Gamma i w act ((profile,seed),Equiv.refl (Fin 2))
      ∂Measure.pi (fun _ : Fin 2=>Gamma.seedLaw)) (userProfileLaw Gamma):=by
  have hm:Measurable (fun omega : Background m 2 unitInterval=>
      focalCount Gamma i act (omega,Equiv.refl (Fin 2))):=
    (measurable_focalCount Gamma i act).comp (measurable_id.prodMk measurable_const)
  have hi:=CountLaw.integrable_comp (backgroundLaw Gamma)
    (fun omega : Background m 2 unitInterval=>focalCount Gamma i act (omega,Equiv.refl (Fin 2))) hm
    (fun r : Fin 3=>userPayoff w act.bid Gamma.g Gamma.A.charge Gamma.G.charge r.val)
  exact hi.integral_prod_left

lemma actual_native_seed_average (P : ProbabilityMeasure (ℝ×JointAction 2)) (hη0:0 ≤ η) (hη1:η<1)
    (i : Fin (N+1)) (w : ℝ) (act : JointAction 2) (hact:act.bid ≤ U)
    (profile : UserProfile (N+1) 2)
    (hz:Function.update profile i ((w,act),Equiv.refl (Fin 2))∈classifiedProfiles (N+1) U) :
    let ξ:=(1-η)/2
    let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
    (∫seed,nativeRealizedPayoff Gamma i w act ((profile,seed),Equiv.refl (Fin 2))
      ∂Measure.pi (fun _ : Fin 2=>Gamma.seedLaw))=
      seedAveragePayoff ξ (by dsimp only [ξ];linarith) (by dsimp only [ξ];linarith) c
        (actualContext U (Function.update profile i ((w,act),Equiv.refl (Fin 2)))) i w:=by
  dsimp only
  let ξ:=(1-η)/2
  have hξ:0<ξ:=by dsimp [ξ];linarith
  have hξ1:ξ<1:=by dsimp [ξ];linarith
  let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
  let C:=contextPolicy (m:=N+1) ξ hξ hξ1 c
  have he:C.nativeGame Gamma U=Gamma:=rfl
  apply integral_congr_ae
  apply ae_of_all
  intro seed
  have hh:=native_broadcast_realized_context_payoff Gamma hη0 hη1 rfl rfl i w act hact
    profile seed (Equiv.refl (Fin 2)) hz
  dsimp only at hh
  rw [he] at hh
  exact hh

theorem native_zero_envelope_of_guard (P : ProbabilityMeasure (ℝ×JointAction 2))
    (hη0:0 ≤ η) (hη1:η<1) (hdU:d ≤ U)
    (hprofiles:∀ᵐprofile ∂userProfileLaw (PopulationGame.game (N+1) c P η hη0 hη1 U),
      ∀k,lowActionGuard d U ((1+η)/2) (profile k).1.2)
    (i : Fin (N+1)) (w : ℝ) (hw:0 ≤ w) (act : JointAction 2) (hk:act.routeCount=2)
    (hzero:act.bid=0) (y : ℝ) (hy:0<y) (hyd:y ≤ d) :
    let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
    (problem Gamma i).payoff w act ≤
      (problem Gamma i).payoff w (NativeLowIncentives.broadcast y hy.le)+2*y:=by
  dsimp only
  let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
  let ay:=NativeLowIncentives.broadcast y hy.le
  let ξ:=(1-η)/2
  have hξ:0<ξ:=by dsimp [ξ];linarith
  have hξh:ξ ≤ 1/2:=by dsimp [ξ];linarith
  have hξ1:ξ<1:=by linarith
  have h0d:act.bid ≤ d:=by rw [hzero];exact hy.le.trans hyd
  rw [broadcast_payoff_eq_profile_seed_integral Gamma i w act hk,
    broadcast_payoff_eq_profile_seed_integral Gamma i w ay rfl]
  have hi0:=integrable_native_seed_average Gamma i w act
  have hiy:=integrable_native_seed_average Gamma i w ay
  have hadd:=integral_add hiy (integrable_const (2*y))
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hadd
  rw [←hadd]
  apply integral_mono_ae hi0 (hiy.add (integrable_const (2*y)))
  filter_upwards [hprofiles] with profile hp
  let z0:=Function.update profile i ((w,act),Equiv.refl (Fin 2))
  let zy:=Function.update profile i ((w,ay),Equiv.refl (Fin 2))
  have hz0guard:=inserted_low_guard hdU profile hp i w act hk h0d (Equiv.refl (Fin 2))
  have hzyguard:=inserted_low_guard hdU profile hp i w ay rfl hyd (Equiv.refl (Fin 2))
  have hz0:z0∈classifiedProfiles (N+1) U:=fun k=>(hz0guard k).1
  dsimp only [Pi.add_apply]
  have hzy:zy∈classifiedProfiles (N+1) U:=fun k=>(hzyguard k).1
  rw [actual_native_seed_average P hη0 hη1 i w act (h0d.trans hdU) profile hz0,
    actual_native_seed_average P hη0 hη1 i w ay (hyd.trans hdU) profile hzy]
  have hh:=actual_profile_zero_payoff_le_positive ξ hξ hξh c U z0 zy hz0 hzy i
    (by simpa only [z0,Function.update_self] using h0d.trans hdU)
    (by simpa only [zy,Function.update_self,ay,NativeLowIncentives.broadcast] using hyd.trans hdU)
    (fun k hk=>by simp only [z0,zy,Function.update_of_ne hk])
    (by simpa only [z0,Function.update_self] using hzero)
    (by simpa only [zy,Function.update_self,ay,NativeLowIncentives.broadcast] using hy) w hw
  dsimp only at hh
  simpa only [zy,Function.update_self,ay,NativeLowIncentives.broadcast] using hh

theorem native_duplicates_le_underflow_of_guard (P : ProbabilityMeasure (ℝ×JointAction 2))
    (hη0:0 ≤ η) (hη1:η<1) (hd:0 ≤ d) (hdU:d ≤ U)
    (hprofiles:∀ᵐprofile ∂userProfileLaw (PopulationGame.game (N+1) c P η hη0 hη1 U),
      ∀k,lowActionGuard d U ((1+η)/2) (profile k).1.2)
    (i : Fin (N+1)) (row : UserProfile (N+1) 2→Fin N→RowRival) (hrow:Measurable row)
    (hrowdef:∀profile,row profile=collapsedDeletedRow d U profile i)
    (nu : Measure (Fin N→RowRival))
    (hlaw:(userProfileLaw (PopulationGame.game (N+1) c P η hη0 hη1 U)).map row=nu)
    (act : JointAction 2) (hk:act.routeCount=2) (hbd:act.bid ≤ d) :
    let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
    ((problem Gamma i).outcome act).duplicates ≤ nu.real (rowBothUnderflow c):=by
  dsimp only
  let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
  let ξ:=(1-η)/2
  have hξ:0<ξ:=by dsimp [ξ];linarith
  have hξ1:ξ<1:=by dsimp [ξ];linarith
  let C:=contextPolicy (m:=N+1) ξ hξ hξ1 c
  have hgame:C.nativeGame Gamma U=Gamma:=rfl
  let E:Set (Sample (N+1) 2 unitInterval):={omega|row omega.1.1∈rowBothUnderflow c}
  have hE:MeasurableSet E:=(measurableSet_rowBothUnderflow c).preimage
    (hrow.comp measurable_fst.fst)
  have hpMP:MeasurePreserving (fun omega : Sample (N+1) 2 unitInterval=>omega.1.1)
      (sampleLaw Gamma) (userProfileLaw Gamma):=
    (measurePreserving_fst (μ:=userProfileLaw Gamma) (ν:=Measure.pi (fun _ : Fin 2=>Gamma.seedLaw))).comp
      (measurePreserving_fst (μ:=backgroundLaw Gamma) (ν:=permLaw 2))
  have hp:=hpMP.quasiMeasurePreserving.ae hprofiles
  rw [problem_outcome,CountLaw.duplicates_eq_expect,CountLaw.expect_ofMeasure]
  have hi:=CountLaw.integrable_comp (sampleLaw Gamma) (focalCount Gamma i act)
    (measurable_focalCount Gamma i act) (fun r : Fin 3=>(r.val:ℝ)-successIndicator r.val)
  have hbound:(∫omega,((focalCount Gamma i act omega).val:ℝ)-
      successIndicator (focalCount Gamma i act omega).val ∂sampleLaw Gamma) ≤
      ∫omega,E.indicator (fun _=>(1:ℝ)) omega ∂sampleLaw Gamma:=by
    apply integral_mono_ae hi ((integrable_const (1:ℝ)).indicator hE)
    filter_upwards [hp] with omega hprofile
    have hc (r : Fin 3):(r.val:ℝ)-successIndicator r.val=(if r.val=2 then (1:ℝ) else 0):=by
      fin_cases r <;> norm_num [successIndicator]
    rw [hc]
    by_cases hdup:(focalCount Gamma i act omega).val=2
    · let z:=Function.update omega.1.1 i ((0,act),omega.2)
      have hguard:=inserted_low_guard hdU omega.1.1 hprofile i 0 act hk hbd omega.2
      have hz:z∈classifiedProfiles (N+1) U:=fun k=>(hguard k).1
      have hcdup:inclusionCount (drawsRealization z) Gamma.policy omega.1.2 i=2:=by
        rw [←focalCount_eq_inserted_count Gamma i 0 act omega.1.1 omega.1.2 omega.2]
        exact hdup
      rw [←hgame] at hcdup
      have hact:∀k∈upperSet d (actualContext U z).1,d<(1-ξ)*entryBid ((actualContext U z).1 k):=by
        have hcoeff:1-ξ=(1+η)/2:=by dsimp [ξ];ring
        rw [hcoeff]
        exact active_order_of_profile_guard z hguard
      have hu:=native_focal_duplicate_implies_bothUnderflow ξ hξ hξ1 c Gamma hd hdU z hz i
        (by simpa only [z,Function.update_self] using hbd) hact omega.1.2 hcdup
      have hr:collapsedDeletedRow d U z i=row omega.1.1:=by
        rw [hrowdef]
        funext j
        simp only [collapsedDeletedRow,z,Function.update_of_ne (Fin.succAbove_ne i j)]
      have he:omega∈E:=by change BothUnderflow c (fun j=>(row omega.1.1 j).1);rwa [hr] at hu
      simp only [if_pos hdup,Set.indicator_of_mem he,le_refl]
    · rw [if_neg hdup]
      exact Set.indicator_nonneg (fun _ _=>zero_le_one) omega
  have hind:=integral_indicator_one (μ:=sampleLaw Gamma) hE
  have hone:(1 : Sample (N+1) 2 unitInterval→ℝ)=(fun _=>1):=rfl
  rw [hone] at hind
  rw [hind] at hbound
  have hmap:(sampleLaw Gamma).map (fun omega=>row omega.1.1)=nu:=by
    change (sampleLaw Gamma).map (row ∘ (fun omega : Sample (N+1) 2 unitInterval=>omega.1.1))=nu
    rw [←Measure.map_map hrow hpMP.measurable,hpMP.map_eq,hlaw]
  have hm:=Measure.map_apply (μ:=sampleLaw Gamma) (hrow.comp hpMP.measurable) (measurableSet_rowBothUnderflow c)
  have hmap' : (sampleLaw Gamma).map (row ∘ (fun omega : Sample (N+1) 2 unitInterval=>omega.1.1))=nu:=hmap
  rw [hmap'] at hm
  have heq:(sampleLaw Gamma).real E=nu.real (rowBothUnderflow c):=by
    exact congrArg ENNReal.toReal hm.symm
  exact hbound.trans_eq heq

end FCAppendix.Affine.Hybrid
