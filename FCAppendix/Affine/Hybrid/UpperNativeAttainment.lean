import FCAppendix.Affine.Hybrid.UpperNativeEnvelope
import FCAppendix.Affine.Hybrid.UpperNativeRoutes

set_option maxHeartbeats 2000000
noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open Existence.RankEnvelope

section Native
variable (m c : ℕ) (U s a h : ℝ) (hU : 0 ≤ U)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2)) (FH : ProbabilityMeasure ℝ)
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),x.2.routeCount=1)
    (hnull : ∀y : ℝ,(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0)
    (b : ℝ→ℝ)
    (hbid : (PH : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)=(FH : Measure ℝ).map b)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1)
local notation "P"=>populationLaw s a h hs ha hh hsum PL PA PH
local notation "Gamma"=>PopulationGame.game m c P η hη0 hη1 U
local notation "mu"=>ENNReal.ofReal h • (FH : Measure ℝ)

include hU hh1 hL hA hH hnull hbid in
theorem native_upper_mean_eq_bidRank (hcm:c ≤ m) (i : Fin m) (y : ℝ) (hy:U<y) :
    meanAcceptProb Gamma i y=bidRank mu (m-1) c 2 b y:=by
  let act:JointAction 2:=⟨y,hU.trans hy.le,1,by norm_num⟩
  have hp:=upper_singleton_payoff_eq_bidRank m c U s a h hU hs ha hh hh1 hsum PL PA PH FH
    hL hA hH hnull b hbid η hη0 hη1 hcm i (y+1) act rfl hy
  rw [singleton_payoff Gamma (by norm_num : 0<2) i act rfl (y+1)] at hp
  change (y+1-0-y)*meanAcceptProb Gamma i y=(y+1-y)*bidRank mu (m-1) c 2 b y at hp
  simpa only [show y+1-0-y=(1:ℝ) by ring,show y+1-y=(1:ℝ) by ring,one_mul] using hp

local instance weightedUpperFinite : IsFiniteMeasure mu:=by
  constructor
  simp only [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
  exact ENNReal.ofReal_lt_top

local instance weightedUpperAtomless [NullSingletonClass (FH : Measure ℝ)] : NullSingletonClass mu:=
  ⟨fun y=>by simp only [Measure.smul_apply,smul_eq_mul,measure_singleton,mul_zero]⟩

include hh hh1 in
lemma weighted_upper_mass_le_one : (mu).real univ ≤ 1:=by
  simp only [Measure.real,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one,ENNReal.toReal_ofReal hh]
  exact hh1

variable [NullSingletonClass (FH : Measure ℝ)]

include hU hh1 hL hA hH hnull hbid in

theorem native_upper_constructed_attainment (hm:2 ≤ m) (hc:1 ≤ c) (hcm:c < m)
    (t R : ℝ) (hR:0<R) (hRt:R<t) (hUR:U<R)
    (hsupport:∀ᵐv ∂(FH : Measure ℝ),t ≤ v)
    (hb:b=bid (rank mu (m-1) c 2) t R) (i : Fin m) (v : ℝ) (hv:t ≤ v) :
    (problem Gamma i).payoff v (upperAction b v)=utility (rank mu (m-1) c 2) t R v:=by
  have hmEq:m-2+1=m-1:=by omega
  have hmass:(mu).real univ ≤ 1:=weighted_upper_mass_le_one h hh hh1 FH
  have hmu:∀ᵐx ∂mu,t ≤ x:=Measure.ae_smul_measure hsupport _
  have hqmono:Monotone (rank mu (m-1) c 2):=by
    have hh:=rank_monotone mu (r:=m-2) hc (by omega) (by norm_num : 2 ≤ (2:ℕ)) hmass
    rwa [hmEq] at hh
  have hqpos:∀x,0<rank mu (m-1) c 2 x:=fun x=>rank_pos mu _ _ hc (by norm_num) hmass x
  have hfloor:R ≤ b v:=by
    rw [hb]
    exact floor_le_bid hqmono hRt.le (hqpos t) hv
  have hpos:0 ≤ b v:=hR.le.trans hfloor
  have hactbid:(upperAction b v).bid=b v:=max_eq_left hpos
  have hp:=upper_singleton_payoff_eq_bidRank m c U s a h hU hs ha hh hh1 hsum PL PA PH FH
    hL hA hH hnull b hbid η hη0 hη1 (by omega) i v (upperAction b v) rfl
    (by rw [hactbid];exact hUR.trans_le hfloor)
  rw [hactbid,hb] at hp
  have hcont:Continuous (bid (rank mu (m-1) c 2) t R):=
    continuous_bid (continuous_rank mu _ _ _) (fun x=>(hqpos x).ne') t R
  letI:NullSingletonClass ((mu).map (bid (rank mu (m-1) c 2) t R)):=by
    have hh:=rank_atomless_bid mu (r:=m-2) hc (by omega) (by norm_num : 2 ≤ (2:ℕ)) hmass hRt hmu
    simpa only [hmEq] using hh
  rw [bidRank_at_report mu hcont.measurable hv (bid_monotoneOn hqmono hRt.le (hqpos t)) hmu] at hp
  rw [hb]
  rw [hp,report_payoff t R v v (hqpos v).ne']
  simp only [sub_self,zero_mul,add_zero]

include hU hh1 hL hA hH hnull hbid in

theorem native_upper_mean_floor_lower (hm:2 ≤ m) (hc:1 ≤ c) (hcm:c < m)
    (t R : ℝ) (hRt:R<t) (hUR:U<R)
    (hsupport:∀ᵐv ∂(FH : Measure ℝ),t ≤ v)
    (hb:b=bid (rank mu (m-1) c 2) t R) (i : Fin m) (y : ℝ) (hy:R ≤ y) :
    rank mu (m-1) c 2 t ≤ meanAcceptProb Gamma i y:=by
  have hmEq:m-2+1=m-1:=by omega
  have hmass:(mu).real univ ≤ 1:=weighted_upper_mass_le_one h hh hh1 FH
  have hmu:∀ᵐx ∂mu,t ≤ x:=Measure.ae_smul_measure hsupport _
  rw [native_upper_mean_eq_bidRank m c U s a h hU hs ha hh hh1 hsum PL PA PH FH
    hL hA hH hnull b hbid η hη0 hη1 (by omega) i y (hUR.trans_le hy),hb]
  have hh:=bidRank_floor_lower mu (r:=m-2) hc (by omega) (by norm_num : 2 ≤ (2:ℕ)) hmass hRt hmu hy
  simpa only [hmEq] using hh

include hU hh1 hL hA hH hnull hbid in

theorem native_upper_hidden_constructed_excluded (hm:2 ≤ m) (hc:1 ≤ c) (hcm:c < m)
    (t R H : ℝ) (hR:0<R) (hRt:R<t) (hUR:U<R)
    (hsupport:∀ᵐv ∂(FH : Measure ℝ),v∈Icc t H)
    (hb:b=bid (rank mu (m-1) c 2) t R)
    (hguard:error (rank mu (m-1) c 2) t R <
      η*R*(1-2*(1-rank mu (m-1) c 2 t)))
    (i : Fin m) (v : ℝ) (hv:t ≤ v) (act : JointAction 2) (hk:act.routeCount=2) (hact:R ≤ act.bid) :
    (problem Gamma i).payoff v act<utility (rank mu (m-1) c 2) t R v:=by
  have hmEq:m-2+1=m-1:=by omega
  have hmass:(mu).real univ ≤ 1:=weighted_upper_mass_le_one h hh hh1 FH
  have hqmono:Monotone (rank mu (m-1) c 2):=by
    have hh:=rank_monotone mu (r:=m-2) hc (by omega) (by norm_num : 2 ≤ (2:ℕ)) hmass
    rwa [hmEq] at hh
  have hq1:∀x,rank mu (m-1) c 2 x ≤ 1:=fun x=>(rank_bounds mu _ _ (by norm_num) hmass x).2
  have hqt:0<rank mu (m-1) c 2 t:=rank_pos mu _ _ hc (by norm_num) hmass t
  have hsupportMu:∀ᵐx ∂mu,x ≤ H:=Measure.ae_smul_measure (hsupport.mono (fun _ hx=>hx.2)) _
  have hint:=rank_deficit_integrable_of_bounded mu (m-1) c 2 hc t hsupportMu
  have hmean:=native_upper_mean_floor_lower m c U s a h hU hs ha hh hh1 hsum PL PA PH FH
    hL hA hH hnull b hbid η hη0 hη1 hm hc hcm t R hRt hUR
    (hsupport.mono (fun _ hx=>hx.1)) hb i act.bid hact
  exact native_hidden_upper_excluded Gamma hη0 hη1.le rfl rfl hqmono hq1 hR hRt hqt hint
    hguard hv i act hk hact (by linarith)

end Native
end FCAppendix.Affine.Hybrid
