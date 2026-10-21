import FCAppendix.Affine.Hybrid.UpperLaw
import FCAppendix.Finite.RankConcentration

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Bayes Set
open Existence.RankEnvelope

theorem weighted_upper_bid_tail (FH : ProbabilityMeasure ℝ)
    (PH : ProbabilityMeasure (ℝ×JointAction 2)) (b : ℝ→ℝ)
    (hbid : (PH : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)=(FH : Measure ℝ).map b)
    (h : ℝ) (hh : 0 ≤ h) (y : ℝ) :
    ((ENNReal.ofReal h • (FH : Measure ℝ)).map b).real (Ioi y)=
      h*(PH : Measure (ℝ×JointAction 2)).real {x | y<x.2.bid} := by
  rw [Measure.map_smul,←hbid]
  change (ENNReal.ofReal h*(((PH : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)) (Ioi y))).toReal=_
  have hm : Measurable (fun x : ℝ×JointAction 2=>x.2.bid):=(measurable_bid 2).comp measurable_snd
  rw [Measure.map_apply hm measurableSet_Ioi,ENNReal.toReal_mul,ENNReal.toReal_ofReal hh]
  rfl

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
theorem upper_singleton_payoff_eq_bidRank (hcm : c ≤ m) (i : Fin m) (v : ℝ)
    (act : JointAction 2) (hk : act.routeCount=1) (hb : U<act.bid) :
    (problem Gamma i).payoff v act=(v-act.bid)*bidRank mu (m-1) c 2 b act.bid := by
  rw [population_upper_singleton_payoff m c U s a h hU hs ha hh hsum PL PA PH hL hA hH hnull η hη0 hη1 i v act hk hb]
  have ht:=weighted_upper_bid_tail FH PH b hbid h hh act.bid
  rw [bidRank,ht]
  have hp : h*(PH : Measure (ℝ×JointAction 2)).real {x | act.bid<x.2.bid}/2∈Icc (0:ℝ) 1:=by
    have hz : 0 ≤ (PH : Measure (ℝ×JointAction 2)).real {x | act.bid<x.2.bid}:=measureReal_nonneg
    have ho : (PH : Measure (ℝ×JointAction 2)).real {x | act.bid<x.2.bid} ≤ 1:=measureReal_le_one
    have hm:=mul_le_mul_of_nonneg_left ho hh
    constructor <;> nlinarith [mul_nonneg hh hz]
  simp only [Nat.cast_ofNat]
  rw [rankSuccess_eq_prob _ _ hp,binomBelow_eq_prob _ _ (by omega) _ hp.1 hp.2]

include hU hh1 hL hA hH hnull hbid in
theorem native_upper_one_route_bound (hm : 2 ≤ m) (hcm : c ≤ m)
    (q V : ℝ→ℝ) (t R E : ℝ) (hUR : U<R)
    (H : UpperEnvelopeProperties mu (m-2) c q b V t R E)
    (i : Fin m) (v : ℝ) (act : JointAction 2) (hk : act.routeCount=1) (hb : R ≤ act.bid) :
    (problem Gamma i).payoff v act ≤ V v := by
  rw [upper_singleton_payoff_eq_bidRank m c U s a h hU hs ha hh hh1 hsum PL PA PH FH
    hL hA hH hnull b hbid η hη0 hη1 hcm i v act hk (hUR.trans_le hb)]
  have he : m-2+1=m-1:=by omega
  have hh:=H.one_route v act.bid hb
  rw [he] at hh
  exact hh

end Native

end FCAppendix.Affine.Hybrid
