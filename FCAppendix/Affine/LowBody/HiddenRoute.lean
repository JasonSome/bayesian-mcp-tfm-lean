import FCAppendix.Finite.SingletonDeviation

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Game Bayes
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def addSecondRoute (a : JointAction 2) : JointAction 2 where
  bid:=a.bid
  bid_nonneg:=a.bid_nonneg
  routeCount:=2
  routeCount_le:=le_rfl

theorem native_affine_zero_fee_payoff (Γ : FiniteGame m 2 c Seed) {η : ℝ}
    (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hg : Γ.g=0) (i : Fin m) (v : ℝ) (a : JointAction 2) :
    (problem Γ i).payoff v a=(v-a.bid)*((problem Γ i).outcome a).success-
      η*a.bid*((problem Γ i).outcome a).duplicates := by
  change ((problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G=_
  rw [CountLaw.utility_eq,hA,hg,CountLaw.charge_affine]
  ring

theorem native_second_route_gain_identity (Γ : FiniteGame m 2 c Seed) {η : ℝ}
    (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hg : Γ.g=0) (i : Fin m) (v : ℝ) (a : JointAction 2) (hk : a.routeCount=1) :
    (problem Γ i).payoff v (addSecondRoute a)-(problem Γ i).payoff v a=
      (problem Γ i).payoff v a-
        (v-(1-η)*a.bid)*((problem Γ i).outcome (addSecondRoute a)).duplicates := by
  have hload:=load_eq_mean Γ (by norm_num : 0<2) i (addSecondRoute a)
  simp only [addSecondRoute,Nat.cast_ofNat] at hload
  rw [native_affine_zero_fee_payoff Γ hη0 hη1 hA hg,
    singleton_payoff Γ (by norm_num : 0<2) i a hk,hg]
  simp only [addSecondRoute,sub_zero]
  unfold CountLaw.duplicates
  rw [hload]
  ring

theorem native_second_route_gain_lower (Γ : FiniteGame m 2 c Seed) {η v ell δ : ℝ}
    (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hg : Γ.g=0) (i : Fin m) (a : JointAction 2) (hk : a.routeCount=1)
    (hbv : a.bid≤v) (hrent : v*ell/2≤(problem Γ i).payoff v a)
    (hdup : ((problem Γ i).outcome (addSecondRoute a)).duplicates≤δ) :
    v*(ell/2-δ)≤(problem Γ i).payoff v (addSecondRoute a)-(problem Γ i).payoff v a := by
  rw [native_second_route_gain_identity Γ hη0 hη1 hA hg i v a hk]
  have hcoeff : 0≤v-(1-η)*a.bid:=by nlinarith [a.bid_nonneg,mul_nonneg hη0 a.bid_nonneg]
  have hcost:=mul_le_mul_of_nonneg_left hdup hcoeff
  have hcoefficient : v-(1-η)*a.bid≤v:=by nlinarith [mul_nonneg (sub_nonneg.mpr hη1) a.bid_nonneg]
  have hδ : 0≤δ:=((problem Γ i).outcome (addSecondRoute a)).duplicates_nonneg.trans hdup
  have hcost' :=mul_le_mul_of_nonneg_right hcoefficient hδ
  nlinarith

theorem native_one_route_optimum_strictly_improved (Γ : FiniteGame m 2 c Seed)
    {η v ell δ : ℝ} (hη0 : 0≤η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hg : Γ.g=0)
    (i : Fin m) (hv : 0<v) (hell : 0<ell) (hsmall : δ<ell/2)
    (a ref : JointAction 2) (hk : a.routeCount=1) (hkr : ref.routeCount=1)
    (href : ref.bid=v/2) (hqref : ell ≤ meanAcceptProb Γ i ref.bid)
    (hopt : ∀a' : JointAction 2,a'.routeCount=1→
      (problem Γ i).payoff v a'≤(problem Γ i).payoff v a)
    (hdup : ((problem Γ i).outcome (addSecondRoute a)).duplicates≤δ) :
    (problem Γ i).payoff v a<(problem Γ i).payoff v (addSecondRoute a) := by
  have hrent : v*ell/2≤(problem Γ i).payoff v a := by
    have hh:=hopt ref hkr
    rw [singleton_payoff Γ (by norm_num : 0<2) i ref hkr,hg,href] at hh
    have hm:=mul_le_mul_of_nonneg_left hqref (show 0≤v/2 by positivity)
    rw [href] at hm
    nlinarith
  have hq : 0 ≤ meanAcceptProb Γ i a.bid := by
    unfold meanAcceptProb acceptProb
    positivity
  have hbv : a.bid≤v := by
    by_contra hn
    have hh : v-a.bid≤0:=by linarith
    have hpay : (problem Γ i).payoff v a≤0:=by
      rw [singleton_payoff Γ (by norm_num : 0<2) i a hk,hg,sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hh hq
    have hp:=mul_pos hv hell
    linarith
  have hgain:=native_second_route_gain_lower Γ hη0 hη1 hA hg i a hk hbv hrent hdup
  have hp:=mul_pos hv (sub_pos.mpr hsmall)
  linarith

theorem native_second_route_utility_lower (Γ : FiniteGame m 2 c Seed) {η v δ : ℝ}
    (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hg : Γ.g=0) (i : Fin m) (a : JointAction 2) (hk : a.routeCount=1)
    (hbv : a.bid≤v) (hdup : ((problem Γ i).outcome (addSecondRoute a)).duplicates≤δ) :
    2*(problem Γ i).payoff v a-v*δ≤(problem Γ i).payoff v (addSecondRoute a) := by
  have hidentity:=native_second_route_gain_identity Γ hη0 hη1 hA hg i v a hk
  have hcoeff : 0≤v-(1-η)*a.bid:=by nlinarith [a.bid_nonneg,mul_nonneg hη0 a.bid_nonneg]
  have hcost:=mul_le_mul_of_nonneg_left hdup hcoeff
  have hcoefficient : v-(1-η)*a.bid≤v:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr hη1) a.bid_nonneg]
  have hδ : 0≤δ:=((problem Γ i).outcome (addSecondRoute a)).duplicates_nonneg.trans hdup
  have hcost' :=mul_le_mul_of_nonneg_right hcoefficient hδ
  nlinarith

theorem native_broadcast_optimum_strictly_beats_one_route
    (Γ : FiniteGame m 2 c Seed) {η v ell δ : ℝ}
    (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hg : Γ.g=0) (i : Fin m) (hv : 0<v) (hell : 0<ell) (hδ : 0≤δ)
    (hsmall : δ≤ell/4) (star ref : JointAction 2) (href : ref.routeCount=2)
    (hcompare : v*(ell-δ)/2≤(problem Γ i).payoff v ref)
    (hopt : ∀a' : JointAction 2,a'.routeCount=2→
      (problem Γ i).payoff v a'≤(problem Γ i).payoff v star)
    (hdup : ∀a : JointAction 2,a.routeCount=1→a.bid≤v→
      ((problem Γ i).outcome (addSecondRoute a)).duplicates≤δ)
    (a : JointAction 2) (hk : a.routeCount=1) :
    (problem Γ i).payoff v a<(problem Γ i).payoff v star := by
  have hstar : v*(ell-δ)/2≤(problem Γ i).payoff v star:=hcompare.trans (hopt ref href)
  have hgap : v*δ<v*(ell-δ)/2 := by
    have hp : 0<v*(ell-3*δ):=mul_pos hv (by linarith)
    nlinarith
  by_cases hbv : a.bid≤v
  · by_cases hu : (problem Γ i).payoff v a≤v*δ
    · exact hu.trans_lt (hgap.trans_le hstar)
    · have hh:=native_second_route_utility_lower Γ hη0 hη1 hA hg i a hk hbv (hdup a hk hbv)
      have htwo:=(hopt (addSecondRoute a) rfl)
      linarith
  · have hq : 0 ≤ meanAcceptProb Γ i a.bid := by
      unfold meanAcceptProb acceptProb
      positivity
    have hpay : (problem Γ i).payoff v a≤0:=by
      rw [singleton_payoff Γ (by norm_num : 0<2) i a hk,hg,sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hq
    have hzero : 0≤v*δ:=mul_nonneg hv.le hδ
    exact hpay.trans_lt (hzero.trans_lt (hgap.trans_le hstar))

end FCAppendix.Affine.LowBody
