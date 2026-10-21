import FCAppendix.Affine.Tail04.OrderedZeroSourcePartialCount
import FCAppendix.Affine.Tail04.GlobalLowerRoutes

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourcePartialGlobal
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings
open MenuError SourceMenuPopulation SourceMomentRectangle SourceMenuError
open OrderedNativePartialDeviation SourcePartialPublicGuard
open OrderedZeroSourcePartialCount

variable (P : ValueParameters) (ξ u Up U width : ℝ) (N : ℕ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u) (huU : 1+u≤ U)
  (hRUp : Central.R ξ≤ Up) (hUp : Up<1) (hUB : U< Central.B ξ) (hw : 0< width)
local notation "cN" => iidCapacity (99/200) N
local notation "D" => SourceNoisyData.data P ξ u Up U width cN
  hξ hξh hu huU hRUp hUp hUB hw
variable (t : ℝ) (ht : P.M< t) (hdR : P.d0< (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).R) (H : ℝ) (hUH : (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ H≤ upperBid v)
  (hrare : (1-(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).ξ)*(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).U+(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).ξ*(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).R)
local notation "E" => regions D P hdR H hUH
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "Γ₀" => coreGame D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare

variable (hN : 0< N) (huB : 1+u< Central.B ξ)
  (hRp : Up≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : width≤ γ ξ) (hroom : ∀reg,8/(N:ℝ)≤ radius ξ (centerMoment P reg))
  (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 ξ (iidCapacity (99/200) N) cats P.originalLowLaw)
  (hL : πL=L.joint)

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in

theorem all_routes_success (i : Fin (N+1)) (b : Icc (D).R (D).Up) (k : Fin 3) :
    ((problem Γ i).outcome (RawRoutes.action b ((D).hR.le.trans b.2.1) k)).success≤
      1-P.theta+OrderedZeroSourcePartialCount.error P ξ N := by
  by_cases hk : k=0
  · subst k
    rw [(RawRoutes.zero_route_statistics Γ i b ((D).hR.le.trans b.2.1)).1]
    linarith [P.theta_small,OrderedZeroSourcePartialCount.error_nonnegative P ξ N]
  · rw [sourceGame_problem D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare]
    have he:=OrderedNativePartialDeviation.success_error K Γ₀ (fun _=> rfl) i b k hk
    have hb:=OrderedZeroSourcePartialCount.badMass_bound P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL i
    have hr:=OrderedZeroSourcePartialCount.regime_error P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN cats L hL i
    unfold OrderedZeroSourcePartialCount.error
    linarith [(abs_le.mp he).2,(abs_le.mp hr).2,
      Real.exp_pos (-(N:ℝ)*(lowMass P.theta)^2/2),
      Real.exp_pos (-(N:ℝ)*P.bulkWeight^2/2)]

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in

theorem singleton_payoff_error (i : Fin (N+1)) (v : ℝ) (b : Icc (D).R (D).Up) :
    |(problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 1)-
      (v-(b:ℝ))*(1-P.theta)|≤|v-(b:ℝ)| *OrderedZeroSourcePartialCount.error P ξ N := by
  have hmass:=OrderedZeroSourcePartialCount.original_count_mass_error P ξ u Up U width N
    hξ hξh hu huU hRUp hUp hUB hw t ht hdR H hUH πL π upperBid hupperBid hfloor hrare
    hN huB hRp hsmall hmSmall hwγ hroom cats L hL i b 0
  rw [(Counts.count_masses _).1] at hmass
  have hq : |((problem Γ i).outcome (RawRoutes.action b ((D).hR.le.trans b.2.1) 1)).success-
      (1-P.theta)|≤ OrderedZeroSourcePartialCount.error P ξ N := by
    have hc : (Counts.singletonLaw (1-P.theta)
        ⟨by linarith [P.theta_small],by linarith [P.theta_pos]⟩).mass 0=P.theta := by
      simp [Counts.singletonLaw,FiniteLaw.mixture,FiniteLaw.dirac]
    rw [hc] at hmass
    convert! hmass using 1
    rw [show (1-_)-P.theta=-(_-(1-P.theta)) by ring,abs_neg]
  rw [LowBody.native_affine_zero_fee_payoff Γ (D).heta0 (D).heta1 rfl rfl,
    (RawRoutes.singleton_statistics Γ i b ((D).hR.le.trans b.2.1)).2]
  simp only [mul_zero,sub_zero,RawRoutes.action]
  change |(v-(b:ℝ))*_-(v-(b:ℝ))*(1-P.theta)|≤_
  rw [←mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in

theorem all_routes_payoff_upper (i : Fin (N+1)) (v : ℝ) (hv : (D).Up≤ v)
    (b : Icc (D).R (D).Up) (k : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) k)≤
      (v-(D).R)*(1-P.theta)+v*OrderedZeroSourcePartialCount.error P ξ N := by
  have hs:=all_routes_success P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL i b k
  have hu0:=((problem Γ i).outcome (RawRoutes.action b ((D).hR.le.trans b.2.1) k)).utility_le_bid_net_success
    v b (Γ).g (Γ).A (Γ).G ((D).hR.le.trans b.2.1) (Γ).g_nonneg
  change (problem Γ i).payoff v _≤(v-0-(b:ℝ))*_ at hu0
  have hnet : 0≤ v-(b:ℝ) := by linarith [b.2.2]
  have hh:=mul_le_mul_of_nonneg_left hs hnet
  have hR := (D).hR
  have he:=OrderedZeroSourcePartialCount.error_nonnegative P ξ N
  have hθ0 : 0≤1-P.theta := by linarith [P.theta_small]
  have hcost:=mul_nonneg (sub_nonneg.mpr b.2.1) hθ0
  have hberr:=mul_nonneg ((D).hR.le.trans b.2.1) he
  linarith

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in

theorem bottom_payoff_lower (i : Fin (N+1)) (v : ℝ) (hv : (D).R≤ v) :
    (v-(D).R)*(1-P.theta)-v*OrderedZeroSourcePartialCount.error P ξ N≤
      (problem Γ i).payoff v (RawRoutes.action (D).R (D).hR.le 1) := by
  let b : Icc (D).R (D).Up:=⟨(D).R,le_rfl,(D).hRUp⟩
  have he:=singleton_payoff_error P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL i v b
  have habs : |v-(D).R|≤ v := by rw [abs_of_nonneg (sub_nonneg.mpr hv)];linarith [(D).hR]
  have herr:=mul_le_mul_of_nonneg_right habs (OrderedZeroSourcePartialCount.error_nonnegative P ξ N)
  linarith [(abs_le.mp he).1]

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in

theorem broadcast_penalty (i : Fin (N+1)) (v : ℝ) (b : Icc (D).R (D).Up) :
    (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 2)-
      (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 1)≤
        -(D).eta*(D).R*(1-P.theta)+(2*|v|+4)*OrderedZeroSourcePartialCount.error P ξ N := by
  rw [sourceGame_problem D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare]
  have he:=OrderedNativePartialDeviation.broadcast_minus_singleton_le K Γ₀ (fun _=> rfl)
    (D).eta (D).heta0 (D).heta1 rfl rfl i b v
  have hb:=OrderedZeroSourcePartialCount.badMass_bound P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL i
  have hr:=OrderedZeroSourcePartialCount.regime_error P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN cats L hL i
  have hb0 : 0≤(b:ℝ) := (D).hR.le.trans b.2.1
  have hb1 : (b:ℝ)≤1 := b.2.2.trans hUp.le
  have hηb : 0≤ (D).eta*(b:ℝ) := mul_nonneg (D).heta0 hb0
  have hηb1 : (D).eta*(b:ℝ)≤1 := by nlinarith [(D).heta0,(D).heta1]
  have hab : |v-(b:ℝ)|≤|v|+1 := (abs_sub v b).trans (by rw [abs_of_nonneg hb0];linarith)
  have hcoef : 0≤2*|v-(b:ℝ)|+(D).eta*(b:ℝ) := by positivity
  have hcoef' : 2*|v-(b:ℝ)|+(D).eta*(b:ℝ)≤2*|v|+3 := by linarith
  have hh:=mul_le_mul_of_nonneg_left (abs_le.mp hr).1 hηb
  have hbad:=mul_le_mul hcoef' hb (OrderedNativePartialDeviation.badMass_nonneg K Γ₀ i)
    (by positivity : 0≤2*|v|+3)
  have hρ:=mul_nonneg (mul_nonneg (D).heta0 (sub_nonneg.mpr b.2.1))
    (show 0≤1-P.theta by linarith [P.theta_small])
  let ε := Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)+Real.exp (-(N:ℝ)*P.bulkWeight^2/2)
  have hε : 0≤ε := by dsimp [ε]; positivity
  have hηε := mul_le_mul_of_nonneg_right hηb1 hε
  have hmain : -(D).eta*(b:ℝ)*serviceProb K Γ₀ i≤
      -(D).eta*(b:ℝ)*(1-P.theta)+ε := by
    change (D).eta*(b:ℝ)* -ε≤_ at hh
    nlinarith only [hh,hηε]
  have hB : 0≤badBound P ξ N := by
    linarith only [hb,OrderedNativePartialDeviation.badMass_nonneg K Γ₀ i]
  have hbuffer : (2*|v|+3)*(2*badBound P ξ N)+ε≤
      (2*|v|+4)*OrderedZeroSourcePartialCount.error P ξ N := by
    have herr : OrderedZeroSourcePartialCount.error P ξ N=2*(badBound P ξ N+ε) := by
      dsimp [OrderedZeroSourcePartialCount.error,ε]
      ring
    rw [herr]
    nlinarith only [hB,hε,mul_nonneg (by positivity : 0≤4*|v|+7) hε]
  have hcombined := he.trans (add_le_add hmain hbad)
  linarith only [hcombined,hbuffer,hρ]

end FCAppendix.Affine.Tail04.OrderedSourcePartialGlobal
