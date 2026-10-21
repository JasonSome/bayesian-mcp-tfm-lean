import FCAppendix.Affine.Tail04.OrderedZeroNativeMenuPayoff
import FCAppendix.Affine.Tail04.SourceGlobalMargins

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeActiveSingleton
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource
open OrderedZeroCommonMenuCount ZeroSourceCommonMoments SourceMenuIdentity
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle
open SourceGlobalMargins RouteMenuStatistics

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)
  [hA : NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (Subtype.val (OrderedNativeZeroNoiseSource.active D P t ht π))))]
  (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀reg,D.e0 reg=baseFlag P reg)
  (hθ : (D.regimeShare:ℝ)=P.theta) (hη : D.eta=1-2*D.ξ)
  (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+D.u< Central.B D.ξ) (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta D.u (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hUH
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => userLaw Γ
local notation "tag" => Observable.Regions.coarseTag E
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH
local notation "M" => mixedMean Ds tag decode μ
local notation "W" => reciprocalMean Ds tag decode μ
local notation "lam" => ZeroSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
local notation "rateN" => SourceMovingMenuRates.rate
  (SourceCommonMenuError.commonCoefficient P D.ξ) (lowMass P.theta) P.bulkWeight N

include hA hcap hN hF hflags hθ hξh hR huB hRp hsmall hmSmall hwγ cats L hL in

theorem payoff_upper (i : Fin (N+1)) (v : ℝ) (hv : Central.B D.ξ≤ v) (b : Icc (1:ℝ) D.U) :
    (problem Γ i).payoff v (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 1)≤
      (3/5)*v+(v+2*Central.B D.ξ)*rateN := by
  let f:=statistic D.eta v b 1
  have hbB : (b:ℝ)∈Icc (1:ℝ) (Central.B D.ξ) :=
    ⟨b.2.1,b.2.2.trans (by simpa only [←hF] using (base_active_le_physical D).trans D.hUF)⟩
  have hB : 0≤ Central.B D.ξ := by unfold Central.B;linarith [D.hξ]
  have hv0 : 0≤ v := hB.trans hv
  have hbounds (reg : Bool):=ZeroSourceMultiplierRectangle.actual_nominal_bounds D P t ht
    πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags huB hξh hR hRp hsmall hmSmall reg
  have hq (reg : Bool) : exposure D.ξ (lam reg) b∈Icc (0:ℝ) 1 :=
    exposure_bounds D.hξ D.hξ1.le hbB (hbounds reg).1 (hbounds reg).2
  have hreg (reg : Bool) : idealRegime P D.ξ (M reg) (W reg) b reg=
      Counts.activeLaw (mixedProbability P D.ξ reg b) (exposure D.ξ (lam reg) b)
        (exposure D.ξ (lam reg) b) (mixedProbability_bounds P D.hξ hbB reg) (hq reg) (hq reg) :=
    idealRegime_eq_activeLaw P («M»:=M reg) («W»:=W reg) D.hξ hbB reg (hq reg)
  have hid : (idealCount P D.ξ (M false) (W false) (M true) (W true) b).expect f=
      (v-(b:ℝ))*((1-P.theta)*((1-mixedProbability P D.ξ false b)/2+
        mixedProbability P D.ξ false b*exposure D.ξ (lam false) b)+
        P.theta*((1-mixedProbability P D.ξ true b)/2+
          mixedProbability P D.ξ true b*exposure D.ξ (lam true) b)) := by
    rw [idealCount,Counts.regimeLaw_expect,
      hreg false,hreg true,Counts.activeLaw_expect,Counts.activeLaw_expect]
    norm_num [f,statistic]
    ring
  have hm:=active_singleton_marginal P D.hξ hbB (hq false).2 (hq true).2
  have hm' : (idealCount P D.ξ (M false) (W false) (M true) (W true) b).expect f≤(3/5)*v := by
    rw [hid]
    have hh:=mul_le_mul_of_nonneg_left hm (show 0≤ v-(b:ℝ) by linarith [hbB.2])
    linarith [b.2.1]
  have he:=OrderedZeroNativeCommonCount.original_count_error D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare cats L hL hcap hN hF hflags hθ hξh hR huB hRp hsmall hmSmall hwγ i b f
  have hf:=RouteMenuStatistics.native_payoff Γ D.eta D.heta0 D.heta1 rfl rfl
    i v b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 1
  rw [←hf] at he
  have ho:=oscillation_bound D.heta0 D.heta1 hv0
    (show (b:ℝ)∈Icc (0:ℝ) (Central.B D.ξ) from ⟨by linarith [hbB.1],hbB.2⟩) (1:Fin 3)
  have hr : 0≤rateN := SourceMovingMenuRates.rate_nonneg
    (SourceCommonMenuError.commonCoefficient_nonnegative P D.hξ) P.bulkWeight_pos.le N
  have hrate:=mul_le_mul_of_nonneg_right ho hr
  linarith [(abs_le.mp he).2]

end FCAppendix.Affine.Tail04.OrderedNativeActiveSingleton
