import FCAppendix.Affine.Tail04.OrderedZeroNativeCommonCount
import FCAppendix.Affine.Tail04.ZeroSourceMultiplierRectangle

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroNativeMenuPayoff
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource
open OrderedZeroCommonMenuCount ZeroSourceCommonMoments SourceMenuIdentity
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle

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
  [NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (Subtype.val (active D P t ht π))))]
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

include t ht hdR H hUH πL π upperBid hupperBid hfloor hrare cats L hL hcap hN hF hflags hθ hη hξh hR huB hRp hsmall hmSmall hwγ in
theorem original_payoff_error (i : Fin (N+1)) (v : ℝ) (hv : 0≤ v) (b : Icc (1:ℝ) D.U) :
    |(problem Γ i).payoff v (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)-
      menuUtility P D.ξ (lam false) (lam true) v b|≤(v+2*Central.B D.ξ)*rateN := by
  have he := OrderedZeroNativeCommonCount.original_count_error D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare cats L hL hcap hN hF hflags hθ hξh hR
    huB hRp hsmall hmSmall hwγ i b (affineStatistic D.eta v b)
  have hbounds (reg : Bool) := ZeroSourceMultiplierRectangle.actual_nominal_bounds D P t ht
    πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags huB
    hξh hR hRp hsmall hmSmall reg
  have hbB : (b:ℝ)∈Icc (1:ℝ) (Central.B D.ξ) :=
    ⟨b.2.1,b.2.2.trans (by simpa only [←hF] using (base_active_le_physical D).trans D.hUF)⟩
  have hq (reg : Bool) : exposure D.ξ (lam reg) b∈Icc (0:ℝ) 1 :=
    exposure_bounds D.hξ D.hξ1.le hbB (hbounds reg).1 (hbounds reg).2
  have hid : (idealCount P D.ξ (M false) (W false) (M true) (W true) b).expect
      (affineStatistic (1-2*D.ξ) v b)=menuUtility P D.ξ (lam false) (lam true) v b :=
    idealCount_payoff P v D.hξ hbB (hq false) (hq true)
  rw [hη] at he
  rw [hid] at he
  have hpay : ((problem Γ i).outcome
      (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)).expect
        (affineStatistic (1-2*D.ξ) v b)=
      (problem Γ i).payoff v (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2) := by
    rw [←hη,affineStatistic_utility _ _ _ _ D.heta0 D.heta1 (Schedule.once 2)]
    rfl
  rw [hpay] at he
  have hosc : MenuError.oscillation (affineStatistic (1-2*D.ξ) v b)≤ v+2*Central.B D.ξ := by
    rw [←hη]
    exact (oscillation_affineStatistic D.heta0 D.heta1 hv
      ((by norm_num : (0:ℝ)≤1).trans b.2.1)).trans (by linarith [hbB.1,hbB.2])
  exact he.trans (mul_le_mul_of_nonneg_right hosc
    (SourceMovingMenuRates.rate_nonneg (SourceCommonMenuError.commonCoefficient_nonnegative P D.hξ)
      P.bulkWeight_pos.le N))

end FCAppendix.Affine.Tail04.OrderedZeroNativeMenuPayoff
