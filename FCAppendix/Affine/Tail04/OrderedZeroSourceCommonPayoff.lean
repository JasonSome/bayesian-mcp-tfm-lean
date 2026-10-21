import FCAppendix.Affine.Tail04.OrderedZeroNativeMenuPayoff
import FCAppendix.Affine.Tail04.ZeroSourceMultiplierRectangle

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroSourceCommonPayoff
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings
open MenuError SourceMenuPopulation SourceMenuIdentity

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw) (π : JointProfile D P t ht)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid) (hfloor : ∀v,t< v→ H≤ upperBid v)
  (N : ℕ)
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "lam" => ZeroSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid
  hdR H hUH hfloor N hrare
local notation "rateN" => SourceMovingMenuRates.rate
  (SourceCommonMenuError.commonCoefficient P D.ξ) (lowMass P.theta) P.bulkWeight N

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)
  [NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (Subtype.val (OrderedNativeZeroNoiseSource.active D P t ht π))))]
  (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀reg,D.e0 reg=baseFlag P reg)
  (hθ : (D.regimeShare:ℝ)=P.theta) (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+D.u< Central.B D.ξ) (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : SourceMomentRectangle.relativeError P.zeta D.u (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ SourceMomentRectangle.γ D.ξ) (hη : D.eta=1-2*D.ξ)

include cats L hL hcap hN hF hflags hθ hξh hR huB hRp hsmall hmSmall hwγ hη in
theorem actual_error (i : Fin (N+1)) (v : ℝ) (hv : 0≤ v) (b : Icc (1:ℝ) D.U) :
    |(problem Γ i).payoff v (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)-
      menuUtility P D.ξ (lam false) (lam true) v b|≤(v+2*Central.B D.ξ)*rateN := by
  exact OrderedZeroNativeMenuPayoff.original_payoff_error D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare cats L hL hcap hN hF hflags hθ hη hξh hR
    huB hRp hsmall hmSmall hwγ i v hv b

end FCAppendix.Affine.Tail04.OrderedZeroSourceCommonPayoff
