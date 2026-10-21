import FCAppendix.Affine.Tail04.CanonicalFailure
import FCAppendix.Affine.Tail04.OrderedZeroNativeCommonCount
import FCAppendix.Affine.Tail04.ZeroSourceMultiplierRectangle
import FCAppendix.Affine.Tail04.RawRouteCounts

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceNativeLowerFailure
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource
open MenuError SourceMenuPopulation SourceMenuIdentity SourceMomentRectangle
open CanonicalFailure

theorem route_success_le_broadcast {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (b : ℝ) (hb : 0≤ b) (k : Fin 3) :
    ((problem Γ i).outcome (RawRoutes.action b hb k)).success≤
      ((problem Γ i).outcome (RawRoutes.action b hb 2)).success := by
  fin_cases k
  · change ((problem Γ i).outcome (RawRoutes.action b hb (0:Fin 3))).success≤_
    rw [(RawRoutes.zero_route_statistics Γ i b hb).1]
    exact ((problem Γ i).outcome (RawRoutes.action b hb 2)).success_nonneg
  · change ((problem Γ i).outcome (RawRoutes.action b hb (1:Fin 3))).success≤_
    rw [(RawRoutes.singleton_statistics Γ i b hb).1]
    exact meanAcceptProb_le_success Γ (by norm_num) i
      (RawRoutes.action b hb 2) (by norm_num [RawRoutes.action])
  · exact le_rfl

lemma success_oscillation : MenuError.oscillation (fun r : Fin 3=>successIndicator r.val)=1 := by
  norm_num [MenuError.oscillation,successIndicator]

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw) (π : JointProfile D P t ht)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid) (hfloor : ∀v,t< v→ H≤ upperBid v)
  (N : ℕ)
local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "Ds" => installOriginal D P t ht
local notation "μ" => userLaw Γ
local notation "ρA" => bidMarginal (Subtype.val (active D P t ht π))
local notation "tag" => Observable.Regions.coarseTag E
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH
local notation "M" => OrderedZeroCommonMenuCount.mixedMean Ds tag decode μ
local notation "W" => OrderedZeroCommonMenuCount.reciprocalMean Ds tag decode μ
local notation "rate" => SourceMovingMenuRates.rate
  (SourceCommonMenuError.commonCoefficient P D.ξ) (lowMass P.theta) P.bulkWeight N

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)
  [hA : NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (Subtype.val (active D P t ht π))))]
  (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀reg,D.e0 reg=baseFlag P reg)
  (hθ : (D.regimeShare:ℝ)=P.theta) (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+D.u< Central.B D.ξ) (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta D.u (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)

include hcap hN hF hflags hθ hξh hR huB hRp hsmall hmSmall hwγ cats L hL hA in
theorem active_all_routes (kcap : ℝ) (hkcap : 0< kcap)
    (hU : D.U≤ Central.B D.ξ-kcap/t) (i : Fin (N+1))
    (b : Icc (1:ℝ) D.U) (k : Fin 3) :
    movingCoefficient P D.ξ kcap/t^2-rate≤
      1-((problem Γ i).outcome
        (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) k)).success := by
  have ht0 : 0< t := P.M_pos.trans ht
  have hlam (reg : Bool) :
      (1-D.ξ)*Central.B D.ξ+2*γ D.ξ≤SourceMenuError.meanNumerator P D.ξ (M reg) reg/W reg ∧
      SourceMenuError.meanNumerator P D.ξ (M reg) reg/W reg+2*γ D.ξ≤1 :=
    ZeroSourceMultiplierRectangle.actual_nominal_margins
    D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags huB
    hξh hR hRp hsmall hmSmall reg
  have hf (reg : Bool) : movingCoefficient P D.ξ kcap/t^2≤
      1-(idealRegime P D.ξ (M reg) (W reg) b reg).success :=
    active_regime_failure P D.hξ D.hξ1.le ht0 hkcap ⟨b.2.1,b.2.2.trans hU⟩ reg
      (hlam reg).1 (by linarith [(hlam reg).2,show 0≤ γ D.ξ by unfold γ;linarith [D.hξ]])
  have hi : movingCoefficient P D.ξ kcap/t^2≤
      1-(idealCount P D.ξ (M false) (W false) (M true) (W true) b).success := by
    change _≤1-(Counts.regimeLaw P.theta _ _ _).expect (fun r : Fin 3=>successIndicator r.val)
    rw [Counts.regimeLaw_expect]
    have hh:=add_le_add
      (mul_le_mul_of_nonneg_left (hf false) (by linarith [P.theta_small] : 0≤1-P.theta))
      (mul_le_mul_of_nonneg_left (hf true) P.theta_pos.le)
    dsimp only [CountLaw.success] at hh
    linarith
  have he:=OrderedZeroNativeCommonCount.original_count_error D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare cats L hL hcap hN hF hflags hθ hξh hR huB hRp hsmall
    hmSmall hwγ i b (fun r : Fin 3=>successIndicator r.val)
  rw [success_oscillation,one_mul] at he
  have hr:=route_success_le_broadcast Γ i b ((by norm_num : (0:ℝ)≤1).trans b.2.1) k
  have he' : |((problem Γ i).outcome
      (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)).success-
      (idealCount P D.ξ (M false) (W false) (M true) (W true) b).success|≤rate := he
  linarith only [hi,hr,(abs_le.mp he').2]

end FCAppendix.Affine.Tail04.OrderedSourceNativeLowerFailure
