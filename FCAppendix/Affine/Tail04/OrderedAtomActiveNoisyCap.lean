import FCAppendix.Affine.Tail04.OrderedAtomMultiplierRectangle

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomActiveNoisyCap
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeNoisySource
open SourceMenuPopulation SourceMenuError SourceMomentRectangle SourceMenuIdentity
open OrderedSourceCommonMenuError SourceBulkAnalyticAdapter SourceTailTaylor SourceTailCapGap

private lemma finite_gap_contradiction {a0 a1 m0 m1 err gap : ℝ}
    (h0 : -err ≤ a0 - m0) (h1 : a1 - m1 ≤ err) (hi : a0 ≤ a1)
    (hg : gap ≤ m0 - m1) (he : 2 * err < gap) : False := by
  linarith only [h0,h1,hi,hg,he]

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (hcap : D.c=MenuError.iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀ reg,D.e0 reg=baseFlag P reg)
  (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+bulkPhysicalWidth D< Central.B D.ξ)
  (hRp : D.V≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)
  (hθ : (D.regimeShare:ℝ)=P.theta) (hη : D.eta=1-2*D.ξ)

local notation "Ds" => installOriginal D P t ht
local notation "lam" => OrderedSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hBH
local notation "rN" => SourceMovingMenuRates.rate (commonCoefficient P D.ξ)
  (lowMass P.theta) P.bulkWeight N
local notation "err" => (t+2*Central.B D.ξ)*rN

include hfloor hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη in
theorem uniform_error (v : ℝ) (hv : 0≤ v) (hvt : v≤ t) (b : Icc (1:ℝ) D.U) :
    |OrderedFiniteTailNoisyGame.activeExpected Ds N (bidLaws D P t ht π,(v,b))-
      ∫ z : unitInterval,menuUtility P D.ξ (lam false) (lam true) v
        ((b:ℝ)*(1+D.eps*(z:ℝ)))|≤ err := by
  have hh := OrderedAtomCommonPayoff.activeExpected_error D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη v hv b
  have hr := SourceMovingMenuRates.rate_nonneg (s:=lowMass P.theta) (commonCoefficient_nonnegative P D.hξ) P.bulkWeight_pos.le N
  have hB : D.B≤ Central.B D.ξ := by simpa only [←hF,Data.B] using D.hUF
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hr)

include hfloor hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη in
theorem bulk_upper_strip {κ : ℝ} (hκ : 0≤ κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P D.ξ κ Λ) (hlam : (lam false,lam true)∈Λ)
    (herror : 2*err< κ*D.u/2)
    (hC1 : AllActionOptimal (π 0) (fun x=> SourceOrderedNoisyFixedPoint.payoff D P t ht N 0 (π,x))) :
    ∀ᵐ x ∂(ProbabilityMeasure.toMeasure (π 0).1),(x.2:ℝ)<1+D.u/2 := by
  filter_upwards [hC1] with x hx
  by_contra hn
  let a := SourceBulkAnalyticAdapter.bottom D
  have hv0 : 0≤(x.1:ℝ) := by
    have hg := P.partial_active_gap
    have hw := P.w_pos
    have hxv := x.1.2.1
    change P.vA-P.w≤(x.1:ℝ) at hxv
    linarith
  have hvt : (x.1:ℝ)≤ t := x.1.2.2.trans (P.active_tail_gap.le.trans ht.le)
  have he0 := uniform_error D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη x.1 hv0 hvt (extendBid D.huU a)
  have he1 := uniform_error D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη x.1 hv0 hvt (extendBid D.huU x.2)
  have hg := averaged_noisy_top_half_gap D P hF hκ hder (lam false,lam true) hlam x.1 x.2 (le_of_not_gt hn)
  have hi := hx a
  change OrderedFiniteTailNoisyGame.activeExpected Ds N (bidLaws D P t ht π,((x.1:ℝ),extendBid D.huU a))≤
    OrderedFiniteTailNoisyGame.activeExpected Ds N (bidLaws D P t ht π,((x.1:ℝ),extendBid D.huU x.2)) at hi
  simp only [a,SourceBulkAnalyticAdapter.bottom,extendBid,Subtype.coe_mk,one_mul] at he0
  simp only [extendBid,Subtype.coe_mk] at he1
  have h0 := (abs_le.mp he0).1
  have h1 := (abs_le.mp he1).2
  dsimp only [Prod.fst,Prod.snd] at hg
  dsimp only [a,SourceBulkAnalyticAdapter.bottom,extendBid] at hi
  exact finite_gap_contradiction h0 h1 hi hg herror

include hfloor hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη in
theorem tail_upper_strip {Amin Amax k : ℝ}
    (hmin : 0< Amin)
    (hA : Amin≤ leadingA P D.ξ (lam false) (lam true))
    (hmax : leadingA P D.ξ (lam false) (lam true)≤ Amax)
    (hk : k<1/(2*Amax))
    (hU : D.U=Central.B D.ξ-k/t)
    (hleft : endpointRadius Amin/t≤ Central.B D.ξ-1)
    (hbudget : 2*taylorConstant D.ξ (endpointRadius Amin)/t^2≤
      Amin*(stripWidth Amax k)^2/(4*t))
    (hnoise : D.eps*D.U≤ stripWidth Amax k/(4*t))
    (herror : 2*err< Amin*(stripWidth Amax k)^2/(2*t))
    (hC1 : AllActionOptimal (π 1) (fun x=> SourceOrderedNoisyFixedPoint.payoff D P t ht N 1 (π,x))) :
    ∀ᵐ x ∂(ProbabilityMeasure.toMeasure (π 1).1),(x.2:ℝ)< inwardCut (Central.B D.ξ) Amax k t := by
  have ht0 : 0< t := P.M_pos.trans ht
  have hlamA := OrderedAtomMultiplierRectangle.actual_nominal_bounds D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare hF hflags huB hξh hR hRp hsmall hmSmall false
  have hlamR := OrderedAtomMultiplierRectangle.actual_nominal_bounds D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare hF hflags huB hξh hR hRp hsmall hmSmall true
  let a := SourceTailNoisyGap.inwardBid D P t Amin Amax k (lam false) (lam true)
    hmin hA hmax hk ht0 hU hleft
  filter_upwards [hC1] with x hx
  by_contra hn
  have hv0 : 0≤(x.1:ℝ) := P.M_pos.le.trans x.1.2.1
  have he0 := uniform_error D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη x.1 hv0 x.1.2.2 a
  have he1 := uniform_error D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη x.1 hv0 x.1.2.2 x.2
  have hg := SourceTailNoisyGap.averaged_gap D P t Amin Amax k (lam false) (lam true)
    hξh.le hmin hA hmax hk ht0 hF hU hleft hlamA.1 hlamA.2 hlamR.1 hlamR.2
    hbudget hnoise x.1 x.1.2.2 x.2 (le_of_not_gt hn)
  have hi := hx a
  change OrderedFiniteTailNoisyGame.activeExpected Ds N (bidLaws D P t ht π,((x.1:ℝ),a))≤
    OrderedFiniteTailNoisyGame.activeExpected Ds N (bidLaws D P t ht π,((x.1:ℝ),x.2)) at hi
  have h0 := (abs_le.mp he0).1
  have h1 := (abs_le.mp he1).2
  change _≤(∫ z : unitInterval,menuUtility P D.ξ (lam false) (lam true) x.1
    ((a:ℝ)*(1+D.eps*(z:ℝ))))-_ at hg
  linarith

end FCAppendix.Affine.Tail04.OrderedAtomActiveNoisyCap
