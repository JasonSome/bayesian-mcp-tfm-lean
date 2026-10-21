import FCAppendix.Affine.Tail04.OrderedZeroActiveSourcePayoff
import FCAppendix.Affine.Tail04.OrderedZeroSourceCommonMenuError

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroNativeCommonCount
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings
open OrderedZeroActiveFiberLaw NativeActiveFiberCoordinates NativeFiberEnumerations PartialNativeCoordinates
open OrderedZeroCommonMenuCount MenuError SourceMenuPopulation SourceMenuIdentity
open scoped BigOperators

private lemma weighted_error {a b c d θ E : ℝ} (hθ0 : 0≤θ) (hθ1 : θ≤1)
    (h0 : |a-c|≤E) (h1 : |b-d|≤E) :
    |(1-θ)*a+θ*b-((1-θ)*c+θ*d)|≤E := by
  calc
    _=|(1-θ)*(a-c)+θ*(b-d)| := congrArg abs (by ring)
    _≤|(1-θ)*(a-c)|+|θ*(b-d)| := abs_add_le _ _
    _=(1-θ)*|a-c|+θ*|b-d| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hθ1),abs_of_nonneg hθ0]
    _≤(1-θ)*E+θ*E := add_le_add
      (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hθ1)) (mul_le_mul_of_nonneg_left h1 hθ0)
    _=E := by ring

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw) (π : JointProfile D P t ht)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid) (hfloor : ∀v,t< v→ H≤ upperBid v)
  (N : ℕ)
local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

private lemma castFiberRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((((n+1:ℕ):ℝ))*p)≤q) : x+y*((n+1:ℝ)*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "Ds" => installOriginal D P t ht
local notation "μ" => userLaw Γ
def commonLaw : ProbabilityMeasure (Icc (1:ℝ) D.U) :=
  bidMarginal (Subtype.val (active D P t ht π))
local notation "ρA" => commonLaw D P t ht π
local notation "μP" => bidMarginal (Subtype.val (π 2))
local notation "tag" => Observable.Regions.coarseTag E
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH
local notation "M" => OrderedZeroCommonMenuCount.mixedMean Ds tag decode μ
local notation "W" => OrderedZeroCommonMenuCount.reciprocalMean Ds tag decode μ

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)
  [hA : NullSingletonClass (bidMarginal (Subtype.val (OrderedNativeZeroNoiseSource.active D P t ht π)) : Measure (Icc (1:ℝ) D.U))]

include cats L hL in
lemma fiber_expect (i : Fin (N+1)) (kind : Fin N→ Fin 4) (b : Icc (1:ℝ) D.U) (f : Fin 3→ℝ) :
    (OrderedZeroNativeCategories.fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castFiberRare hrare)
      kind i (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)).expect f=
      (1-(Q).θ)*(∫row : Fin (commonSize i kind)→ Icc (1:ℝ) D.U,
        (AllCountActiveFiniteGain.physicalCount (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind))
          D.c D.ξ D.U D.R D.Up D.width (D.e0 false) D.F false (decide (0< (Ds).count kind 0))
          ((Ds).marksLaw (min (zeroSize i kind) (oneSize i kind))) ((Ds).marksLaw (max (zeroSize i kind) (oneSize i kind)))
          (ZeroNoiseFiniteGame.privateBayes Ds (min (zeroSize i kind) (oneSize i kind)) μP).val (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0).expect f
        ∂Measure.pi (fun _ : Fin (commonSize i kind)=>ProbabilityMeasure.toMeasure ρA))+
      (Q).θ*(∫row : Fin (commonSize i kind)→ Icc (1:ℝ) D.U,
        (AllCountActiveFiniteGain.physicalCount (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind))
          D.c D.ξ D.U D.R D.Up D.width (D.e0 true) D.F true (decide (0< (Ds).count kind 0))
          ((Ds).marksLaw (min (zeroSize i kind) (oneSize i kind))) ((Ds).marksLaw (max (zeroSize i kind) (oneSize i kind)))
          (ZeroNoiseFiniteGame.privateBayes Ds (min (zeroSize i kind) (oneSize i kind)) μP).val (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0).expect f
        ∂Measure.pi (fun _ : Fin (commonSize i kind)=>ProbabilityMeasure.toMeasure ρA)) := by
  rw [OrderedZeroActiveSourcePayoff.fiberCount_numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castFiberRare hrare) cats L hL i kind b,
    numericalCount_expect D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castFiberRare hrare) i kind b]
  let H0 := (K).finiteCount (rivalSet i kind 2)
  let H1 := (K).finiteCount (rivalSet i kind 3)
  have he (reg : Bool) :
      ∀ᵐ row ∂Measure.pi (fun _ : Fin (commonSize i kind)=>ProbabilityMeasure.toMeasure ρA),
      OrderedNativePayoffExperiment.perRegime K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0 reg (decide (0< (Ds).count kind 0))=
        AllCountActiveFiniteGain.physicalCount (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind))
          D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F reg (decide (0< (Ds).count kind 0))
          ((Ds).marksLaw (min (zeroSize i kind) (oneSize i kind))) ((Ds).marksLaw (max (zeroSize i kind) (oneSize i kind)))
          (ZeroNoiseFiniteGame.privateBayes Ds (min (zeroSize i kind) (oneSize i kind)) μP).val (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0 := by
    filter_upwards [OrderedZeroActiveFiberLaw.common_distinct D P t ht hdR H hUH π N i kind b]
      with row hrow
    by_cases h : zeroSize i kind≤oneSize i kind
    · have hfin : H0.val≤H1.val := h
      rw [OrderedNativePayoffExperiment.perRegime,if_pos hfin,
        NativeHighExperiment.perRegime_physical K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0
          (base_receipt_gap D) (fun j k hjk hj=> hjk (hrow hj)),
        localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H0,
        localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H1,
        localData_signalProbability D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H0,
        min_eq_left h,max_eq_right h]
      rfl
    · have hfin : ¬H0.val≤H1.val := h
      have hr : oneSize i kind≤zeroSize i kind := Nat.le_of_lt (Nat.lt_of_not_ge h)
      rw [OrderedNativePayoffExperiment.perRegime,if_neg hfin,
        NativeHighExperiment.perRegime_physical K H1 H0 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0
          (base_receipt_gap D) (fun j k hjk hj=> hjk (hrow hj)),
        localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H1,
        localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H0,
        localData_signalProbability D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H1,
        min_eq_right hr,max_eq_left hr]
      rfl
  have hi (reg : Bool) : Integrable (fun row : Fin (commonSize i kind)→ Icc (1:ℝ) D.U=>
      (AllCountActiveFiniteGain.physicalCount (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind))
        D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F reg (decide (0< (Ds).count kind 0))
        ((Ds).marksLaw (min (zeroSize i kind) (oneSize i kind))) ((Ds).marksLaw (max (zeroSize i kind) (oneSize i kind)))
        (ZeroNoiseFiniteGame.privateBayes Ds (min (zeroSize i kind) (oneSize i kind)) μP).val (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0).expect f)
      (Measure.pi (fun _ : Fin (commonSize i kind)=>ProbabilityMeasure.toMeasure ρA)) := by
    have hm : Measurable (fun row : Fin (commonSize i kind)→ Icc (1:ℝ) D.U=>
      (AllCountActiveFiniteGain.physicalCount (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind))
        D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F reg (decide (0< (Ds).count kind 0))
        ((Ds).marksLaw (min (zeroSize i kind) (oneSize i kind))) ((Ds).marksLaw (max (zeroSize i kind) (oneSize i kind)))
        (ZeroNoiseFiniteGame.privateBayes Ds (min (zeroSize i kind) (oneSize i kind)) μP).val (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0).expect f) := physical_expect_measurable Ds μP _ _ _ reg _ b f
    apply Integrable.of_bound hm.aestronglyMeasurable
      (∑r,‖f r‖)
    exact ae_of_all _ fun row=> FiniteLaw.norm_expect_le_sum_norm _ f
  rw [←integral_const_mul,←integral_const_mul,←integral_add ((hi false).const_mul _) ((hi true).const_mul _)]
  apply integral_congr_ae
  filter_upwards [he false,he true] with row h0 h1
  rw [IndependentCounts.expect_bernoulli]
  exact congrArg₂ (fun x y : CountLaw 2 => (1-(Q).θ)*x.expect f+(Q).θ*y.expect f) h0 h1

include t ht πL π upperBid hupperBid hfloor hrare cats L hL in
theorem original_outcome_expect (i : Fin (N+1)) (b : Icc (1:ℝ) D.U) (f : Fin 3→ℝ) :
    ((problem Γ i).outcome (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)).expect f=
      (1-(D.regimeShare:ℝ))*(averageCount Ds tag (E).measurable_coarseTag decode
        (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH) μP N μ false b).expect f+
      (D.regimeShare:ℝ)*(averageCount Ds tag (E).measurable_coarseTag decode
        (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH) μP N μ true b).expect f := by
  have hmass := OrderedZeroNativeCategories.native_source_category_ne_zero D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor Γ
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
  have hcat := OrderedZeroNativeCategories.native_source_category_mass D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor Γ
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
  have hρ := ZeroNativeFiberProduct.common_projection_law D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castFiberRare hrare)
  rw [OrderedZeroNativeCategories.native_count_statistic_mixture D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castFiberRare hrare) i]
  simp_rw [original_count_integral Ds μ tag (E).measurable_coarseTag decode
    (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH) hmass ρA hρ μP hcat]
  rw [FiniteLaw.expect]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro kind _
  rw [fiber_expect D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare cats L hL i kind b f]
  let F : ℕ→ℕ→ℕ→Bool→ℝ := fun A H0 H1 reg =>
    ∫ row : Fin A→Icc (1:ℝ) D.U,
      (AllCountActiveFiniteGain.physicalCount (min H0 H1) (max H0 H1)
        D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F reg (decide (0<(Ds).count kind 0))
        ((Ds).marksLaw (min H0 H1)) ((Ds).marksLaw (max H0 H1))
        (ZeroNoiseFiniteGame.privateBayes Ds (min H0 H1) μP).val
        (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0).expect f
      ∂Measure.pi (fun _ : Fin A=>ProbabilityMeasure.toMeasure ρA)
  have hF (reg : Bool) : F (commonSize i kind) (zeroSize i kind) (oneSize i kind) reg=
      F ((Ds).count kind 1) ((Ds).count kind 2) ((Ds).count kind 3) reg := by
    rw [show commonSize i kind=(Ds).count kind 1 from
      (OrderedZeroActiveSourcePayoff.count_rivalSet D P t ht N i kind 1).symm,
      show zeroSize i kind=(Ds).count kind 2 from
      (OrderedZeroActiveSourcePayoff.count_rivalSet D P t ht N i kind 2).symm,
      show oneSize i kind=(Ds).count kind 3 from
      (OrderedZeroActiveSourcePayoff.count_rivalSet D P t ht N i kind 3).symm]
  let C:=CommonList.iid (originalCategories P t ht) N
  change (C.mass kind)*((1-(D.regimeShare:ℝ))*F (commonSize i kind) (zeroSize i kind) (oneSize i kind) false+
      (D.regimeShare:ℝ)*F (commonSize i kind) (zeroSize i kind) (oneSize i kind) true)=
    (1-(D.regimeShare:ℝ))*((C.mass kind)*F ((Ds).count kind 1) ((Ds).count kind 2) ((Ds).count kind 3) false)+
      (D.regimeShare:ℝ)*((C.mass kind)*F ((Ds).count kind 1) ((Ds).count kind 2) ((Ds).count kind 3) true)
  rw [hF false,hF true]
  ring

variable (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀reg,D.e0 reg=baseFlag P reg)
  (hθ : (D.regimeShare:ℝ)=P.theta) (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+D.u< Central.B D.ξ) (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : SourceMomentRectangle.relativeError P.zeta D.u (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ SourceMomentRectangle.γ D.ξ)

include t ht hdR H hUH πL π upperBid hupperBid hfloor hrare cats L hL hcap hN hF hflags hθ hξh hR huB hRp hsmall hmSmall hwγ in
theorem original_count_error (i : Fin (N+1)) (b : Icc (1:ℝ) D.U) (f : Fin 3→ℝ) :
    |((problem Γ i).outcome (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)).expect f-
      (idealCount P D.ξ (M false) (W false) (M true) (W true) b).expect f|≤
      MenuError.oscillation f*SourceMovingMenuRates.rate
        (SourceCommonMenuError.commonCoefficient P D.ξ) (lowMass P.theta) P.bulkWeight N := by
  have h0 := OrderedZeroSourceCommonMenuError.original_count_error D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ false b f
  have h1 := OrderedZeroSourceCommonMenuError.original_count_error D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ true b f
  rw [original_outcome_expect D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare cats L hL i b f,
    idealCount,Counts.regimeLaw_expect,hθ]
  exact weighted_error P.theta_pos.le (by linarith [P.theta_small]) h0 h1

end FCAppendix.Affine.Tail04.OrderedZeroNativeCommonCount
