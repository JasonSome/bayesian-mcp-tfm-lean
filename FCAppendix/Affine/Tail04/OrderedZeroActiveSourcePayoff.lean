import FCAppendix.Affine.Tail04.OrderedZeroActiveFiberLaw
import FCAppendix.Affine.Tail04.OrderedZeroNoiseFiniteGame

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroActiveSourcePayoff
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings NativeActiveFiberCoordinates
open OrderedZeroActiveFiberLaw NativeLocalPolicy PartialNativeCoordinates NativeFiberEnumerations
open scoped BigOperators

theorem base_count_utility (D : FiniteTailNoisyGame.Data) (A H0 H1 : ℕ)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ)
    (b : Icc (1:ℝ) D.U) (row : Fin A→ Icc (1:ℝ) D.U) (reg low : Bool) :
    affineCountUtility
      (AllCountActiveFiniteGain.physicalCount H0 H1 D.c D.ξ D.U D.R D.Up D.width
        (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
        (ZeroNoiseFiniteGame.privateBayes D H0 μP).val (Fin.cons (α:=fun _=>Icc (1:ℝ) D.U) b row) 0)
      v b D.eta D.heta0 D.heta1=
        ZeroNoiseFiniteGame.activeFiber D A H0 H1 low reg ((v,b,μP),row) := by
  by_cases h : H0=H1
  · simp only [AllCountActiveFiniteGain.physicalCount,if_pos h,
      ZeroNoiseFiniteGame.activeFiber,FiniteTailNoisyGame.Data.insertActive,
      WeakProbability.mk_val,EqualPrivateCountPayoff.utility]
    rw [EqualPrivateActiveRelabel.countLaw_sorted D.hξ]
    rfl
  · simp only [AllCountActiveFiniteGain.physicalCount,if_neg h,
      ZeroNoiseFiniteGame.activeFiber,FiniteTailNoisyGame.Data.insertActive]

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ H≤ upperBid v) (N : ℕ)
local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "m" => N+1
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℝ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

private lemma castMarketRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((n+1:ℝ)*p)≤q) : x+y*((((n+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h
local notation "Γ" => OrderedNativeZeroNoiseSource.game D P t ht hdR H hUH πL π
  upperBid hupperBid hfloor m (castMarketRare hrare)
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "Ds" => installOriginal D P t ht
local notation "ρA" => bidMarginal (Subtype.val (active D P t ht π))
local notation "μP" => bidMarginal (Subtype.val (π 2))

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)
  [hA : NullSingletonClass (bidMarginal (Subtype.val (OrderedNativeZeroNoiseSource.active D P t ht π)) : Measure (Icc (1:ℝ) D.U))]

lemma count_subtype (kind : Fin N→ Fin 4) (k : Fin 4) :
    (Ds).count kind k=Fintype.card {r : Fin N // kind r=k} := by
  simp only [FiniteTailNoisyGame.Data.count,Fintype.card_subtype]

lemma count_rivalSet (i : Fin m) (kind : Fin N→ Fin 4) (k : Fin 4) :
    (Ds).count kind k=(rivalSet i kind k).card :=
  (rivalSet_card_filter i kind k).symm

include cats L hL in
theorem fiberCount_numerical (i : Fin m) (kind : Fin N→ Fin 4) (b : Icc (1:ℝ) (E).U) :
    OrderedZeroNativeCategories.fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      kind i (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2)=
      numericalCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b
        (decide (0< (Ds).count kind 0)) := by
  by_cases h : 0< (Ds).count kind 0
  · have hc : 0< Fintype.card {r : Fin N // kind r=0} := by
      rw [←count_subtype D P t ht N]
      exact h
    let n := Fintype.card {r : Fin N // kind r=0}-1
    have hn : n+1=Fintype.card {r : Fin N // kind r=0} := Nat.sub_add_cancel hc
    let e : Fin (n+1)≃{r : Fin N // kind r=0} :=
      (castEquiv hn).trans (Fintype.equivFin {r : Fin N // kind r=0}).symm
    rw [decide_eq_true h]
    exact fiberCount_low D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      i kind n e cats L hL b
  · have hh : ∀r,kind r≠0 := by
      intro r hr
      have hc : 0< Fintype.card {r : Fin N // kind r=0} :=
        Fintype.card_pos_iff.mpr ⟨⟨r,hr⟩⟩
      exact h (by rw [count_subtype D P t ht N];exact hc)
    rw [decide_eq_false h]
    exact fiberCount_noLow D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b hh

include cats L hL in
theorem fiber_payoff (i : Fin m) (kind : Fin N→ Fin 4) (v : ℝ) (b : Icc (1:ℝ) (E).U) :
    affineCountUtility
      (OrderedZeroNativeCategories.fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        kind i (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2))
      v b D.eta D.heta0 D.heta1=
      ∫row : Fin (commonSize i kind)→ Icc (1:ℝ) (E).U,
        OrderedZeroNoiseFiniteGame.activeRegimeFiber Ds (commonSize i kind)
          (zeroSize i kind) (oneSize i kind) (decide (0< (Ds).count kind 0)) ((v,b,μP),row)
        ∂Measure.pi (fun _ : Fin (commonSize i kind)=>ProbabilityMeasure.toMeasure ρA) := by
  let H0 := (K).finiteCount (rivalSet i kind 2)
  let H1 := (K).finiteCount (rivalSet i kind 3)
  have hgap : (1-D.ξ)*D.U< D.R :=
    (mul_le_mul_of_nonneg_left (base_active_le_physical D)
      (sub_nonneg.mpr D.hξ1.le)).trans_lt D.hgap
  rw [affineCountUtility,CountLaw.utility,fiberCount_numerical D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare cats L hL i kind b,
    numericalCount_expect D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b]
  apply integral_congr_ae
  filter_upwards [OrderedZeroActiveFiberLaw.common_distinct D P t ht hdR H hUH π N i kind b] with row hrow
  have he (reg : Bool) :
      (OrderedNativePayoffExperiment.perRegime K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b row) 0 reg
        (decide (0< (Ds).count kind 0))).expect
          (fun r=> userPayoff v b 0 (Schedule.affine 2 D.eta D.heta0 D.heta1).charge
            (Schedule.once 2).charge r.val)=
        ZeroNoiseFiniteGame.activeFiber Ds (commonSize i kind)
          (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind))
          (decide (0< (Ds).count kind 0)) reg ((v,b,μP),row) := by
    by_cases h : zeroSize i kind≤oneSize i kind
    · have hfin : H0.val≤H1.val := h
      rw [OrderedNativePayoffExperiment.perRegime,if_pos hfin,
        NativeHighExperiment.perRegime_physical K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b row) 0 hgap
          (fun j k hjk hj=> hjk (hrow hj)),
        localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) H0,
        localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) H1,
        localData_signalProbability D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) H0,
        min_eq_left h,max_eq_right h]
      exact base_count_utility Ds (commonSize i kind) (zeroSize i kind) (oneSize i kind)
        μP v b row reg (decide (0< (Ds).count kind 0))
    · have hfin : ¬H0.val≤H1.val := h
      have hr : oneSize i kind≤zeroSize i kind := Nat.le_of_lt (Nat.lt_of_not_ge h)
      rw [OrderedNativePayoffExperiment.perRegime,if_neg hfin,
        NativeHighExperiment.perRegime_physical K H1 H0 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b row) 0 hgap
          (fun j k hjk hj=> hjk (hrow hj)),
        localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) H1,
        localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) H0,
        localData_signalProbability D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) H1,
        min_eq_right hr,max_eq_left hr]
      exact base_count_utility Ds (commonSize i kind) (oneSize i kind) (zeroSize i kind)
        μP v b row reg (decide (0< (Ds).count kind 0))
  calc
    _=(IndependentCounts.bernoulli (Q).θ (Q).θ_nonneg (Q).θ_le_one).expect
        (fun reg=>ZeroNoiseFiniteGame.activeFiber Ds (commonSize i kind)
          (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind))
          (decide (0< (Ds).count kind 0)) reg ((v,b,μP),row)) :=
      congrArg (fun f : Bool→ℝ =>
        (IndependentCounts.bernoulli (Q).θ (Q).θ_nonneg (Q).θ_le_one).expect f) (funext he)
    _=_ := by
      rw [IndependentCounts.expect_bernoulli]
      rfl

include hdR H hUH πL upperBid hupperBid hfloor hrare cats L hL in
theorem active_payoff (i : Fin m) (v : ℝ) (b : Icc (1:ℝ) D.U) :
    (problem Γ i).payoff v
      (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)=
      OrderedZeroNoiseFiniteGame.activeExpected Ds N (bidLaws D P t ht π,(v,b)) := by
  unfold Interim.Problem.payoff CountLaw.utility
  rw [OrderedZeroNativeCategories.native_count_statistic_mixture D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare i]
  unfold OrderedZeroNoiseFiniteGame.activeExpected FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  change affineCountUtility
      (OrderedZeroNativeCategories.fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        kind i (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2))
      v b D.eta D.heta0 D.heta1=_
  rw [fiber_payoff D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare cats L hL i kind v b]
  have hcommon : ρA=(Ds).commonLaw (bidLaws D P t ht π) :=
    ZeroCommonRowLaw.original_common_base_law D P t ht π
  rw [hcommon]
  simp only [count_rivalSet D P t ht N i kind,commonSize,zeroSize,oneSize,rowLaw_eq_pi]
  let F : ℕ→ℝ := fun A =>
    ∫ row : Fin A→Icc (1:ℝ) (Ds).U,
      OrderedZeroNoiseFiniteGame.activeRegimeFiber Ds A
        (rivalSet i kind 2).card (rivalSet i kind 3).card
        (decide (0<(rivalSet i kind 0).card)) ((v,b,μP),row)
        ∂Measure.pi (fun _ : Fin A=>ProbabilityMeasure.toMeasure
          ((Ds).commonLaw (bidLaws D P t ht π)))
  change F (rivalSet i kind 1).card=F ((Ds).count kind 1)
  exact congrArg F (count_rivalSet D P t ht N i kind 1).symm

include hdR H hUH πL upperBid hupperBid hfloor hrare cats L hL in
theorem bulk_tail_payoff (k : Fin 3) (hk : k≠2) (i : Fin m)
    (x : Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k)) :
    (problem Γ i).payoff (x.1:ℝ)
      (OriginalPopulation.bandAction (bidLo_pos D k).le 2 le_rfl x.2)=
      OrderedZeroNoiseFiniteGame.sourcePayoff D P t ht N k (π,x) := by
  fin_cases k
  · simpa only [OrderedZeroNoiseFiniteGame.sourcePayoff,OriginalPopulation.bandAction,RawRoutes.action,
      Fin.isValue,Fin.cases_zero,Fin.cases_succ,extendBid] using! active_payoff D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        cats L hL i x.1 (extendBid D.huU x.2)
  · simpa only [OrderedZeroNoiseFiniteGame.sourcePayoff,OriginalPopulation.bandAction,RawRoutes.action,
      Fin.isValue,Fin.cases_zero,Fin.cases_succ,extendBid] using! active_payoff D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        cats L hL i x.1 x.2
  · exact (hk rfl).elim

end FCAppendix.Affine.Tail04.OrderedZeroActiveSourcePayoff
