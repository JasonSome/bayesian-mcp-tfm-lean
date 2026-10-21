import FCAppendix.Affine.Tail04.OrderedNativePayoffActiveLaw
import FCAppendix.Affine.Tail04.ActivePhysicalPayoff
import FCAppendix.Affine.Tail04.OrderedNativeBandCarrierIC

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffActive
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeNoisySource OrderedNativePayoffBindings NativeActiveFiberCoordinates
open OrderedNativePayoffActiveLaw NativeLocalPolicy PartialNativeCoordinates NativeFiberEnumerations
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

def partialBidLaw : ProbabilityMeasure (Icc (installOriginal D P t ht).R (installOriginal D P t ht).Up) :=
  bidMarginal (π 2).1

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)

lemma count_subtype (kind : Fin N → Fin 4) (k : Fin 4) :
    (installOriginal D P t ht).count kind k=Fintype.card {r : Fin N // kind r=k} := by
  simp only [FiniteTailNoisyGame.Data.count,Fintype.card_subtype]

lemma count_rivalSet (i : Fin (N+1)) (kind : Fin N → Fin 4) (k : Fin 4) :
    (installOriginal D P t ht).count kind k=(rivalSet i kind k).card :=
  (rivalSet_card_filter i kind k).symm

include cats L hL in
theorem fiberCount_numerical (i : Fin (N+1)) (kind : Fin N → Fin 4)
    (b : Icc (1:ℝ) (regions D P hdR H hBH).U) :
    OrderedNoisyNativeCategories.fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i
      (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2)=
        numericalCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b
          (decide (0< (installOriginal D P t ht).count kind 0)) := by
  by_cases h : 0< (installOriginal D P t ht).count kind 0
  · have hc : 0< Fintype.card {r : Fin N // kind r=0} := by rw [←count_subtype D P t ht N];exact h
    let n:=Fintype.card {r : Fin N // kind r=0}-1
    have hn : n+1=Fintype.card {r : Fin N // kind r=0} := Nat.sub_add_cancel hc
    let e : Fin (n+1) ≃ {r : Fin N // kind r=0} :=
      (castEquiv hn).trans (Fintype.equivFin {r : Fin N // kind r=0}).symm
    rw [decide_eq_true h]
    exact fiberCount_low D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i kind n e cats L hL b
  · have hh : ∀ r,kind r≠0 := by
      intro r hr
      have hc : 0< Fintype.card {r : Fin N // kind r=0} :=
        Fintype.card_pos_iff.mpr ⟨⟨r,hr⟩⟩
      exact h (by rw [count_subtype D P t ht N];exact hc)
    rw [decide_eq_false h]
    exact fiberCount_noLow D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b hh

include cats L hL in
theorem fiber_payoff (i : Fin (N+1)) (kind : Fin N → Fin 4) (v : ℝ)
    (b : Icc (1:ℝ) (regions D P hdR H hBH).U) :
    affineCountUtility
      (OrderedNoisyNativeCategories.fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i
        (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2))
      v b D.eta D.heta0 D.heta1=
        ∫ row : Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U,
          ActivePhysicalPayoff.regimeValue (installOriginal D P t ht) (commonSize i kind)
            (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind)) (partialBidLaw D P t ht π) v (decide (0< (installOriginal D P t ht).count kind 0))
              (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) b row) ∂Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π)) := by
  let H0:=(localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)
  let H1:=(localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)
  rw [affineCountUtility,CountLaw.utility,fiberCount_numerical D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor N hrare cats L hL i kind b,
    numericalCount_expect D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b]
  apply integral_congr_ae
  filter_upwards [OrderedNativePayoffActiveLaw.common_distinct D P t ht hdR H hBH π N i kind b] with row hrow
  have he (reg : Bool) :
      (OrderedNativePayoffExperiment.perRegime (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) H0 H1 (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) b row) 0 reg
        (decide (0< (installOriginal D P t ht).count kind 0))).expect
          (fun r => userPayoff v b 0 (Schedule.affine 2 D.eta D.heta0 D.heta1).charge
            (Schedule.once 2).charge r.val)=
        ActivePhysicalPayoff.value (installOriginal D P t ht) (commonSize i kind) (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind)) (partialBidLaw D P t ht π) v
          reg (decide (0< (installOriginal D P t ht).count kind 0)) (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) b row) := by
    by_cases h : zeroSize i kind≤oneSize i kind
    · have hfin : H0.val≤H1.val := h
      erw [OrderedNativePayoffExperiment.perRegime,if_pos hfin,
        NativeHighExperiment.perRegime_physical (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) H0 H1 (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) b row) 0 D.hgap
          (fun j k hjk hj => hjk (hrow hj)),
        localData_marksLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H0,
        localData_marksLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H1,
        localData_signalProbability D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H0]
      rw [min_eq_left h,max_eq_right h]
      rfl
    · have hfin : ¬H0.val≤H1.val := h
      have hrev : oneSize i kind≤zeroSize i kind := Nat.le_of_lt (Nat.lt_of_not_ge h)
      erw [OrderedNativePayoffExperiment.perRegime,if_neg hfin,
        NativeHighExperiment.perRegime_physical (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) H1 H0 (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) b row) 0 D.hgap
          (fun j k hjk hj => hjk (hrow hj)),
        localData_marksLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H1,
        localData_marksLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H0,
        localData_signalProbability D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H1]
      rw [min_eq_right hrev,max_eq_left hrev]
      rfl
  rw [IndependentCounts.expect_bernoulli]
  erw [he false,he true]
  rfl

include cats L hL in
theorem active_payoff (i : Fin (N+1)) (v : ℝ) (b : Icc (1:ℝ) D.U) :
    (∫ u : unitInterval,(problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i).payoff v
      (RawRoutes.action (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u))
        (le_trans (by norm_num) (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)).2.1) 2))=
      OrderedFiniteTailNoisyGame.activeExpected (installOriginal D P t ht) N (bidLaws D P t ht π,(v,b)) := by
  let C:=CommonList.iid (originalCategories P t ht) N
  let fy (kind : Fin N → Fin 4) (u : unitInterval) : ℝ :=
    ∫ row : Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U,
      ActivePhysicalPayoff.regimeValue (installOriginal D P t ht) (commonSize i kind) (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind))
        (partialBidLaw D P t ht π) v (decide (0< (installOriginal D P t ht).count kind 0))
        (Fin.cons (α:=fun _=>Icc (1:ℝ) D.B) (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row)
          ∂Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))
  have hi (kind : Fin N → Fin 4) : Integrable (fy kind) (volume : Measure unitInterval) := by
    unfold fy
    dsimp only [OrderedNativePayoffActiveLaw.commonLaw]
    erw [NoisyCommonRowLaw.original_common_noisy_law D P t ht π]
    exact ActivePhysicalPayoff.integrable_focal_average (installOriginal D P t ht) (commonSize i kind)
      (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind)) (partialBidLaw D P t ht π) v (decide (0< (installOriginal D P t ht).count kind 0)) b
      ((installOriginal D P t ht).commonLaw (bidLaws D P t ht π))
  have hp (u : unitInterval) :
      (problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i).payoff v
        (RawRoutes.action (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u))
          (le_trans (by norm_num) (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)).2.1) 2)=
        ∑ kind : Fin N → Fin 4,C.mass kind*fy kind u := by
    unfold Interim.Problem.payoff CountLaw.utility
    rw [OrderedNoisyNativeCategories.native_count_statistic_mixture D P t ht hdR H hBH πL π
      upperBid hupperBid hfloor N hrare i]
    unfold FiniteLaw.expect
    apply Finset.sum_congr rfl
    intro kind _
    congr 1
    exact fiber_payoff D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare cats L hL
      i kind v (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u))
  simp_rw [hp]
  rw [integral_finsetSum _ (fun kind _ => (hi kind).const_mul (C.mass kind))]
  simp_rw [integral_const_mul]
  unfold OrderedFiniteTailNoisyGame.activeExpected
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  unfold fy
  dsimp only [OrderedNativePayoffActiveLaw.commonLaw]
  erw [NoisyCommonRowLaw.original_common_noisy_law D P t ht π,
    ActivePhysicalPayoff.split_focal_integral (installOriginal D P t ht) (commonSize i kind)
      (min (zeroSize i kind) (oneSize i kind)) (max (zeroSize i kind) (oneSize i kind)) (partialBidLaw D P t ht π) v (decide (0< (installOriginal D P t ht).count kind 0)) b]
  simp only [OrderedFiniteTailNoisyGame.activeRegimeFiber,
    count_rivalSet D P t ht N i kind,commonSize,zeroSize,oneSize,rowLaw_eq_pi]
  let F : ℕ→ℝ := fun A =>
    ∫ row : Fin A→Icc (1:ℝ) (installOriginal D P t ht).U,
      (installOriginal D P t ht).activeRegimeFiber A
        (min (rivalSet i kind 2).card (rivalSet i kind 3).card)
        (max (rivalSet i kind 2).card (rivalSet i kind 3).card)
        (decide (0<(rivalSet i kind 0).card))
        ((v,b,partialBidLaw D P t ht π),row)
        ∂Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure
          ((installOriginal D P t ht).commonLaw (bidLaws D P t ht π)))
  change F (rivalSet i kind 1).card=F ((installOriginal D P t ht).count kind 1)
  exact congrArg F (count_rivalSet D P t ht N i kind 1).symm

include hrare cats L hL in
theorem bulk_tail_payoff (k : Fin 3) (hk : k≠2) (i : Fin (N+1))
    (x : Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k)) :
    (∫ u : unitInterval,(problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i).payoff (x.1:ℝ)
      (OrderedNativeBandCarrierIC.physicalBandAction D P t k x u))=
      SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x) := by
  fin_cases k
  · simpa only [OrderedNativeBandCarrierIC.physicalBandAction,LatentSpeciesCalculus.bandBase,
      LatentSpeciesCalculus.bandRoutes,Matrix.cons_val_zero,LatentNoisyPopulation.noisyAction,
      OriginalPopulation.bandAction,RawRoutes.action,CompactSourceBidLaws.noisyBid,
      SourceOrderedNoisyFixedPoint.payoff,Fin.isValue,Hybrid.activeNoisyRealBid,extendBid,Fin.cases_zero,Fin.cases_succ]
      using! active_payoff D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare cats L hL i x.1
        (extendBid D.huU x.2)
  · simpa only [OrderedNativeBandCarrierIC.physicalBandAction,LatentSpeciesCalculus.bandBase,
      LatentSpeciesCalculus.bandRoutes,Matrix.cons_val_succ,Matrix.cons_val_zero,
      LatentNoisyPopulation.noisyAction,OriginalPopulation.bandAction,RawRoutes.action,
      CompactSourceBidLaws.noisyBid,SourceOrderedNoisyFixedPoint.payoff,Fin.isValue,Hybrid.activeNoisyRealBid,extendBid,Fin.cases_zero,Fin.cases_succ]
      using! active_payoff D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare cats L hL i x.1 x.2
  · exact (hk rfl).elim

end FCAppendix.Affine.Tail04.OrderedNativePayoffActive
