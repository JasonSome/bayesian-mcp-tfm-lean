import FCAppendix.Affine.Tail04.OrderedZeroPartialNumericalPayoff
import FCAppendix.Affine.Tail04.OrderedZeroActiveSourcePayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroPartialSourcePayoff
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings
open NativeLocalPolicy NativePartialExperiment NativePartialTerminal
open NativePartialProductReduction NativeActiveFiberCoordinates NativeFiberEnumerations
open PartialNativeCoordinates OrderedZeroActiveSourcePayoff
open OrderedNativePayoffPartialTerminal
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

include hrare in
private lemma fiberRare : (1-D.ξ)*D.U+D.ξ*D.U*(((N:ℝ)+1)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R := by
  simpa only [Nat.cast_add,Nat.cast_one] using hrare
local notation "hfr" => fiberRare D P t N hrare

local notation "Γ" => OrderedNativeZeroNoiseSource.game D P t ht hdR H hUH πL π
  upperBid hupperBid hfloor (N+1) hrare
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Ds" => installOriginal D P t ht
set_option quotPrecheck false in
local notation "μA" => (Ds).commonLaw (bidLaws D P t ht π)
set_option quotPrecheck false in
local notation "μP" => bidMarginal (π 2).1
set_option quotPrecheck false in
local notation "ρA" => bidMarginal (OrderedNativeZeroNoiseSource.active D P t ht π).1

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw) (hL : πL=L.joint)
  [NullSingletonClass (ProbabilityMeasure.toMeasure
    (bidMarginal (OrderedNativeZeroNoiseSource.active D P t ht π).1))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (π 2).1).map (fun x=>(x.2:ℝ)))]

include cats L hL in
theorem fiber_payoff (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (v : ℝ) (price : Icc D.R D.Up) :
    affineCountUtility
      (OrderedZeroNativeCategories.fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor
        N hfr kind i (RawRoutes.action price (D.hR.le.trans price.2.1) 1))
      v price D.eta D.heta0 D.heta1=
    ∫ common : Fin ((Ds).count kind 1)→ Icc (1:ℝ) D.U,
      OrderedZeroNoiseFiniteGame.partialPattern Ds kind ((v,price,μP),common)
        ∂Measure.pi (fun _ : Fin ((Ds).count kind 1)=>(ProbabilityMeasure.toMeasure μA)) := by
  rw [OrderedZeroPartialFiberLaw.original_partial_numeric D P t ht hdR H hUH πL π upperBid
    hupperBid hfloor N hfr i kind cats L hL v price,
    OrderedZeroPartialNumericalPayoff.numerical_integral_eq D P t ht hdR H hUH πL π upperBid
      hupperBid hfloor N hrare i kind false v price,
    OrderedZeroPartialNumericalPayoff.numerical_integral_eq D P t ht hdR H hUH πL π upperBid
      hupperBid hfloor N hrare i kind true v price]
  have hi (side : Bool) : Integrable (fun common : Fin (commonSize i kind)→ Icc (1:ℝ) D.U=>
      OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds (commonSize i kind)
        (ownTotal K i kind side).val (otherTotal K i kind side).val
        (OrderedZeroPartialFiberLaw.lowPresent D P t ht kind) (focalIndex K i kind side)
        ((v,price,μP),common)) (Measure.pi (fun _ : Fin (commonSize i kind)=>(ProbabilityMeasure.toMeasure μA))) := by
    have hh := OrderedZeroPartialIntegral.integrable_regime D P t ht hdR H hUH πL π upperBid hupperBid
      hfloor N hrare (commonSize i kind) (ownTotal K i kind side) (otherTotal K i kind side)
      (physical side) (OrderedZeroPartialFiberLaw.lowPresent D P t ht kind) (focalIndex K i kind side) v price
    have he : ρA=μA := ZeroCommonRowLaw.original_common_base_law D P t ht π
    simpa only [he] using! hh
  have hadd := integral_add ((hi false).const_mul (1/2:ℝ)) ((hi true).const_mul (1/2:ℝ))
  simp only [integral_const_mul] at hadd
  refine hadd.symm.trans ?_
  let F (A nL n0 n1 : ℕ) : ℝ := ∫ base : Fin A→Icc (1:ℝ) D.U,
    (1/2:ℝ)*OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds
      A (n0+1) n1 (decide (0<nL)) 0 ((v,price,μP),base)+
    (1/2:ℝ)*OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds
      A (n1+1) n0 (decide (0<nL)) 0 ((v,price,μP),base)
      ∂Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure
        μA)
  have castTerm (A n k other : ℕ) (h : n=k+1) (low : Bool)
      (base : Fin A→Icc (1:ℝ) D.U) :
      OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds
        A n other low (Fin.cast h.symm 0) ((v,price,μP),base)=
      OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds
        A (k+1) other low 0 ((v,price,μP),base) := by
    subst n
    rfl
  have heq (side : Bool) (base : Fin (commonSize i kind)→Icc (1:ℝ) D.U) :
      OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds (commonSize i kind)
        (ownTotal K i kind side).val
        (otherTotal K i kind side).val
        (OrderedZeroPartialFiberLaw.lowPresent D P t ht kind)
        (focalIndex K i kind side)
        ((v,price,μP),base)=
      if side then OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds
        (commonSize i kind) ((rivalSet i kind 3).card+1) (rivalSet i kind 2).card
        (decide (0<(Ds).count kind 0)) 0
        ((v,price,μP),base)
      else OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds
        (commonSize i kind) ((rivalSet i kind 2).card+1) (rivalSet i kind 3).card
        (decide (0<(Ds).count kind 0)) 0
        ((v,price,μP),base) := by
    cases side
    · exact castTerm _ _ _ _ (insert_card _ i (focal_not_mem_rivalSet i kind 2)) _ base
    · exact castTerm _ _ _ _ (insert_card _ i (focal_not_mem_rivalSet i kind 3)) _ base
  calc
    _=F (commonSize i kind) ((Ds).count kind 0)
        (rivalSet i kind 2).card (rivalSet i kind 3).card := by
      apply integral_congr_ae
      exact ae_of_all _ fun base => by
        dsimp only
        rw [heq false base,heq true base]
        rfl
    _=F ((Ds).count kind 1) ((Ds).count kind 0)
        ((Ds).count kind 2) ((Ds).count kind 3) := by
      have hA : commonSize i kind=(Ds).count kind 1 :=
        (count_rivalSet D P t ht N i kind 1).symm
      have h0 := (count_rivalSet D P t ht N i kind 2).symm
      have h1 := (count_rivalSet D P t ht N i kind 3).symm
      exact (congrArg (fun n => F n ((Ds).count kind 0)
          (rivalSet i kind 2).card (rivalSet i kind 3).card) hA).trans
        ((congrArg (fun n => F ((Ds).count kind 1)
          ((Ds).count kind 0) n (rivalSet i kind 3).card) h0).trans
        (congrArg (fun n => F ((Ds).count kind 1)
          ((Ds).count kind 0) ((Ds).count kind 2) n) h1))
    _=_ := rfl

include cats L hL in
theorem partial_payoff (i : Fin (N+1)) (v : ℝ) (price : Icc D.R D.Up) :
    (problem Γ i).payoff v (RawRoutes.action price (D.hR.le.trans price.2.1) 1)=
      OrderedZeroNoiseFiniteGame.partialExpected Ds N (bidLaws D P t ht π,(v,price)) := by
  unfold Interim.Problem.payoff CountLaw.utility
  rw [OrderedZeroNativeCategories.native_count_statistic_mixture D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hfr i]
  unfold OrderedZeroNoiseFiniteGame.partialExpected FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  change affineCountUtility
      (OrderedZeroNativeCategories.fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor
        N hfr kind i (RawRoutes.action price (D.hR.le.trans price.2.1) 1))
      v price D.eta D.heta0 D.heta1=_
  simpa only [rowLaw_eq_pi] using! fiber_payoff D P t ht hdR H hUH πL π upperBid hupperBid
    hfloor N hrare cats L hL i kind v price

include cats L hL in
theorem partial_carrier_payoff (i : Fin (N+1))
    (x : Icc (valueLo P 2) (valueHi P t 2)×Icc (bidLo D 2) (bidHi D 2)) :
    (problem Γ i).payoff (x.1:ℝ)
      (OriginalPopulation.bandAction (bidLo_pos D 2).le 1 (by omega) x.2)=
      OrderedZeroNoiseFiniteGame.sourcePayoff D P t ht N 2 (π,x) := by
  simpa only [OrderedZeroNoiseFiniteGame.sourcePayoff,OriginalPopulation.bandAction,RawRoutes.action,
    Fin.isValue,Fin.cases_zero,Fin.cases_succ] using! partial_payoff D P t ht hdR H hUH πL π upperBid hupperBid hfloor
      N hrare cats L hL i x.1 x.2

include cats L hL in
theorem all_species_payoff (k : Fin 3) (i : Fin (N+1))
    (x : Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k)) :
    (problem Γ i).payoff (x.1:ℝ)
      (OriginalPopulation.bandAction (bidLo_pos D k).le
        (if k=2 then 1 else 2) (by split_ifs <;> omega) x.2)=
      OrderedZeroNoiseFiniteGame.sourcePayoff D P t ht N k (π,x) := by
  by_cases hk : k=2
  · subst k
    simpa only [ite_true] using partial_carrier_payoff D P t ht hdR H hUH πL π upperBid
      hupperBid hfloor N hrare cats L hL i x
  · simpa only [if_neg hk] using OrderedZeroActiveSourcePayoff.bulk_tail_payoff D P t ht hdR H hUH
      πL π upperBid hupperBid hfloor N hfr cats L hL k hk i x

end FCAppendix.Affine.Tail04.OrderedZeroPartialSourcePayoff
