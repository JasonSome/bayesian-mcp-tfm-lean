import FCAppendix.Affine.Tail04.OrderedNativePayoffPartialNumerical
import FCAppendix.Affine.Tail04.OrderedNativePayoffActive

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffPartial
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeNoisySource OrderedNativePayoffBindings
open NativeLocalPolicy NativePartialExperiment NativePartialTerminal
open NativePartialProductReduction NativeActiveFiberCoordinates NativeFiberEnumerations
open PartialNativeCoordinates OrderedNativePayoffActive
open OrderedNativePayoffPartialTerminal
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)

private lemma integrable_regime (A own other : ℕ) (low : Bool)
    (j : Fin own) (v : ℝ) (price : Icc D.R D.Up) :
    Integrable (fun b : Fin A→ Icc (1:ℝ) D.U =>
      OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht) A own other low j ((v,price,(NativePartialC1Integral.partialBidLaw D P t ht π)),b))
        (Measure.pi (fun _ : Fin A => ((OrderedNativePayoffPartialNumerical.commonBaseLaw D P t ht π) : Measure _))) := by
  let f : C(Fin A→ Icc (1:ℝ) D.U,ℝ) :=
    ⟨fun b => OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht) A own other low j
      ((v,price,NativePartialC1Integral.partialBidLaw D P t ht π),b),
      (OrderedFiniteTailNoisyGame.continuous_partialOwnRegimeFiber (installOriginal D P t ht) A own other low j).comp
      (continuous_const.prodMk continuous_id)⟩
  let g := ContinuousMap.equivBoundedOfCompact _ _ f
  exact integrable_bounded _ _ f.continuous.measurable ‖g‖ (fun b => g.norm_coe_le_norm b)

include cats L hL in
theorem fiber_ownNoise_payoff (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (v : ℝ) (price : Icc D.R D.Up) :
    (∫ a : unitInterval,affineCountUtility
      (OrderedNoisyNativeCategories.fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor
        N hrare kind i (RawRoutes.action (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a)
          (D.hR.le.trans (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a).2.1) 1))
        v (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a) D.eta D.heta0 D.heta1)=
      ∫ base : Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.U,
        OrderedFiniteTailNoisyGame.partialPattern (installOriginal D P t ht) kind ((v,price,(NativePartialC1Integral.partialBidLaw D P t ht π)),base)
          ∂Measure.pi (fun _ : Fin ((installOriginal D P t ht).count kind 1) => ((OrderedNativePayoffPartialNumerical.commonBaseLaw D P t ht π) : Measure _)) := by
  rw [OrderedNativePayoffPartialLaw.original_partial_numeric D P t ht hdR H hBH πL π upperBid
    hupperBid hfloor N hrare i kind cats L hL v price,
    OrderedNativePayoffPartialNumerical.numerical_integral_eq D P t ht hdR H hBH πL π upperBid
      hupperBid hfloor N hrare i kind false v price,
    OrderedNativePayoffPartialNumerical.numerical_integral_eq D P t ht hdR H hBH πL π upperBid
      hupperBid hfloor N hrare i kind true v price]
  have hi (side : Bool) := integrable_regime D P t ht π (commonSize i kind)
    (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side).val (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side).val
      (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v price
  rw [←integral_const_mul,←integral_const_mul,
    ←integral_add ((hi false).const_mul (1/2:ℝ)) ((hi true).const_mul (1/2:ℝ))]
  let F (A nL n0 n1 : ℕ) : ℝ := ∫ base : Fin A→Icc (1:ℝ) D.U,
    (1/2:ℝ)*OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht)
      A (n0+1) n1 (decide (0<nL)) 0 ((v,price,NativePartialC1Integral.partialBidLaw D P t ht π),base)+
    (1/2:ℝ)*OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht)
      A (n1+1) n0 (decide (0<nL)) 0 ((v,price,NativePartialC1Integral.partialBidLaw D P t ht π),base)
      ∂Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure
        (OrderedNativePayoffPartialNumerical.commonBaseLaw D P t ht π))
  have castTerm (A n k other : ℕ) (h : n=k+1) (low : Bool)
      (base : Fin A→Icc (1:ℝ) D.U) :
      OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht)
        A n other low (Fin.cast h.symm 0) ((v,price,NativePartialC1Integral.partialBidLaw D P t ht π),base)=
      OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht)
        A (k+1) other low 0 ((v,price,NativePartialC1Integral.partialBidLaw D P t ht π),base) := by
    subst n
    rfl
  have heq (side : Bool) (base : Fin (commonSize i kind)→Icc (1:ℝ) D.U) :
      OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht) (commonSize i kind)
        (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side).val
        (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side).val
        (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind)
        (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side)
        ((v,price,NativePartialC1Integral.partialBidLaw D P t ht π),base)=
      if side then OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht)
        (commonSize i kind) ((rivalSet i kind 3).card+1) (rivalSet i kind 2).card
        (decide (0<(installOriginal D P t ht).count kind 0)) 0
        ((v,price,NativePartialC1Integral.partialBidLaw D P t ht π),base)
      else OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht)
        (commonSize i kind) ((rivalSet i kind 2).card+1) (rivalSet i kind 3).card
        (decide (0<(installOriginal D P t ht).count kind 0)) 0
        ((v,price,NativePartialC1Integral.partialBidLaw D P t ht π),base) := by
    cases side
    · exact castTerm _ _ _ _ (insert_card _ i (focal_not_mem_rivalSet i kind 2)) _ base
    · exact castTerm _ _ _ _ (insert_card _ i (focal_not_mem_rivalSet i kind 3)) _ base
  calc
    _=F (commonSize i kind) ((installOriginal D P t ht).count kind 0)
        (rivalSet i kind 2).card (rivalSet i kind 3).card := by
      apply integral_congr_ae
      exact ae_of_all _ fun base => by
        dsimp only
        rw [heq false base,heq true base]
        rfl
    _=F ((installOriginal D P t ht).count kind 1) ((installOriginal D P t ht).count kind 0)
        ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3) := by
      have hA : commonSize i kind=(installOriginal D P t ht).count kind 1 :=
        (count_rivalSet D P t ht N i kind 1).symm
      have h0 := (count_rivalSet D P t ht N i kind 2).symm
      have h1 := (count_rivalSet D P t ht N i kind 3).symm
      exact (congrArg (fun n => F n ((installOriginal D P t ht).count kind 0)
          (rivalSet i kind 2).card (rivalSet i kind 3).card) hA).trans
        ((congrArg (fun n => F ((installOriginal D P t ht).count kind 1)
          ((installOriginal D P t ht).count kind 0) n (rivalSet i kind 3).card) h0).trans
        (congrArg (fun n => F ((installOriginal D P t ht).count kind 1)
          ((installOriginal D P t ht).count kind 0) ((installOriginal D P t ht).count kind 2) n) h1))
    _=_ := rfl

lemma integrable_fiber_ownNoise (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (v : ℝ) (price : Icc D.R D.Up) :
    Integrable (fun a : unitInterval => affineCountUtility
      (OrderedNoisyNativeCategories.fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor
        N hrare kind i (RawRoutes.action (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a)
          (D.hR.le.trans (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a).2.1) 1))
        v (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a) D.eta D.heta0 D.heta1) volume := by
  let μ := OrderedNoisyNativeCategories.fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid
    hfloor N hrare kind
  have hi (side : Bool) : Integrable (fun a : unitInterval =>
      ∫ w,OrderedNativePayoffPartialLaw.nativeValue D P t ht hdR H hBH πL π upperBid hupperBid
        hfloor N hrare i side v (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a) w ∂μ) volume := by
    have hf := (OrderedNativePayoffPartialLaw.measurable_nativeValue D P t ht hdR H hBH πL π upperBid
      hupperBid hfloor N hrare i side v).comp
        (((measurable_noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price).comp measurable_fst).prodMk measurable_snd)
    exact (integrable_bounded ((volume : Measure unitInterval).prod μ) _ hf (|v|+D.V)
      (fun x => OrderedNativePayoffPartialLaw.nativeValue_bound D P t ht hdR H hBH πL π upperBid
        hupperBid hfloor N hrare i side v _ _)).integral_prod_left
  simp_rw [OrderedNativePayoffPartialLaw.fiber_payoff_halves D P t ht hdR H hBH πL π upperBid
    hupperBid hfloor N hrare i kind]
  exact ((hi false).const_mul (1/2:ℝ)).add ((hi true).const_mul (1/2:ℝ))

include cats L hL in
theorem partial_payoff (i : Fin (N+1)) (v : ℝ) (b : Icc D.R D.Up) :
    (∫ u : unitInterval,(problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i).payoff v
      (RawRoutes.action (noisyBid D.hR D.heps.le (b,u))
        (D.hR.le.trans (noisyBid D.hR D.heps.le (b,u)).2.1) 1))=
      OrderedFiniteTailNoisyGame.partialExpected (installOriginal D P t ht) N (bidLaws D P t ht π,(v,b)) := by
  let C := CommonList.iid (originalCategories P t ht) N
  let fy (kind : Fin N→ Fin 4) (u : unitInterval) : ℝ := affineCountUtility
    (OrderedNoisyNativeCategories.fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor
      N hrare kind i (RawRoutes.action (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b u)
        (D.hR.le.trans (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b u).2.1) 1))
      v (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b u) D.eta D.heta0 D.heta1
  have hi (kind : Fin N→ Fin 4) : Integrable (fy kind) (volume : Measure unitInterval) :=
    integrable_fiber_ownNoise D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind v b
  have he (u : unitInterval) :
      (problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i).payoff v
        (RawRoutes.action (noisyBid D.hR D.heps.le (b,u))
          (D.hR.le.trans (noisyBid D.hR D.heps.le (b,u)).2.1) 1)=
        ∑ kind : Fin N→ Fin 4,C.mass kind*fy kind u := by
    unfold Interim.Problem.payoff CountLaw.utility
    rw [OrderedNoisyNativeCategories.native_count_statistic_mixture D P t ht hdR H hBH πL π
      upperBid hupperBid hfloor N hrare i]
    unfold FiniteLaw.expect
    apply Finset.sum_congr rfl
    intro kind _
    rfl
  simp_rw [he]
  rw [integral_finsetSum _ (fun kind _ => (hi kind).const_mul (C.mass kind))]
  simp_rw [integral_const_mul]
  unfold OrderedFiniteTailNoisyGame.partialExpected
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  simpa only [fy,rowLaw_eq_pi,OrderedNativePayoffPartialNumerical.commonBaseLaw,
    NativePartialC1Integral.partialBidLaw,SourceTailNoisyFixedPoint.bidLaws] using!
    fiber_ownNoise_payoff D P t ht hdR H hBH πL π upperBid hupperBid hfloor
    N hrare cats L hL i kind v b

include cats L hL in
theorem partial_carrier_payoff (i : Fin (N+1))
    (x : Icc (valueLo P 2) (valueHi P t 2)×Icc (bidLo D 2) (bidHi D 2)) :
    (∫ u : unitInterval,(problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i).payoff (x.1:ℝ)
      (OrderedNativeBandCarrierIC.physicalBandAction D P t 2 x u))=
      SourceOrderedNoisyFixedPoint.payoff D P t ht N 2 (π,x) := by
  simpa only [OrderedNativeBandCarrierIC.physicalBandAction,LatentSpeciesCalculus.bandBase,
    LatentSpeciesCalculus.bandRoutes,Matrix.cons_val_succ,Matrix.cons_val_zero,
    LatentNoisyPopulation.noisyAction,OriginalPopulation.bandAction,RawRoutes.action,
    CompactSourceBidLaws.noisyBid,SourceOrderedNoisyFixedPoint.payoff,Fin.isValue]
    using! partial_payoff D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      cats L hL i x.1 x.2

include cats L hL in
theorem all_species_payoff (k : Fin 3) (i : Fin (N+1))
    (x : Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k)) :
    (∫ u : unitInterval,(problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i).payoff (x.1:ℝ)
      (OrderedNativeBandCarrierIC.physicalBandAction D P t k x u))=
      SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x) := by
  by_cases hk : k=2
  · subst k
    exact partial_carrier_payoff D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      cats L hL i x
  · exact OrderedNativePayoffActive.bulk_tail_payoff D P t ht hdR H hBH πL π upperBid hupperBid
      hfloor N hrare cats L hL k hk i x

end FCAppendix.Affine.Tail04.OrderedNativePayoffPartial
