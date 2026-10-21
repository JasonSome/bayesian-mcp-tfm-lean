import FCAppendix.Affine.Tail04.OrderedNativePayoffPartialIntegral

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffPartialNumerical
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open OrderedNativeNoisySource OrderedNativePayoffBindings SourceTailNoisyFixedPoint
open NativeLocalPolicy NativePartialExperiment NativePartialTerminal
open NativePartialProductReduction NativeActiveFiberCoordinates NativeFiberEnumerations
open PartialNativeCoordinates EqualPrivateUpper PrivateRowSorting NativeHighExperiment
open OrderedNativePayoffPartialExperiment OrderedNativePayoffPartialTerminal
open OrderedNativePayoffPartialReduction

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

def commonBaseLaw : ProbabilityMeasure (Icc (1:ℝ) D.U) :=
  (installOriginal D P t ht).commonLaw (bidLaws D P t ht π)

variable (i : Fin (N+1)) (kind : Fin N → Fin 4) (side : Bool)

lemma numericalValue_inserted (v : ℝ) (price : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp)
    (b : Fin (commonSize i kind)→ Icc (1:ℝ) (regions D P hdR H hBH).U) (pub : unitInterval) (payload : RawPayload (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))) :
    OrderedNativePayoffPartialLaw.numericalValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor
      N hrare i kind side v price (b,(pub,payload))=
    insertedValue (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (OrderedNativePayoffPartialTerminal.physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) side (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (post_card (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side)
      v price b pub payload := by
  cases side <;> rfl

lemma numerical_payload_integral (v : ℝ) (price : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp) :
    (∫ x,OrderedNativePayoffPartialLaw.numericalValue D P t ht hdR H hBH πL π upperBid hupperBid
      hfloor N hrare i kind side v price x ∂((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))))=
      ∫ b,∫ pub : unitInterval,∫ row,∫ u : unitInterval,
        value (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (OrderedNativePayoffPartialTerminal.physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v price b
          (Function.update row (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (Sum.inr price)) pub u
            ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH (post0 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (post1 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) side).val (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))) ∂(volume : Measure unitInterval) ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))) := by
  let f := OrderedNativePayoffPartialLaw.numericalValue D P t ht hdR H hBH πL π upperBid hupperBid
    hfloor N hrare i kind side v price
  have hf : Measurable f := (OrderedNativePayoffPartialLaw.measurable_numericalValue D P t ht hdR H hBH
    πL π upperBid hupperBid hfloor N hrare i kind side v).comp
      (measurable_const.prodMk measurable_id)
  have hb (x) : ‖f x‖≤|v|+D.V :=
    OrderedNativePayoffPartialLaw.numericalValue_bound D P t ht hdR H hBH πL π upperBid hupperBid
      hfloor N hrare i kind side v price x
  rw [integral_prod _ (integrable_bounded ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))) f hf _ hb)]
  apply integral_congr_ae
  refine ae_of_all _ fun b => ?_
  dsimp only
  rw [integral_prod _ (integrable_bounded ((volume : Measure unitInterval).prod (rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))
    (fun x => f (b,x)) (hf.comp (measurable_const.prodMk measurable_id)) _ (fun x => hb (b,x)))]
  apply integral_congr_ae
  refine ae_of_all _ fun pub => ?_
  change (∫ payload,OrderedNativePayoffPartialLaw.numericalValue D P t ht hdR H hBH πL π upperBid
    hupperBid hfloor N hrare i kind side v price (b,(pub,payload)) ∂(rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))=_
  simp_rw [numericalValue_inserted D P t ht hdR H hBH πL π upperBid hupperBid hfloor
    N hrare i kind side v price b pub]
  simpa only [focalIndex_eq_cast] using!
    payload_integral (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (OrderedNativePayoffPartialTerminal.physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) side (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (post_card (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v price b pub

theorem numerical_integral_eq (v : ℝ) (price : Icc D.R D.Up) :
    (∫ a : unitInterval,∫ x,
      OrderedNativePayoffPartialLaw.numericalValue D P t ht hdR H hBH πL π upperBid hupperBid
        hfloor N hrare i kind side v (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a) x ∂((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))))=
      ∫ base : Fin (commonSize i kind)→ Icc (1:ℝ) D.U,
        OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht) (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side).val (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side).val (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) ((v,price,(NativePartialC1Integral.partialBidLaw D P t ht π)),base) ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonBaseLaw D P t ht π))) := by
  let Raw := Row (ownH (post0 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (post1 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H
  let Common := Fin (commonSize i kind)→ Icc (1:ℝ) (regions D P hdR H hBH).U
  let f : unitInterval×(Common×(unitInterval×Raw))→ℝ := fun x =>
    ∫ u : unitInterval,noisyValue (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (OrderedNativePayoffPartialTerminal.physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) D.heps.le rfl (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v price
      x.2.1 x.2.2.2 x.1 x.2.2.1 u
  have hf : Measurable f := measurable_integral volume _
    ((measurable_noisyValue (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (OrderedNativePayoffPartialTerminal.physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) D.heps.le rfl (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v price).comp
      (by fun_prop : Measurable (fun x : (unitInterval×(Common×(unitInterval×Raw)))×unitInterval =>
        (x.1.2.1,(x.1.2.2.2,(x.1.1,(x.1.2.2.1,x.2)))))))
  have hb (x) : ‖f x‖≤|v|+D.V := integral_bound volume _ _ (fun u =>
    noisyValue_bound (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (OrderedNativePayoffPartialTerminal.physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) D.heps.le rfl (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v price _ _ _ _ _)
  let g : Common×Raw→ℝ := fun x => ∫ a : unitInterval,∫ pub : unitInterval,
    f (a,(x.1,(pub,x.2)))
  have hg : Measurable g := measurable_integral volume _
    (measurable_integral volume _ (hf.comp
      (by fun_prop : Measurable (fun x : ((Common×Raw)×unitInterval)×unitInterval =>
        (x.1.2,(x.1.1.1,(x.2,x.1.1.2)))))))
  have hgb (x) : ‖g x‖≤|v|+D.V := integral_bound volume _ _ (fun a =>
    integral_bound volume _ _ (fun pub => hb (a,(x.1,(pub,x.2)))))
  let h : Common→ℝ := fun b => ∫ row,g (b,row) ∂(ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH (post0 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (post1 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) side).val (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)))
  have hh : Measurable h := measurable_integral (ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH (post0 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (post1 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) side).val (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))) g hg
  have hhb (b) : ‖h b‖≤|v|+D.V := integral_bound (ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH (post0 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (post1 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) side).val (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))) _ _ (fun row => hgb (b,row))
  have hp : MeasurePreserving
      (OriginalNoiseProduct.physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (commonSize i kind))
      ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonBaseLaw D P t ht π))).prod (Measure.pi (fun _ : Fin (commonSize i kind) => (volume : Measure unitInterval)))) (Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))) := by
    have he : OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π=
        noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le (commonBaseLaw D P t ht π) :=
      NoisyCommonRowLaw.original_common_noisy_law D P t ht π
    rw [he]
    exact OriginalNoiseProduct.physicalRow_preserves (by norm_num : (0:ℝ)<1) D.heps.le
      (commonSize i kind) (commonBaseLaw D P t ht π)

  have hcomp : Integrable
      (h ∘ OriginalNoiseProduct.physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (commonSize i kind)) ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonBaseLaw D P t ht π))).prod (Measure.pi (fun _ : Fin (commonSize i kind) => (volume : Measure unitInterval)))) :=
    integrable_bounded _ _ (hh.comp hp.measurable) _ (fun x => hhb _)
  calc
    _=∫ a : unitInterval,∫ b,∫ pub : unitInterval,∫ row,f (a,(b,(pub,row)))
        ∂(ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH (post0 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (post1 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) side).val (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))) ∂(volume : Measure unitInterval) ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))) ∂(volume : Measure unitInterval) := by
      apply integral_congr_ae
      refine ae_of_all _ fun a => ?_
      exact numerical_payload_integral D P t ht hdR H hBH πL π upperBid hupperBid hfloor
        N hrare i kind side v (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price a)
    _=∫ b,∫ row,∫ a : unitInterval,∫ pub : unitInterval,f (a,(b,(pub,row)))
        ∂(volume : Measure unitInterval) ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH (post0 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (post1 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) side).val (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))) ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))) :=
      transpose_four volume (Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))) volume (ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH (post0 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (post1 (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) side).val (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))) f hf (|v|+D.V) hb
    _=∫ b,h b ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))) := rfl
    _=∫ x,h (OriginalNoiseProduct.physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (commonSize i kind) x)
        ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonBaseLaw D P t ht π))).prod (Measure.pi (fun _ : Fin (commonSize i kind) => (volume : Measure unitInterval))) := (hp.integral_comp_ae_real hh.aestronglyMeasurable).symm
    _=∫ base,∫ commonNoise,h
        (OriginalNoiseProduct.physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (commonSize i kind)
          (base,commonNoise)) ∂(Measure.pi (fun _ : Fin (commonSize i kind) => (volume : Measure unitInterval))) ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonBaseLaw D P t ht π))) := integral_prod _ hcomp
    _=∫ base,OrderedNativePayoffPartialIntegral.originalIntegral D P t ht hdR H hBH πL π upperBid
        hupperBid hfloor N hrare (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (OrderedNativePayoffPartialTerminal.physical side) (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v price base ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonBaseLaw D P t ht π))) := rfl
    _=_ := integral_congr_ae (ae_of_all _ fun base =>
      OrderedNativePayoffPartialIntegral.originalIntegral_eq D P t ht hdR H hBH πL π upperBid hupperBid
        hfloor N hrare (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (OrderedNativePayoffPartialTerminal.physical side) (OrderedNativePayoffPartialLaw.lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v price base)

end FCAppendix.Affine.Tail04.OrderedNativePayoffPartialNumerical
