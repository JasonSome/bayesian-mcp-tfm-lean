import FCAppendix.Affine.Tail04.OrderedNativeUnusedExperiment
import FCAppendix.Affine.Tail04.OrderedZeroActiveFiberLaw
import FCAppendix.Affine.Tail04.RealIntegralTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroUnusedFiberLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeCategories
open NativeLocalPolicy NativeDeletedCounts OrderedZeroNativeBindings NativeActiveFiberCoordinates
open NativeHighExperiment PrivateRowSorting EqualPrivateUpper OriginalFiniteFibers
open PartialNativeCoordinates CompactSourceBidLaws MenuError

private lemma castMarketRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((n+1:ℝ)*p)≤q) : x+y*((((n+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

variable (i : Fin (N+1)) (kind : Fin N→ Fin 4)

def badPublic : Set ((Fin (commonSize i kind)→ Icc (1:ℝ) (regions D P hdR H hUH).U)×(unitInterval×RawPayload (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)))) := {x | ¬OrderedNativeUnusedExperiment.Good (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) x.1 x.2.1}

lemma measurableSet_badPublic : MeasurableSet
    (badPublic D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind) :=
  (OrderedNativeUnusedExperiment.measurableSet_good (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor)).compl.preimage
    (measurable_fst.prodMk measurable_snd.fst)

def referenceCount (b : ℝ) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)))))
    (fun x : ((Fin (commonSize i kind)→ Icc (1:ℝ) (regions D P hdR H hUH).U)×(unitInterval×RawPayload (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)))) => OrderedNativeUnusedExperiment.outcome (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) x.1 b x.2)
    (OrderedNativeUnusedExperiment.measurable_outcome_joint (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) b)

variable (n : ℕ) (el : Fin (n+1)≃{r : Fin N // kind r=0})

theorem original_integrand_error (b : ℝ) (hb0 : 0≤ b)
    (hb : (regions D P hdR H hUH).localTag (some b)=1) (hbo : b∉Icc (1:ℝ) (regions D P hdR H hUH).U) (f : Fin 3→ℝ) :
    ∀ᵐ w ∂(fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind),
      |f (deletedCount (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) (castMarketRare hrare)) i (RawRoutes.action b hb0 2) w)-
        f (OrderedNativeUnusedExperiment.outcome (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w).1 b ((OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w).2)|≤
          2*MenuError.oscillation f*(if (OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w∈badPublic D P t ht hdR H hUH πL π upperBid hupperBid
            hfloor N hrare i kind then 1 else 0) := by
  filter_upwards [fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind]
    with w hw
  let ω:=restoreSample i w
  have hr:=restored_source_rivals D P t hdR H hUH N i w
    (fun r => (hw r).1)
  have hk:=restored_kind D P hdR H hUH N i w kind
    (fun r => (hw r).2)
  have hm (r : Fin N) : NativeMenuReports.MenuAction (regions D P hdR H hUH) (ω.1.1 (i.succAbove r)).1.2 :=
    NativeMenuReports.source_menu (regions D P hdR H hUH) P t _ (hr _ (Fin.succAbove_ne i r))
  let e : Fin (n+1)≃{r : Fin N // rivalKinds (regions D P hdR H hUH) i ω.1 r=0} :=
    el.trans (Equiv.subtypeEquivRight (fun r => by rw [hk]))
  have hseed (j : Fin 2) : seedOnList ((LowBody.realLowBidLaw πL.1 : Measure ℝ)) ((regions D P hdR H hUH).roleList 0 (presentList ω.1 i b j))=
      some (conditionalMinimumSeed (nativeLowBidLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) (castMarketRare hrare)) (regions D P hdR H hUH)) n (fun q => nativeBid (w.1.1 (el q)))) := by
    have hs:=NativeUnusedCoordinates.raw_low_seed_enumeration (regions D P hdR H hUH) i ω.1 hm b hb j ((LowBody.realLowBidLaw πL.1 : Measure ℝ)) n e
    rw [source_lowBidLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)]
    simpa only [e,Equiv.trans_apply,Equiv.subtypeEquivRight_apply,ω,restoreSample,
      restoreUsers_succAbove,nativeBid] using! hs
  change |f (focalCount (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) (castMarketRare hrare)) i _ ω)-_|≤_
  rw [sourceGame_focalCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)]
  have hh:=OrderedNativeUnusedExperiment.original_count_error (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((LowBody.realLowBidLaw πL.1 : Measure ℝ))
    (localData_publicChoice D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare))
    (coreGame D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) rfl i kind ω hm hk b hb0 hb hbo _ hseed f
  simp only [OrderedZeroActiveFiberLaw.seeded,OrderedZeroActiveFiberLaw.numerical,ω,
    restoreSample,restoreUsers_succAbove,badPublic,Set.mem_setOf_eq] at hh ⊢
  have indicatorFlip (x C : ℝ) (p : Prop) [Decidable p] (d : Decidable (¬p)) :
      x≤C*(if p then (0:ℝ) else 1) → x≤C*(@ite ℝ (¬p) d 1 0) := by
    by_cases h : p <;> simp only [h,not_true_eq_false,not_false_eq_true,ite_true,ite_false,imp_self]
  exact indicatorFlip _ _ _ (Classical.propDecidable _) hh

include n el in
theorem original_fiber_count_error (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) (b : ℝ) (hb0 : 0≤ b)
    (hb : (regions D P hdR H hUH).localTag (some b)=1) (hbo : b∉Icc (1:ℝ) (regions D P hdR H hUH).U) (f : Fin 3→ℝ) :
    |(fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind i
        (RawRoutes.action b hb0 2)).expect f-
      (referenceCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b).expect f|≤
        2*MenuError.oscillation f*((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3))))).real
          (badPublic D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind) := by
  let Y : ((Fin (commonSize i kind)→ Icc (1:ℝ) (regions D P hdR H hUH).U)×(unitInterval×RawPayload (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3))))→ Fin 3:=fun x => OrderedNativeUnusedExperiment.outcome (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) x.1 b x.2
  have hY : Measurable Y:=OrderedNativeUnusedExperiment.measurable_outcome_joint (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) b
  have hT:=OrderedZeroActiveFiberLaw.seeded_preserves D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare i kind n el cats L hL
  have hXi:=CountLaw.integrable_comp (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind) (deletedCount (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) (castMarketRare hrare)) i (RawRoutes.action b hb0 2))
    (measurable_deletedCount (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) (castMarketRare hrare)) i _) f
  have hYi:=CountLaw.integrable_comp (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind) (Y ∘ (OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el)) (hY.comp hT.measurable) f
  let B:=badPublic D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind
  have hB:=measurableSet_badPublic D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind
  have hBi : Integrable (fun w => if (OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w∈B then (1:ℝ) else 0) (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind) :=
    Integrable.of_bound (Measurable.ite (hB.preimage hT.measurable)
      measurable_const measurable_const).aestronglyMeasurable 1
      (ae_of_all _ fun w => by split_ifs <;> norm_num)
  have hmap : ∫ w,f (Y ((OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w)) ∂(fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind)=∫ x,f (Y x) ∂((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3))))) :=
    hT.integral_comp_ae_real ((measurable_of_countable f).comp hY).aestronglyMeasurable
  have hBmap : (∫ w,if (OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w∈B then (1:ℝ) else 0 ∂(fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind))=((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3))))).real B := by
    have hp := hT.integral_comp_ae_real
      (f:=fun x => if x∈B then (1:ℝ) else 0)
      (Measurable.ite hB measurable_const measurable_const).aestronglyMeasurable
    refine hp.trans ?_
    simpa only [Set.indicator,Pi.one_apply,Set.mem_setOf_eq] using! integral_indicator_one (μ:=((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3)))))) hB
  rw [fiberCount,referenceCount,FiniteLaw.expect_ofMeasure,FiniteLaw.expect_ofMeasure]
  erw [←hmap,←integral_sub hXi hYi]
  calc
    |∫ w,f (deletedCount (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) (castMarketRare hrare)) i (RawRoutes.action b hb0 2) w)-f (Y ((OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w)) ∂(fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind)|
        ≤∫ w,|f (deletedCount (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) (castMarketRare hrare)) i (RawRoutes.action b hb0 2) w)-f (Y ((OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w))| ∂(fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind) :=
      abs_integral_le_integral_abs
    _≤∫ w,2*MenuError.oscillation f*(if (OrderedZeroActiveFiberLaw.seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) w∈B then (1:ℝ) else 0) ∂(fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind) :=
      integral_mono_ae (hXi.sub hYi).abs (hBi.const_mul _)
        (original_integrand_error D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
          i kind n el b hb0 hb hbo f)
    _=2*MenuError.oscillation f*((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)) (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)).finiteCount (rivalSet i kind 3))))).real B := by rw [integral_const_mul,hBmap]

end FCAppendix.Affine.Tail04.OrderedZeroUnusedFiberLaw
