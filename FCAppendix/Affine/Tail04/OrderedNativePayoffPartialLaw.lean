import FCAppendix.Affine.Tail04.OrderedNativePayoffActiveLaw
import FCAppendix.Affine.Tail04.PartialScalarIntegration
import FCAppendix.Affine.Tail04.OrderedNativePayoffPartialTerminal
import FCAppendix.Affine.Tail04.RealIntegralTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffPartialLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource OrderedNoisyNativeCategories NativeDeletedCounts
open OrderedNativePayoffBindings NativeLocalPolicy NativeActiveFiberCoordinates OrderedNativePayoffActiveLaw
open NativePartialExperiment NativePartialTerminal NativeFiberEnumerations PartialNativeCoordinates
open OrderedNativePayoffPartialExperiment OrderedNativePayoffPartialTerminal
open PrivateRowSorting EqualPrivateUpper PartialScalarIntegration CompactSourceBidLaws
open OriginalFiniteFibers NativeMenuReports
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

variable (i : Fin (N+1)) (kind : Fin N → Fin 4)

def lowPresent {n : ℕ} (kind' : Fin n → Fin 4) : Bool := decide (0< (installOriginal D P t ht).count kind' 0)

abbrev Numeric := (Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U)×(unitInterval×NativeHighExperiment.RawPayload (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)))

def nativeValue (side : Bool) (v : ℝ) (b : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp) (w : DeletedSample N Seed) : ℝ :=
  (v-b)*(if OrderedNativePayoffPartialTerminal.privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i side b (restoreSample i w).1 then 1 else 0)

lemma measurable_nativeValue (side : Bool) (v : ℝ) : Measurable
    (Function.uncurry (nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i side v)) := by
  have hr : Measurable (fun x : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp×DeletedSample N Seed => (restoreSample i x.2).1) :=
    (measurable_restoreSample (Seed:=Seed) i).fst.comp measurable_snd
  have ha := (OrderedNativePayoffPartialTerminal.measurable_privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i side).comp (measurable_fst.prodMk hr)
  exact (measurable_const.sub measurable_fst.subtype_val).mul
    ((measurable_of_countable (fun a : Bool => if a then (1:ℝ) else 0)).comp ha)

lemma nativeValue_bound (side : Bool) (v : ℝ) (b : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp) (w : DeletedSample N Seed) :
    |nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i side v b w|≤|v|+(regions D P hdR H hBH).Rp :=
  indicator_surplus_bound D.hR.le v b _

def numericalValue (side : Bool) (v : ℝ) (b : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp)
    (x : Numeric D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind) : ℝ :=
  value (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor)
    (lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) v b x.1
    (focalRow (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side b x.2.2.1) x.2.1 (x.2.2.2.1 (if side then 1 else 0)).1

lemma measurable_numericalValue (side : Bool) (v : ℝ) : Measurable
    (Function.uncurry (numericalValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i kind side v)) := by
  have hr : Measurable (fun x : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp×(Numeric D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind) => focalRow (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side x.1 x.2.2.2.1) := (measurable_focalRow (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side).comp
    (measurable_fst.prodMk measurable_snd.snd.snd.fst)
  have hi := (OrderedNativePayoffPartialExperiment.measurable_inclusion (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) (ownTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side) (otherTotal (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side)
    (physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (lowPresent D P t ht kind) (focalIndex (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind side)).comp
      (measurable_snd.fst.prodMk (hr.prodMk (measurable_snd.snd.fst.prodMk
        (measurable_fst.comp ((measurable_pi_apply (if side then 1 else 0)).comp
          measurable_snd.snd.snd.snd.fst)))))
  exact (measurable_const.sub measurable_fst.subtype_val).mul hi

lemma numericalValue_bound (side : Bool) (v : ℝ) (b : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp)
    (x : Numeric D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind) :
    |numericalValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind side v b x|
      ≤|v|+(regions D P hdR H hBH).Rp := OrderedNativePayoffPartialExperiment.value_bound (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (commonSize i kind) _ _ (physical side) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) _ _ v b _ _ _ _

def rawSeed (w : DeletedSample N Seed) : Option unitInterval :=
  seedOnList (LowBody.realLowBidLaw πL.1 : Measure ℝ) ((regions D P hdR H hBH).roleList 0 (presentList (restoreSample i w).1 i (floorPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)) 0))

lemma measurable_rawSeed : Measurable
    (rawSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i) := by
  exact (Hybrid.measurable_seedOnList (LowBody.realLowBidLaw πL.1 : Measure ℝ)).comp (((regions D P hdR H hBH).measurable_roleList 0).comp
    ((measurable_presentList i (regions D P hdR H hBH).R 0).comp (measurable_restoreSample (Seed:=Seed) i).fst))

def allSeed (x : unitInterval×DeletedSample N Seed) :
    Numeric D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind :=
  let y := numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x.2
  (y.1,((rawSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i x.2).getD x.1,y.2))

lemma measurable_allSeed : Measurable
    (allSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind) := by
  have hy : Measurable (fun x : unitInterval×DeletedSample N Seed => numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x.2) := (measurable_numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
    i kind).comp measurable_snd
  have hu : Measurable (fun x : unitInterval×DeletedSample N Seed => rawSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i x.2) := (measurable_rawSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i).comp
    measurable_snd
  exact hy.fst.prodMk
    ((measurable_option_default.comp (hu.prodMk measurable_fst)).prodMk hy.snd)

lemma rawSeed_independent_price (w : DeletedSample N Seed)
    (hw : ∀ r,sourceBands P (regions D P hdR H hBH) t (w.1.1 r).1 ∧ (regions D P hdR H hBH).coarseTag (w.1.1 r)=kind r)
    (b : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp) (j : Fin 2) :
    seedOnList (LowBody.realLowBidLaw πL.1 : Measure ℝ) ((regions D P hdR H hBH).roleList 0 (presentList (restoreSample i w).1 i b j))=
      rawSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i w := by
  let ω := (restoreSample i w).1
  have hr := restored_source_rivals D P t hdR H hBH N
    i w (fun r => (hw r).1)
  have hm (r : Fin N) : MenuAction (regions D P hdR H hBH) (ω.1 (i.succAbove r)).1.2 :=
    source_menu (regions D P hdR H hBH) P t _ (hr _ (Fin.succAbove_ne i r))
  congr 1
  exact (low_list_rivalSet (regions D P hdR H hBH) i ω hm b j).trans
    (low_list_rivalSet (regions D P hdR H hBH) i ω hm (floorPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)) 0).symm

lemma rawSeed_low (n : ℕ) (el : Fin (n+1) ≃ {r : Fin N // kind r=0}) :
    ∀ᵐ w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),rawSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i w=
      some (conditionalMinimumSeed (nativeLowBidLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) (regions D P hdR H hBH)) n
        (fun j => nativeBid (w.1.1 (el j)))) := by
  filter_upwards [fiber_support D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind] with w hw
  let ω := (restoreSample i w).1
  have hr := restored_source_rivals D P t hdR H hBH N
    i w (fun r => (hw r).1)
  have hk := restored_kind D P hdR H hBH N
    i w kind (fun r => (hw r).2)
  have hm (r : Fin N) : MenuAction (regions D P hdR H hBH) (ω.1 (i.succAbove r)).1.2 :=
    source_menu (regions D P hdR H hBH) P t _ (hr _ (Fin.succAbove_ne i r))
  let e : Fin (n+1) ≃ {r : Fin N // rivalKinds (regions D P hdR H hBH) i ω r=0} :=
    el.trans (Equiv.subtypeEquivRight (fun r => by rw [hk]))
  have hs := low_seed_enumeration (regions D P hdR H hBH) i ω hm (floorPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)) 0 (LowBody.realLowBidLaw πL.1 : Measure ℝ) n e
  rw [source_lowBidLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  simpa only [rawSeed,ω,e,Equiv.trans_apply,Equiv.subtypeEquivRight_apply,restoreSample,
    restoreUsers_succAbove,nativeBid] using! hs

lemma rawSeed_noLow (h : (installOriginal D P t ht).count kind 0=0) :
    ∀ᵐ w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),rawSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i w=none := by
  filter_upwards [fiber_support D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind] with w hw
  let ω := (restoreSample i w).1
  have hr := restored_source_rivals D P t hdR H hBH N
    i w (fun r => (hw r).1)
  have hk := restored_kind D P hdR H hBH N
    i w kind (fun r => (hw r).2)
  have hm (r : Fin N) : MenuAction (regions D P hdR H hBH) (ω.1 (i.succAbove r)).1.2 :=
    source_menu (regions D P hdR H hBH) P t _ (hr _ (Fin.succAbove_ne i r))
  apply no_low_seed (regions D P hdR H hBH) i ω hm (floorPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)) 0 (LowBody.realLowBidLaw πL.1 : Measure ℝ)
  intro r hr0
  have he : Finset.univ.filter (fun r : Fin N => kind r=0)=∅ :=
    Finset.card_eq_zero.mp h
  have hm' : r∈Finset.univ.filter (fun r : Fin N => kind r=0) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r,by simpa only [ω,hk] using hr0⟩
  rw [he] at hm'
  exact Finset.notMem_empty _ hm'

theorem allSeed_preserves (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) : MeasurePreserving
    (allSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind)
    ((volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)) ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))) := by
  refine ⟨measurable_allSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind,?_⟩
  by_cases hl : 0< (installOriginal D P t ht).count kind 0
  · have hc : 0< Fintype.card {r : Fin N // kind r=0} := by
      simpa only [FiniteTailNoisyGame.Data.count,Fintype.card_subtype] using hl
    let n := Fintype.card {r : Fin N // kind r=0}-1
    have hn : n+1=Fintype.card {r : Fin N // kind r=0} := Nat.sub_add_cancel hc
    let el : Fin (n+1) ≃ {r : Fin N // kind r=0} :=
      (castEquiv hn).trans (Fintype.equivFin _).symm
    let f := seeded D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el
    have hp := (seeded_preserves D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i kind n el cats L hL).comp (measurePreserving_snd (μ:=(volume : Measure unitInterval)) (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)))
    rw [←hp.map_eq]
    apply Measure.map_congr
    filter_upwards [(measurePreserving_snd (μ:=(volume : Measure unitInterval)) (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))).quasiMeasurePreserving.ae
      (rawSeed_low D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el)] with x hx
    simp only [allSeed,hx,Option.getD_some,Function.comp_apply,seeded]
  · let T : unitInterval×DeletedSample N Seed →
        Numeric D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind := fun x =>
      ((numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x.2).1,
        (x.1,(numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x.2).2))
    have hp : MeasurePreserving T ((volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)) ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))) :=
      (measurePreserving_prodAssoc (Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))) (volume : Measure unitInterval) (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)))).comp
        (((Measure.measurePreserving_swap (μ:=(volume : Measure unitInterval)) (ν:=(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))))).prod
          (MeasurePreserving.id (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))).comp
          ((measurePreserving_prodAssoc (volume : Measure unitInterval) (Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))) (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)))).symm.comp
            ((MeasurePreserving.id (volume : Measure unitInterval)).prod
              (numerical_preserves D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind))))
    rw [←hp.map_eq]
    apply Measure.map_congr
    filter_upwards [(measurePreserving_snd (μ:=(volume : Measure unitInterval)) (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))).quasiMeasurePreserving.ae
      (rawSeed_noLow D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind
        (Nat.eq_zero_of_not_pos hl))] with x hx
    simp only [allSeed,hx,Option.getD_none,T]

lemma allSeed_shape : ∀ᵐ x ∂(volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),
    ∀ b : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp,∀ j : Fin 2,
      seedOnList (LowBody.realLowBidLaw πL.1 : Measure ℝ) ((regions D P hdR H hBH).roleList 0 (presentList (restoreSample i x.2).1 i b j))=
        if lowPresent D P t ht kind then
          some (allSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x).2.1
        else none := by
  by_cases hl : 0< (installOriginal D P t ht).count kind 0
  · have hc : 0< Fintype.card {r : Fin N // kind r=0} := by
      simpa only [FiniteTailNoisyGame.Data.count,Fintype.card_subtype] using hl
    let n := Fintype.card {r : Fin N // kind r=0}-1
    let el : Fin (n+1) ≃ {r : Fin N // kind r=0} :=
      (castEquiv (Nat.sub_add_cancel hc)).trans (Fintype.equivFin _).symm
    have lift := (measurePreserving_snd (μ:=(volume : Measure unitInterval)) (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))).quasiMeasurePreserving
    filter_upwards [lift.ae (fiber_support D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),
      lift.ae (rawSeed_low D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el)] with x hw hs
    intro b j
    rw [rawSeed_independent_price D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i kind x.2 hw b j]
    simp only [lowPresent,decide_eq_true hl,ite_true,allSeed,hs,Option.getD_some]
  · have lift := (measurePreserving_snd (μ:=(volume : Measure unitInterval)) (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))).quasiMeasurePreserving
    filter_upwards [lift.ae (fiber_support D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),
      lift.ae (rawSeed_noLow D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind
          (Nat.eq_zero_of_not_pos hl))] with x hw hs
    intro b j
    rw [rawSeed_independent_price D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i kind x.2 hw b j]
    simp only [lowPresent,decide_eq_false hl,Bool.false_eq_true,ite_false,hs]

theorem native_numerical_ownNoise (side : Bool) (v : ℝ) (b : Icc D.R D.Up) :
    ∀ᵐ x ∂(volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),∀ᵐ a : unitInterval ∂volume,
      nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i side v
        (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a) x.2=
      numericalValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind side v
        (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a)
        (allSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x) := by
  have hs := (measurePreserving_snd (μ:=(volume : Measure unitInterval)) (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))).quasiMeasurePreserving.ae
    (fiber_support D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)
  filter_upwards [hs,allSeed_shape D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
    i kind] with x hx hseed
  let ω := (restoreSample i x.2).1
  have hr := restored_source_rivals D P t hdR H hBH N
    i x.2 (fun r => (hx r).1)
  have hm (r : Fin N) : MenuAction (regions D P hdR H hBH) (ω.1 (i.succAbove r)).1.2 :=
    source_menu (regions D P hdR H hBH) P t _ (hr _ (Fin.succAbove_ne i r))
  have hk := restored_kind D P hdR H hBH N
    i x.2 kind (fun r => (hx r).2)
  have hh := OrderedNativePayoffPartialTerminal.private_value_ae (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i kind (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) ((LowBody.realLowBidLaw πL.1 : Measure ℝ))
    (localData_publicChoice D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
    ω hm hk D.heps rfl D.hgap side (lowPresent D P t ht kind)
    (allSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x).2.1
    hseed v b
  exact hh.mono fun a ha => by
    dsimp only [OrderedNativePayoffPartialExperiment.noisyValue] at ha
    erw [focalRow_update] at ha
    simpa only [nativeValue,numericalValue,OrderedNativePayoffPartialExperiment.noisyValue,
      allSeed,numerical,ω,restoreSample,restoreUsers_succAbove,
      NativePartialTerminal.privateSeed,noisyPrice] using! ha

theorem original_side_integral (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) (side : Bool) (v : ℝ) (b : Icc D.R D.Up) :
    (∫ a : unitInterval,∫ w,
      nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i side v
        (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a) w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))=
    ∫ a : unitInterval,∫ x,
      numericalValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind side v
        (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a) x ∂((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))) := by
  let S := (volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)
  let f : unitInterval×(unitInterval×DeletedSample N Seed) → ℝ := fun y =>
    nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i side v
      (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b y.1) y.2.2
  let g : unitInterval×Numeric D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind → ℝ :=
    fun y => numericalValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind side v
      (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b y.1) y.2
  have hf : Measurable f := (measurable_nativeValue D P t ht hdR H hBH πL π upperBid hupperBid
    hfloor N hrare i side v).comp
      (((measurable_noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b).comp measurable_fst).prodMk measurable_snd.snd)
  have hg : Measurable g := (measurable_numericalValue D P t ht hdR H hBH πL π upperBid
    hupperBid hfloor N hrare i kind side v).comp
      (((measurable_noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b).comp measurable_fst).prodMk measurable_snd)
  have hfb (y) : ‖f y‖≤|v|+(regions D P hdR H hBH).Rp := by
    exact nativeValue_bound D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i side v _ _
  have hgb (y) : ‖g y‖≤|v|+(regions D P hdR H hBH).Rp := by
    exact numericalValue_bound D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind side v _ _
  let T := allSeed D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind
  have hT := allSeed_preserves D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind cats L hL
  calc
    _=∫ a : unitInterval,∫ x,f (a,x) ∂S := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => by
        exact (measurePreserving_snd (μ:=(volume : Measure unitInterval)) (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))).integral_comp_ae_real
          ((measurable_nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
            i side v).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable |>.symm
    _=∫ x,∫ a : unitInterval,f (a,x) ∂(volume : Measure unitInterval) ∂S :=
      integral_swap_bounded _ _ f hf _ hfb
    _=∫ x,∫ a : unitInterval,g (a,T x) ∂(volume : Measure unitInterval) ∂S := by
      apply integral_congr_ae
      exact (native_numerical_ownNoise D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
        i kind side v b).mono (fun x hx => integral_congr_ae hx)
    _=∫ x,∫ a : unitInterval,g (a,x) ∂(volume : Measure unitInterval) ∂((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))) := hT.integral_comp_ae_real
      (hg.comp measurable_swap).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    _=_ := (integral_swap_bounded _ _ g hg _ hgb).symm

attribute [local irreducible] OrderedNativePayoffPartialTerminal.privateAccept NativeDeletedCounts.restoreUsers

theorem fiber_payoff_halves (v : ℝ) (b : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp) :
    affineCountUtility
      (fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i
        (RawRoutes.action b (D.hR.le.trans b.2.1) 1)) v b D.eta D.heta0 D.heta1=
      (1/2:ℝ)*(∫ w,nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
        i false v b w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))+
      (1/2:ℝ)*(∫ w,nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
        i true v b w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)) := by
  let β : Measure ((Fin N → UserDraw 2)×(Fin 2→ Seed)) :=
    (Measure.pi (fun r => cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind r}))).prod
      (Measure.pi (fun _ : Fin 2 => (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)).seedLaw))
  haveI : IsProbabilityMeasure β := by
    constructor
    have he := measure_univ (μ:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))
    change (β.prod (permLaw 2)) Set.univ=1 at he
    simpa only [←Set.univ_prod_univ,Measure.prod_prod,measure_univ,mul_one] using he
  let restore : ((Fin N→ UserDraw 2)×(Fin 2→ Seed)) → Background (N+1) 2 Seed :=
    fun y => (restoreUsers i y.1,y.2)
  have hr : Measurable restore := ((measurable_restoreUsers i).comp measurable_fst).prodMk measurable_snd
  let aa : ((Fin N→ UserDraw 2)×(Fin 2→ Seed)) → Bool×Bool := fun y =>
    (OrderedNativePayoffPartialTerminal.privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i false b (restore y),OrderedNativePayoffPartialTerminal.privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i true b (restore y))
  have ha : Measurable aa :=
    ((OrderedNativePayoffPartialTerminal.measurable_privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i false).comp (measurable_const.prodMk hr)).prodMk
      ((OrderedNativePayoffPartialTerminal.measurable_privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i true).comp (measurable_const.prodMk hr))
  let f : Fin 3 → ℝ := fun r => userPayoff v b 0
    (Schedule.affine 2 D.eta D.heta0 D.heta1).charge (Schedule.once 2).charge r.val
  have hg : Measurable (fun w : DeletedSample N Seed => gated (aa w.1) w.2) := by
    have hgate : Measurable (fun x : (Bool×Bool)×Equiv.Perm (Fin 2) => gated x.1 x.2) :=
      measurable_of_countable _
    have hinput : Measurable (fun w : DeletedSample N Seed => (aa w.1,w.2)) :=
      (ha.comp measurable_fst).prodMk measurable_snd
    have hcomp := hgate.comp hinput
    exact hcomp
  have hgi : Integrable (fun w : DeletedSample N Seed => f (gated (aa w.1) w.2)) (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind) :=
    HierarchicalFiniteSampler.integrable_finite_comp (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind) _ hg f
  have hc : ∀ᵐ w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i (RawRoutes.action b (D.hR.le.trans b.2.1) 1) w=
      gated (aa w.1) w.2 := by
    filter_upwards [fiber_support D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind] with w hw
    have hrivals := restored_source_rivals D P t hdR H hBH N i w (fun r => (hw r).1)
    have hc := source_partial_count D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i b 1 (restoreSample i w) hrivals
    rw [OrderedNativePayoffBindings.privateAccept_eq D P t ht hdR H hBH πL π upperBid
        hupperBid hfloor N hrare i b _ hrivals 0,
      OrderedNativePayoffBindings.privateAccept_eq D P t ht hdR H hBH πL π upperBid
        hupperBid hfloor N hrare i b _ hrivals 1] at hc
    simpa only [OrderedNativePayoffPartialTerminal.privateAccept,physical,
      PartialScalarIntegration.gated,aa,restore,restoreSample,deletedCount,Bool.false_eq_true,ite_false,ite_true] using! hc
  have hi (side : Bool) : Integrable
      (fun y => (v-b)*(if OrderedNativePayoffPartialTerminal.privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i side b (restore y) then (1:ℝ) else 0)) β := by
    apply Integrable.of_bound
      ((measurable_const.mul ((measurable_of_countable (fun a : Bool => if a then (1:ℝ) else 0)).comp
        ((OrderedNativePayoffPartialTerminal.measurable_privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i side).comp (measurable_const.prodMk hr)))).aestronglyMeasurable)
      (|v|+(regions D P hdR H hBH).Rp)
    exact ae_of_all _ fun y => indicator_surplus_bound D.hR.le v b _
  have hprojection (side : Bool) :
      (∫ w,nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
        i side v b w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))=
      ∫ y,(v-b)*(if OrderedNativePayoffPartialTerminal.privateAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i side b (restore y) then (1:ℝ) else 0) ∂β := by
    exact (measurePreserving_fst (μ:=β) (ν:=permLaw 2)).integral_comp_ae_real (hi side).aestronglyMeasurable
  rw [affineCountUtility,CountLaw.utility,fiberCount,FiniteLaw.expect_ofMeasure]
  change (∫ w,f (deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i (RawRoutes.action b (D.hR.le.trans b.2.1) 1) w) ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))=_
  erw [integral_congr_ae (hc.mono fun _ h => congrArg f h),integral_prod _ hgi]
  dsimp only [f]
  simp_rw [fair_route_payoff D.eta D.heta0 D.heta1 v (b:ℝ)]
  rw [integral_add ((hi false).const_mul (1/2:ℝ)) ((hi true).const_mul (1/2:ℝ)),
    hprojection false,hprojection true]
  simp only [integral_const_mul]

theorem original_partial_numeric (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) (v : ℝ) (b : Icc D.R D.Up) :
    (∫ a : unitInterval,affineCountUtility
      (fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i
        (RawRoutes.action (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a)
          (D.hR.le.trans (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a).2.1) 1))
        v (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a) D.eta D.heta0 D.heta1)=
      (1/2:ℝ)*(∫ a : unitInterval,∫ x,
        numericalValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind false v
          (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a) x ∂((Measure.pi (fun _ : Fin (commonSize i kind) => ((OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π) : Measure _))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))))+
      (1/2:ℝ)*(∫ a : unitInterval,∫ x,
        numericalValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind true v
          (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a) x ∂((Measure.pi (fun _ : Fin (commonSize i kind) => ((OrderedNativePayoffActiveLaw.commonLaw D P t ht hdR H hBH π) : Measure _))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (OrderedNativePayoffActiveLaw.privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)))))) := by
  have hi (side : Bool) : Integrable (fun a : unitInterval =>
      ∫ w,nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i side v
        (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b a) w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)) volume := by
    have hm := (measurable_nativeValue D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i side v).comp (((measurable_noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl b).comp measurable_fst).prodMk measurable_snd)
    exact (Integrable.of_bound hm.aestronglyMeasurable (|v|+(regions D P hdR H hBH).Rp)
      (ae_of_all _ fun x => nativeValue_bound D P t ht hdR H hBH πL π upperBid hupperBid hfloor
        N hrare i side v _ _) : Integrable _ ((volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))).integral_prod_left
  simp_rw [fiber_payoff_halves D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind]
  rw [integral_add ((hi false).const_mul (1/2:ℝ)) ((hi true).const_mul (1/2:ℝ)),
    integral_const_mul,integral_const_mul,
    original_side_integral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i kind cats L hL false v b,
    original_side_integral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i kind cats L hL true v b]

end FCAppendix.Affine.Tail04.OrderedNativePayoffPartialLaw
