import FCAppendix.Affine.Tail04.OrderedZeroPartialTerminal
import FCAppendix.Affine.Tail04.OrderedZeroActiveFiberLaw
import FCAppendix.Affine.Tail04.PartialScalarIntegration
import FCAppendix.Affine.Tail04.RealIntegralTransport
import FCAppendix.Affine.Tail04.ZeroPrivateRegularity

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroPartialFiberLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeCategories NativeDeletedCounts
open OrderedZeroNativeBindings NativeLocalPolicy NativeActiveFiberCoordinates OrderedZeroActiveFiberLaw
open NativePartialExperiment NativePartialTerminal NativeFiberEnumerations PartialNativeCoordinates
open PrivateRowSorting EqualPrivateUpper PartialScalarIntegration CompactSourceBidLaws
open OrderedNativePayoffPartialExperiment OrderedNativePayoffPartialTerminal
open OriginalFiniteFibers NativeMenuReports NativeHighExperiment SortedAllNoise
open scoped BigOperators

attribute [local irreducible] OrderedNativePayoffPartialTerminal.privateAccept PartialScalarIntegration.gated

private lemma ae_pair {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {p : α→Prop} {q : β→Prop} (hp : ∀ᵐ a ∂μ,p a) (hq : ∀ᵐ b ∂ν,q b) :
    ∀ᵐ x ∂μ.prod ν,p x.1 ∧ q x.2 :=
  ((measurePreserving_fst («μ»:=μ) («ν»:=ν)).quasiMeasurePreserving.ae hp).and
    ((measurePreserving_snd («μ»:=μ) («ν»:=ν)).quasiMeasurePreserving.ae hq)

private lemma measurable_gated_comp {Y : Type*} [MeasurableSpace Y]
    (a : Y→Bool×Bool) (ha : Measurable a) :
    Measurable (fun x : Y×Equiv.Perm (Fin 2) => gated (a x.1) x.2) :=
  (measurable_of_countable (fun x : (Bool×Bool)×Equiv.Perm (Fin 2) => gated x.1 x.2)).comp
    ((ha.comp measurable_fst).prodMk measurable_snd)

private lemma measurable_restored_pair {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c)
    (i : Fin (N+1)) (b : Icc K.E.R K.E.Rp) : Measurable
    (fun y : (Fin N→UserDraw 2)×(Fin 2→Seed) =>
      (OrderedNativePayoffPartialTerminal.privateAccept K i false b (restoreUsers i y.1,y.2),
        OrderedNativePayoffPartialTerminal.privateAccept K i true b (restoreUsers i y.1,y.2))) := by
  have hr : Measurable (fun y : (Fin N→UserDraw 2)×(Fin 2→Seed) =>
      (restoreUsers i y.1,y.2)) :=
    ((measurable_restoreUsers i).comp measurable_fst).prodMk measurable_snd
  exact ((OrderedNativePayoffPartialTerminal.measurable_privateAccept K i false).comp
    (measurable_const.prodMk hr)).prodMk
      ((OrderedNativePayoffPartialTerminal.measurable_privateAccept K i true).comp
        (measurable_const.prodMk hr))

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "m" => N+1
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℝ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

private lemma castMarketRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((n+1:ℝ)*p)≤q) : x+y*((((n+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "G" => (LowBody.realLowBidLaw (Subtype.val πL) : Measure ℝ)
local notation "Ds" => installOriginal D P t ht
local notation "ρA" => OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π
local notation "ρP" => OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare

variable (i : Fin (N+1)) (kind : Fin N → Fin 4)
local notation "A" => commonSize i kind
local notation "H0" => NativeLocalPolicy.Data.finiteCount K (rivalSet i kind 2)
local notation "H1" => NativeLocalPolicy.Data.finiteCount K (rivalSet i kind 3)
local notation "μ" => fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind
local notation "ν" => NativeHighExperiment.rawPayloadLaw K ρP H0 H1
local notation "M" => Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure ρA)
local notation "Ξ" => Measure.prod M (Measure.prod (volume : Measure unitInterval) ν)

def lowPresent {n : ℕ} (kind' : Fin n → Fin 4) : Bool := decide (0< (Ds).count kind' 0)

abbrev Numeric := (Fin A → Icc (1:ℝ) (E).U)×(unitInterval×NativeHighExperiment.RawPayload K H0 H1)

def nativeValue (side : Bool) (v : ℝ) (b : Icc (E).R (E).Rp) (w : DeletedSample N Seed) : ℝ :=
  (v-b)*(if OrderedNativePayoffPartialTerminal.privateAccept K i side b (restoreSample i w).1 then 1 else 0)

lemma measurable_nativeValue (side : Bool) (v : ℝ) : Measurable
    (Function.uncurry (nativeValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i side v)) := by
  have hr : Measurable (fun x : Icc (E).R (E).Rp×DeletedSample N Seed => (restoreSample i x.2).1) := (measurable_restoreSample (Seed:=Seed) i).fst.comp measurable_snd
  have ha := (OrderedNativePayoffPartialTerminal.measurable_privateAccept K i side).comp (measurable_fst.prodMk hr)
  exact (measurable_const.sub measurable_fst.subtype_val).mul
    ((measurable_of_countable (fun a : Bool => if a then (1:ℝ) else 0)).comp ha)

lemma nativeValue_bound (side : Bool) (v : ℝ) (b : Icc (E).R (E).Rp) (w : DeletedSample N Seed) :
    |nativeValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i side v b w|≤|v|+(E).Rp :=
  indicator_surplus_bound D.hR.le v b _

def numericalValue (side : Bool) (v : ℝ) (b : Icc (E).R (E).Rp)
    (x : Numeric D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind) : ℝ :=
  value K A (ownTotal K i kind side) (otherTotal K i kind side) (physical side) Q
    (lowPresent D P t ht kind) (focalIndex K i kind side) v b x.1
    (focalRow K i kind side b x.2.2.1) x.2.1 (x.2.2.2.1 (if side then 1 else 0)).1

lemma measurable_numericalValue (side : Bool) (v : ℝ) : Measurable
    (Function.uncurry (numericalValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      i kind side v)) := by
  have hr : Measurable (fun x : Icc (E).R (E).Rp×Numeric D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind => focalRow K i kind side x.1 x.2.2.2.1) := (measurable_focalRow K i kind side).comp
    (measurable_fst.prodMk measurable_snd.snd.snd.fst)
  have hi := (OrderedNativePayoffPartialExperiment.measurable_inclusion K A (ownTotal K i kind side) (otherTotal K i kind side)
    (physical side) Q (lowPresent D P t ht kind) (focalIndex K i kind side)).comp
      (measurable_snd.fst.prodMk (hr.prodMk (measurable_snd.snd.fst.prodMk
        (measurable_fst.comp ((measurable_pi_apply (if side then 1 else 0)).comp
          measurable_snd.snd.snd.snd.fst)))))
  exact (measurable_const.sub measurable_fst.subtype_val).mul hi

lemma numericalValue_bound (side : Bool) (v : ℝ) (b : Icc (E).R (E).Rp)
    (x : Numeric D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind) :
    |numericalValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind side v b x|
      ≤|v|+(E).Rp := OrderedNativePayoffPartialExperiment.value_bound K A _ _ (physical side) Q _ _ v b _ _ _ _

def rawSeed (w : DeletedSample N Seed) : Option unitInterval :=
  seedOnList G ((E).roleList 0 (presentList (restoreSample i w).1 i (floorPrice K) 0))

lemma measurable_rawSeed : Measurable
    (rawSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i) := by
  exact (Hybrid.measurable_seedOnList G).comp (((E).measurable_roleList 0).comp
    ((measurable_presentList i (E).R 0).comp (measurable_restoreSample (Seed:=Seed) i).fst))

def allSeed (x : unitInterval×DeletedSample N Seed) :
    Numeric D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind :=
  let y := numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x.2
  (y.1,((rawSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i x.2).getD x.1,y.2))

lemma measurable_allSeed : Measurable
    (allSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind) := by
  have hy : Measurable (fun x : unitInterval×DeletedSample N Seed => numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x.2) := (measurable_numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
    i kind).comp measurable_snd
  have hu : Measurable (fun x : unitInterval×DeletedSample N Seed => rawSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i x.2) := (measurable_rawSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i).comp
    measurable_snd
  exact hy.fst.prodMk
    ((measurable_option_default.comp (hu.prodMk measurable_fst)).prodMk hy.snd)

lemma rawSeed_independent_price (w : DeletedSample N Seed)
    (hw : ∀ r,sourceBands P E t (w.1.1 r).1 ∧ (E).coarseTag (w.1.1 r)=kind r)
    (b : Icc (E).R (E).Rp) (j : Fin 2) :
    seedOnList G ((E).roleList 0 (presentList (restoreSample i w).1 i b j))=
      rawSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i w := by
  let ω := (restoreSample i w).1
  have hr := restored_source_rivals D P t hdR H hUH N
    i w (fun r => (hw r).1)
  have hm (r : Fin N) : NativeMenuReports.MenuAction E (ω.1 (i.succAbove r)).1.2 :=
    NativeMenuReports.source_menu E P t _ (hr _ (Fin.succAbove_ne i r))
  congr 1
  exact (low_list_rivalSet E i ω hm b j).trans
    (low_list_rivalSet E i ω hm (floorPrice K) 0).symm

lemma rawSeed_low (n : ℕ) (el : Fin (n+1) ≃ {r : Fin N // kind r=0}) :
    ∀ᵐ w ∂μ,rawSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i w=
      some (conditionalMinimumSeed (nativeLowBidLaw Γ E) n
        (fun j => nativeBid (w.1.1 (el j)))) := by
  filter_upwards [fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind] with w hw
  let ω := (restoreSample i w).1
  have hr := restored_source_rivals D P t hdR H hUH N
    i w (fun r => (hw r).1)
  have hk := restored_kind D P hdR H hUH N
    i w kind (fun r => (hw r).2)
  have hm (r : Fin N) : NativeMenuReports.MenuAction E (ω.1 (i.succAbove r)).1.2 :=
    NativeMenuReports.source_menu E P t _ (hr _ (Fin.succAbove_ne i r))
  let e : Fin (n+1) ≃ {r : Fin N // rivalKinds E i ω r=0} :=
    el.trans (Equiv.subtypeEquivRight (fun r => by rw [hk]))
  have hs := low_seed_enumeration E i ω hm (floorPrice K) 0 G n e
  rw [source_lowBidLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)]
  simpa only [rawSeed,ω,e,Equiv.trans_apply,Equiv.subtypeEquivRight_apply,restoreSample,
    restoreUsers_succAbove,nativeBid] using! hs

lemma rawSeed_noLow (h : (Ds).count kind 0=0) :
    ∀ᵐ w ∂μ,rawSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i w=none := by
  filter_upwards [fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind] with w hw
  let ω := (restoreSample i w).1
  have hr := restored_source_rivals D P t hdR H hUH N
    i w (fun r => (hw r).1)
  have hk := restored_kind D P hdR H hUH N
    i w kind (fun r => (hw r).2)
  have hm (r : Fin N) : NativeMenuReports.MenuAction E (ω.1 (i.succAbove r)).1.2 :=
    NativeMenuReports.source_menu E P t _ (hr _ (Fin.succAbove_ne i r))
  apply no_low_seed E i ω hm (floorPrice K) 0 G
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
    (allSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind)
    ((volume : Measure unitInterval).prod μ) Ξ := by
  refine ⟨measurable_allSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind,?_⟩
  by_cases hl : 0< (Ds).count kind 0
  · have hc : 0< Fintype.card {r : Fin N // kind r=0} := by
      simpa only [FiniteTailNoisyGame.Data.count,Fintype.card_subtype] using hl
    let n := Fintype.card {r : Fin N // kind r=0}-1
    have hn : n+1=Fintype.card {r : Fin N // kind r=0} := Nat.sub_add_cancel hc
    let el : Fin (n+1) ≃ {r : Fin N // kind r=0} :=
      (castEquiv hn).trans (Fintype.equivFin _).symm
    let f := seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el
    have hp := (seeded_preserves D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      i kind n el cats L hL).comp (measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ))
    rw [←hp.map_eq]
    apply Measure.map_congr
    filter_upwards [(measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ)).quasiMeasurePreserving.ae
      (rawSeed_low D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el)] with x hx
    simp only [allSeed,hx,Option.getD_some,Function.comp_apply,seeded]
  · let T : unitInterval×DeletedSample N Seed →
        Numeric D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind := fun x =>
      ((numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x.2).1,
        (x.1,(numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x.2).2))
    have hp : MeasurePreserving T ((volume : Measure unitInterval).prod μ) Ξ :=
      (measurePreserving_prodAssoc M (volume : Measure unitInterval) ν).comp
        (((Measure.measurePreserving_swap («μ»:=(volume : Measure unitInterval)) («ν»:=M)).prod
          (MeasurePreserving.id ν)).comp
          ((measurePreserving_prodAssoc (volume : Measure unitInterval) M ν).symm.comp
            ((MeasurePreserving.id (volume : Measure unitInterval)).prod
              (numerical_preserves D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind))))
    rw [←hp.map_eq]
    apply Measure.map_congr
    filter_upwards [(measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ)).quasiMeasurePreserving.ae
      (rawSeed_noLow D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind
        (Nat.eq_zero_of_not_pos hl))] with x hx
    simp only [allSeed,hx,Option.getD_none,T]

lemma allSeed_shape : ∀ᵐ x ∂(volume : Measure unitInterval).prod μ,
    ∀ b : Icc (E).R (E).Rp,∀ j : Fin 2,
      seedOnList G ((E).roleList 0 (presentList (restoreSample i x.2).1 i b j))=
        if lowPresent D P t ht kind then
          some (allSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x).2.1
        else none := by
  by_cases hl : 0< (Ds).count kind 0
  · have hc : 0< Fintype.card {r : Fin N // kind r=0} := by
      simpa only [FiniteTailNoisyGame.Data.count,Fintype.card_subtype] using hl
    let n := Fintype.card {r : Fin N // kind r=0}-1
    let el : Fin (n+1) ≃ {r : Fin N // kind r=0} :=
      (castEquiv (Nat.sub_add_cancel hc)).trans (Fintype.equivFin _).symm
    have lift := (measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ)).quasiMeasurePreserving
    filter_upwards [lift.ae (fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind),
      lift.ae (rawSeed_low D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el)] with x hw hs
    intro b j
    rw [rawSeed_independent_price D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      i kind x.2 hw b j]
    simp only [lowPresent,decide_eq_true hl,ite_true,allSeed,hs,Option.getD_some]
  · have lift := (measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ)).quasiMeasurePreserving
    filter_upwards [lift.ae (fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind),
      lift.ae (rawSeed_noLow D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind
        (Nat.eq_zero_of_not_pos hl))] with x hw hs
    intro b j
    rw [rawSeed_independent_price D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      i kind x.2 hw b j]
    simp only [lowPresent,decide_eq_false hl,Bool.false_eq_true,ite_false,hs]

section Atomless
variable [hA : NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (Subtype.val (OrderedNativeZeroNoiseSource.active D P t ht π))))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (Subtype.val (π 2))).map (fun x=>(x.2:ℝ)))]

include P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind in
theorem numerical_regular (side : Bool) (price : Icc D.R D.Up) :
    ∀ᵐ x ∂Ξ,
      (∀ h : Fin (N+2),∀ q,EqualReceiptLaw.receipt (c:=D.c) (ξ:=D.ξ)
        ((K).signalLaw h) (sortedBox x.1) q≠(price:ℝ)) ∧
      (∀ l,l≠focalIndex K i kind side→
        numericalEntry (focalRow K i kind side price x.2.2.1 l)≠(price:ℝ)) := by
  letI : NullSingletonClass (bidMarginal (Subtype.val (NativeZeroNoiseSource.active D P t ht π)) : Measure (Icc (1:ℝ) D.U)) := hA
  have hc : ∀ᵐcommon ∂M,∀h : Fin (N+2),∀q,
      EqualReceiptLaw.receipt (c:=D.c) (ξ:=D.ξ) ((K).signalLaw h)
        (sortedBox common) q≠(price:ℝ) := ae_all_iff.mpr (fun h=>
    ZeroPrivateRegularity.source_common_receipts D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor N (castMarketRare hrare) A h price)
  have h0 := ZeroPrivateRegularity.source_raw_numerical D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor (H0).val price
  have h1 := ZeroPrivateRegularity.source_raw_numerical D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor (H1).val price
  have hrows : ∀ᵐ rows ∂(ProbabilityMeasure.toMeasure (originalIid E (H0).val ρP)).prod
      (ProbabilityMeasure.toMeasure (originalIid E (H1).val ρP)),
      (∀ q,numericalEntry (rows.1 q)≠(price:ℝ)) ∧
      (∀ q,numericalEntry (rows.2 q)≠(price:ℝ)) :=
    ae_pair _ _ h0 h1
  have hp : ∀ᵐ payload ∂ν,
      (∀ q,numericalEntry (payload.1.1 q)≠(price:ℝ)) ∧
      (∀ q,numericalEntry (payload.1.2 q)≠(price:ℝ)) :=
    (measurePreserving_fst («μ»:=(ProbabilityMeasure.toMeasure (originalIid E (H0).val ρP)).prod
      (ProbabilityMeasure.toMeasure (originalIid E (H1).val ρP)))
      («ν»:=(Measure.pi (fun _ : Fin 2=> seedLaw)).prod (permLaw 2))).quasiMeasurePreserving.ae hrows
  have hp' := (measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=ν)).quasiMeasurePreserving.ae hp
  exact (ae_pair M ((volume : Measure unitInterval).prod ν) hc hp').mono fun x hx=>
    ⟨hx.1,ZeroPrivateRegularity.focalRow_no_ties K i kind side x.2.2.1 price hx.2.1 hx.2.2⟩

theorem native_numerical (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) (side : Bool) (v : ℝ) (price : Icc D.R D.Up) :
    ∀ᵐ x ∂(volume : Measure unitInterval).prod μ,
      nativeValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i side v price x.2=
      numericalValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind side v price
        (allSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x) := by
  have hs := (measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ)).quasiMeasurePreserving.ae
    (fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind)
  have hp := (allSeed_preserves D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
    i kind cats L hL).quasiMeasurePreserving.ae
      (numerical_regular D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind side price)
  filter_upwards [hs,allSeed_shape D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
    i kind,hp] with x hx hseed hregular
  let ω := (restoreSample i x.2).1
  let y := allSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x
  have hr := restored_source_rivals D P t hdR H hUH N
    i x.2 (fun r=>(hx r).1)
  have hm (r : Fin N) : NativeMenuReports.MenuAction E (ω.1 (i.succAbove r)).1.2 :=
    NativeMenuReports.source_menu E P t _ (hr _ (Fin.succAbove_ne i r))
  have hk := restored_kind D P hdR H hUH N
    i x.2 kind (fun r=>(hx r).2)
  have hh := OrderedZeroPartialTerminal.value_regular K i kind Q G
    (localData_publicChoice D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare))
    ω hm hk side price (lowPresent D P t ht kind) y.2.1
    (hseed price (physical side)) (base_receipt_gap D)
    (by simpa only [y,allSeed,numerical,ω,restoreSample,restoreUsers_succAbove] using! hregular.1)
    (by simpa only [y,allSeed,numerical,ω,restoreSample,restoreUsers_succAbove] using! hregular.2) v
  simpa only [nativeValue,numericalValue,y,allSeed,numerical,ω,restoreSample,
    restoreUsers_succAbove,NativePartialTerminal.privateSeed,physical] using! hh

theorem original_side_integral (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) (side : Bool) (v : ℝ) (price : Icc D.R D.Up) :
    (∫ w,nativeValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i side v price w ∂μ)=
    ∫ x,numericalValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind side v price x ∂Ξ := by
  let f := nativeValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i side v price
  let g := numericalValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind side v price
  have hf : Measurable f := (measurable_nativeValue D P t ht hdR H hUH πL π upperBid hupperBid
    hfloor N hrare i side v).comp (measurable_const.prodMk measurable_id)
  have hg : Measurable g := (measurable_numericalValue D P t ht hdR H hUH πL π upperBid hupperBid
    hfloor N hrare i kind side v).comp (measurable_const.prodMk measurable_id)
  calc
    _=∫ x,f x.2 ∂(volume : Measure unitInterval).prod μ :=
      ((measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ)).integral_comp_ae_real hf.aestronglyMeasurable).symm
    _=∫ x,g (allSeed D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x)
        ∂(volume : Measure unitInterval).prod μ := integral_congr_ae
      (native_numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind
        cats L hL side v price)
    _=_ := (allSeed_preserves D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      i kind cats L hL).integral_comp_ae_real hg.aestronglyMeasurable

end Atomless

theorem fiber_payoff_halves (v : ℝ) (b : Icc (E).R (E).Rp) :
    affineCountUtility
      (fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind i
        (RawRoutes.action b (D.hR.le.trans b.2.1) 1)) v b D.eta D.heta0 D.heta1=
      (1/2:ℝ)*(∫ w,nativeValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        i false v b w ∂μ)+
      (1/2:ℝ)*(∫ w,nativeValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        i true v b w ∂μ) := by
  let β : Measure ((Fin N → UserDraw 2)×(Fin 2→ Seed)) :=
    (Measure.pi (fun r => cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind r}))).prod
      (Measure.pi (fun _ : Fin 2 => (Γ).seedLaw))
  haveI : IsProbabilityMeasure β := by
    haveI (r : Fin N) : IsProbabilityMeasure (cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind r})) :=
      cond_isProbabilityMeasure (native_source_category_ne_zero D P t ht hdR H hUH πL π
        upperBid hupperBid hfloor Γ
        (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)) (kind r))
    unfold β
    infer_instance
  let restore : ((Fin N→ UserDraw 2)×(Fin 2→ Seed)) → Background m 2 Seed :=
    fun y => (restoreUsers i y.1,y.2)
  have hr : Measurable restore := ((measurable_restoreUsers i).comp measurable_fst).prodMk measurable_snd
  let aa : ((Fin N→ UserDraw 2)×(Fin 2→ Seed)) → Bool×Bool := fun y =>
    (OrderedNativePayoffPartialTerminal.privateAccept K i false b (restore y),OrderedNativePayoffPartialTerminal.privateAccept K i true b (restore y))
  have ha : Measurable aa := measurable_restored_pair K i b
  let f : Fin 3 → ℝ := fun r => userPayoff v b 0
    (Schedule.affine 2 D.eta D.heta0 D.heta1).charge (Schedule.once 2).charge r.val
  have hg : Measurable (fun w : DeletedSample N Seed => gated (aa w.1) w.2) :=
    measurable_gated_comp aa ha
  have hgi : Integrable (fun w : DeletedSample N Seed => f (gated (aa w.1) w.2)) μ :=
    HierarchicalFiniteSampler.integrable_finite_comp μ _ hg f
  have hc : ∀ᵐ w ∂μ,deletedCount Γ i (RawRoutes.action b (D.hR.le.trans b.2.1) 1) w=
      gated (aa w.1) w.2 := by
    filter_upwards [fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind] with w hw
    have hrivals := restored_source_rivals D P t hdR H hUH N i w (fun r => (hw r).1)
    have hc := source_partial_count D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)
      i b 1 (restoreSample i w) hrivals
    rw [OrderedZeroNativeBindings.privateAccept_eq D P t ht hdR H hUH πL π upperBid
        hupperBid hfloor N (castMarketRare hrare) i b _ hrivals 0,
      OrderedZeroNativeBindings.privateAccept_eq D P t ht hdR H hUH πL π upperBid
        hupperBid hfloor N (castMarketRare hrare) i b _ hrivals 1] at hc
    simpa only [OrderedNativePayoffPartialTerminal.privateAccept,physical,
      PartialScalarIntegration.gated,aa,restore,restoreSample,Bool.false_eq_true,ite_false,ite_true] using! hc
  have hi (side : Bool) : Integrable
      (fun y => (v-b)*(if OrderedNativePayoffPartialTerminal.privateAccept K i side b (restore y) then (1:ℝ) else 0)) β := by
    apply Integrable.of_bound
      ((measurable_const.mul ((measurable_of_countable (fun a : Bool => if a then (1:ℝ) else 0)).comp
        ((OrderedNativePayoffPartialTerminal.measurable_privateAccept K i side).comp (measurable_const.prodMk hr)))).aestronglyMeasurable)
      (|v|+(E).Rp)
    exact ae_of_all _ fun y => indicator_surplus_bound D.hR.le v b _
  have hprojection (side : Bool) :
      (∫ w,nativeValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        i side v b w ∂μ)=
      ∫ y,(v-b)*(if OrderedNativePayoffPartialTerminal.privateAccept K i side b (restore y) then (1:ℝ) else 0) ∂β := by
    exact (measurePreserving_fst («μ»:=β) («ν»:=permLaw 2)).integral_comp_ae_real (hi side).aestronglyMeasurable
  rw [affineCountUtility,CountLaw.utility,fiberCount,FiniteLaw.expect_ofMeasure]
  change (∫ w,f (deletedCount Γ i (RawRoutes.action b (D.hR.le.trans b.2.1) 1) w) ∂μ)=_
  rw [integral_congr_ae (hc.mono fun _ h => congrArg f h)]
  change (∫ w : ((Fin N→UserDraw 2)×(Fin 2→Seed))×Equiv.Perm (Fin 2),
    f (gated (aa w.1) w.2) ∂β.prod (permLaw 2))=_
  rw [integral_prod _ hgi]
  dsimp only [f]
  simp_rw [fair_route_payoff D.eta D.heta0 D.heta1 v (b:ℝ)]
  rw [integral_add ((hi false).const_mul (1/2:ℝ)) ((hi true).const_mul (1/2:ℝ))]
  simp only [hprojection,integral_const_mul]

section Atomless
variable [hA : NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (Subtype.val (OrderedNativeZeroNoiseSource.active D P t ht π))))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (Subtype.val (π 2))).map (fun x=>(x.2:ℝ)))]

theorem original_partial_numeric (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) (v : ℝ) (price : Icc D.R D.Up) :
    affineCountUtility
      (fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind i
        (RawRoutes.action price (D.hR.le.trans price.2.1) 1)) v price D.eta D.heta0 D.heta1=
      (1/2:ℝ)*(∫ x,numericalValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        i kind false v price x ∂Ξ)+
      (1/2:ℝ)*(∫ x,numericalValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        i kind true v price x ∂Ξ) := by
  rw [fiber_payoff_halves D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind,
    original_side_integral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      i kind cats L hL false v price,
    original_side_integral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      i kind cats L hL true v price]

end Atomless
end FCAppendix.Affine.Tail04.OrderedZeroPartialFiberLaw
