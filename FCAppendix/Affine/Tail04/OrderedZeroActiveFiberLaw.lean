import FCAppendix.Affine.Tail04.OrderedNativePayoffActiveCoordinates
import FCAppendix.Affine.Tail04.ZeroCommonRowLaw
import FCAppendix.Affine.Tail04.OrderedZeroNativeBindings

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroActiveFiberLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeCategories
open NativeLocalPolicy NativeDeletedCounts OrderedZeroNativeBindings NativeActiveFiberCoordinates
open NativeHighExperiment PrivateRowSorting EqualPrivateUpper OriginalFiniteFibers
open PartialNativeCoordinates CompactSourceBidLaws

section Shuffle
variable {A X Z : Type*} [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Z]

def exposeCommon (z : unitInterval×((A×X)×Z)) : A×(unitInterval×(X×Z)) :=
  (z.2.1.1,(z.1,(z.2.1.2,z.2.2)))

lemma measurable_exposeCommon : Measurable (exposeCommon (A:=A) (X:=X) (Z:=Z)) :=
  measurable_snd.fst.fst.prodMk
    (measurable_fst.prodMk (measurable_snd.fst.snd.prodMk measurable_snd.snd))

lemma exposeCommon_preserves (μ : Measure A) (ν : Measure X) (ω : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ω] :
    MeasurePreserving exposeCommon ((volume : Measure unitInterval).prod (((μ).prod ν).prod ω))
      ((μ).prod ((volume : Measure unitInterval).prod ((ν).prod ω))) := by
  exact (measurePreserving_prodAssoc μ (volume : Measure unitInterval) ((ν).prod ω)).comp
    (((Measure.measurePreserving_swap («μ»:=(volume : Measure unitInterval)) («ν»:=μ)).prod
      (MeasurePreserving.id ((ν).prod ω))).comp
      ((measurePreserving_prodAssoc (volume : Measure unitInterval) μ ((ν).prod ω)).symm.comp
        ((MeasurePreserving.id (volume : Measure unitInterval)).prod
          (measurePreserving_prodAssoc μ ν ω))))

end Shuffle

lemma measurable_cons_outcome {m c A : ℕ} (K : Data m c)
    (H0 H1 : Fin (m+1)) (Q : PublicScenario.Data) (b : Icc (1:ℝ) K.E.U) (low : Bool) :
    Measurable (fun x : (Fin A→Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1) =>
      OrderedNativePayoffExperiment.rawOutcome K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) K.E.U) b x.1) 0 low x.2) := by
  have hc : Measurable (fun x : (Fin A→Icc (1:ℝ) K.E.U)×
      (unitInterval×RawPayload K H0 H1) =>
        Fin.cons (α:=fun _=>Icc (1:ℝ) K.E.U) b x.1) := by
    refine measurable_pi_lambda _ (fun j => ?_)
    refine Fin.cases measurable_const (fun l=>?_) j
    exact (measurable_pi_apply l).comp measurable_fst
  have hj := OrderedNativePayoffExperiment.measurable_rawOutcome_joint (A:=A+1) K H0 H1 Q (0 : Fin (A+1)) low
  have hh : Measurable (fun x : (Fin A→Icc (1:ℝ) K.E.U)×
      (unitInterval×RawPayload K H0 H1) =>
        (Fin.cons (α:=fun _=>Icc (1:ℝ) K.E.U) b x.1,x.2)) :=
    hc.prodMk measurable_snd
  have hg := hj.comp hh
  exact hg

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
local notation "Γ₀" => coreGame D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "G" => (LowBody.realLowBidLaw (Subtype.val πL) : Measure ℝ)
def commonLaw : ProbabilityMeasure (Icc (1:ℝ) (E).U) :=
  bidMarginal (Subtype.val (active D P t ht π))

def privateLaw : ProbabilityMeasure (Ici (K).E.H ⊕ Icc (K).E.R (K).E.Rp) :=
  OriginalPrivateSource.originalEntryLaw E P rfl t ht.le πL
    (partialLaw D P t ht π) (active D P t ht π) upperBid hupperBid hfloor

local notation "ρA" => commonLaw D P t ht hdR H hUH π
local notation "ρP" => privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare

variable (i : Fin (N+1)) (kind : Fin N → Fin 4)
local notation "A" => commonSize i kind
local notation "H0" => NativeLocalPolicy.Data.finiteCount K (rivalSet i kind 2)
local notation "H1" => NativeLocalPolicy.Data.finiteCount K (rivalSet i kind 3)
local notation "μ" => fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind
local notation "ν" => NativeHighExperiment.rawPayloadLaw K ρP H0 H1
local notation "M" => Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure ρA)

abbrev Numerical := (Fin A → Icc (1:ℝ) (E).U)×NativeHighExperiment.RawPayload K H0 H1

def numerical (w : DeletedSample N Seed) : Numerical D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N hrare i kind :=
  (commonRow E i kind w.1.1,
    ((privateRowRaw E i kind 2 w.1.1,privateRowRaw E i kind 3 w.1.1),(w.1.2,w.2)))

lemma measurable_numerical : Measurable
    (numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind) :=
  ((measurable_commonRow E i kind).comp measurable_fst.fst).prodMk
    ((((measurable_privateRowRaw E i kind 2).comp measurable_fst.fst).prodMk
      ((measurable_privateRowRaw E i kind 3).comp measurable_fst.fst)).prodMk
      (measurable_fst.snd.prodMk measurable_snd))

theorem numerical_preserves : MeasurePreserving
    (numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind)
    μ ((M).prod ν) := by
  let f := OriginalFiberProduct.fiberRows (Z:=ZeroNativeFiberProduct.RestSeeds) kind A (H0).val (H1).val
    (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind)
    (ZeroNativeFiberProduct.commonProjection D P hdR H hUH)
    (ZeroNativeFiberProduct.privateProjection D P hdR H hUH)
  have hf : Measurable (f ∘ ZeroNativeFiberProduct.associate N) :=
    (OriginalFiberProduct.measurable_fiberRows (Z:=ZeroNativeFiberProduct.RestSeeds) kind A (H0).val (H1).val
      (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind) _ _
      (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH)
      (ZeroNativeFiberProduct.measurable_privateProjection D P hdR H hUH)).comp
        (ZeroNativeFiberProduct.measurable_associate N)
  have hp : MeasurePreserving (f ∘ ZeroNativeFiberProduct.associate N) μ
      ((OriginalFiberProduct.numericalLaw A (H0).val (H1).val (ProbabilityMeasure.toMeasure ρA) (ProbabilityMeasure.toMeasure ρP)).prod
        (ZeroNativeFiberProduct.restSeedLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare)) :=
    ⟨hf,ZeroNativeFiberProduct.native_numerical_fibers D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor N hrare kind A (H0).val (H1).val
      (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind)⟩
  change MeasurePreserving (f ∘ ZeroNativeFiberProduct.associate N) μ
    (((M).prod ((ProbabilityMeasure.toMeasure (originalIid (K).E (H0).val ρP)).prod
      (ProbabilityMeasure.toMeasure (originalIid (K).E (H1).val ρP)))).prod
        ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2))) at hp
  exact (measurePreserving_prodAssoc M
    ((ProbabilityMeasure.toMeasure (originalIid (K).E (H0).val ρP)).prod
      (ProbabilityMeasure.toMeasure (originalIid (K).E (H1).val ρP)))
    ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2))).comp hp

variable (n : ℕ) (el : Fin (n+1) ≃ {r : Fin N // kind r=0})

def seeded (w : DeletedSample N Seed) :
    (Fin A → Icc (1:ℝ) (E).U)×(unitInterval×NativeHighExperiment.RawPayload K H0 H1) :=
  ((numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind w).1,
    (conditionalMinimumSeed (nativeLowBidLaw Γ E) n (fun j => nativeBid (w.1.1 (el j))),
      (numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind w).2))

lemma measurable_seeded : Measurable
    (seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el) :=
  (measurable_numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind).fst.prodMk
    (((measurable_conditionalMinimumSeed _ n).comp (measurable_pi_lambda _ fun j =>
      measurable_nativeBid.comp ((measurable_pi_apply (el j).val).comp measurable_fst.fst))).prodMk
      (measurable_numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind).snd)

theorem seeded_preserves (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) : MeasurePreserving
    (seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el)
    μ ((M).prod ((volume : Measure unitInterval).prod ν)) := by
  have huser : userLaw Γ=userLaw (NativeZeroNoiseSource.game D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor (N+1) (castMarketRare hrare)) := by
    rw [userLaw,userLaw,
      OrderedNativeZeroNoiseSource.game_original_joint D P t ht hdR H hUH πL π
        upperBid hupperBid hfloor (N+1) (castMarketRare hrare),
      NativeZeroNoiseSource.game_original_joint D P t ht hdR H hUH πL π
        upperBid hupperBid hfloor (N+1) (castMarketRare hrare)]
    rfl
  let f := (OriginalFiberProduct.seedRows (userLaw Γ) (E).coarseTag kind A (H0).val (H1).val
    (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind)
    (ZeroNativeFiberProduct.commonProjection D P hdR H hUH)
    (ZeroNativeFiberProduct.privateProjection D P hdR H hUH) nativeBid n el) ∘
      ZeroNativeFiberProduct.associate N
  have hf : Measurable f :=
    (OriginalFiberProduct.measurable_seedRows (userLaw Γ) (E).coarseTag kind A (H0).val (H1).val
      (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind) _ _
      (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH)
      (ZeroNativeFiberProduct.measurable_privateProjection D P hdR H hUH)
      nativeBid measurable_nativeBid n el).comp (ZeroNativeFiberProduct.measurable_associate N)
  have hp : MeasurePreserving f μ
      ((volume : Measure unitInterval).prod
        ((OriginalFiberProduct.numericalLaw A (H0).val (H1).val (ProbabilityMeasure.toMeasure ρA) (ProbabilityMeasure.toMeasure ρP)).prod
          (ZeroNativeFiberProduct.restSeedLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare))) :=
    by
      refine ⟨hf,?_⟩
      simpa only [f,huser] using! ZeroNativeFiberProduct.native_seed_numerical_fibers_of_C2 D P t ht hdR H hUH πL π
        upperBid hupperBid hfloor N hrare kind A (H0).val (H1).val
        (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind) n el cats L hL
  change MeasurePreserving f μ ((volume : Measure unitInterval).prod
    (((M).prod ((ProbabilityMeasure.toMeasure (originalIid (K).E (H0).val ρP)).prod
      (ProbabilityMeasure.toMeasure (originalIid (K).E (H1).val ρP)))).prod
        ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2)))) at hp
  exact (exposeCommon_preserves M
    ((ProbabilityMeasure.toMeasure (originalIid (K).E (H0).val ρP)).prod
      (ProbabilityMeasure.toMeasure (originalIid (K).E (H1).val ρP)))
    ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2))).comp hp

variable [hA : NullSingletonClass (bidMarginal (Subtype.val
  (OrderedNativeZeroNoiseSource.active D P t ht π)) : Measure (Icc (1:ℝ) D.U))]

omit n el in
lemma common_distinct (b : Icc (1:ℝ) (E).U) :
    ∀ᵐrow ∂M,Function.Injective (fun j=>(Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b row j:ℝ)) := by
  letI : NullSingletonClass (ProbabilityMeasure.toMeasure ρA) := hA
  exact ZeroCommonRowLaw.ae_cons_injective ρA A b

omit n el in
lemma native_common_distinct (b : Icc (1:ℝ) (E).U) :
    ∀ᵐ w ∂μ,Function.Injective (fun j => (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b (commonRow E i kind w.1.1) j:ℝ)) :=
  (((measurePreserving_fst («μ»:=M) («ν»:=ν)).comp
    (numerical_preserves D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind)).quasiMeasurePreserving.ae
      (common_distinct D P t ht hdR H hUH π N i kind b))

theorem active_seeded_ae (b : Icc (1:ℝ) (E).U) :
    ∀ᵐ w ∂μ,deletedCount Γ i (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2) w=
      OrderedNativePayoffExperiment.rawOutcome K H0 H1 Q
        (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b (seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el w).1)
        0 true (seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el w).2 := by
  filter_upwards [fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind,
    native_common_distinct D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b] with w hw hb
  let ω:=restoreSample i w
  have hr:=restored_source_rivals D P t hdR H hUH N i w
    (fun r => (hw r).1)
  have hk:=restored_kind D P hdR H hUH N i w kind
    (fun r => (hw r).2)
  have hm (r : Fin N) : NativeMenuReports.MenuAction E (ω.1.1 (i.succAbove r)).1.2 :=
    NativeMenuReports.source_menu E P t _ (hr _ (Fin.succAbove_ne i r))
  let e : Fin (n+1) ≃ {r : Fin N // rivalKinds E i ω.1 r=0} := el.trans (Equiv.subtypeEquivRight (fun r => by rw [hk]))
  have hs' (j : Fin 2) : seedOnList G ((E).roleList 0 (presentList ω.1 i b j))=
      some (conditionalMinimumSeed (nativeLowBidLaw Γ E) n (fun j => nativeBid (w.1.1 (el j)))) := by
    have hs:=active_low_seed_enumeration E i ω.1 hm b j G n e
    rw [source_lowBidLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)]
    simpa only [e,Equiv.trans_apply,Equiv.subtypeEquivRight_apply,ω,restoreSample,
      restoreUsers_succAbove,nativeBid] using! hs
  change focalCount Γ i _ ω=_
  rw [sourceGame_focalCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)]
  have hh:=OrderedNativePayoffActiveCoordinates.active_count K Q G
    (localData_publicChoice D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare))
    P t i kind ω hr hk b
    (by simpa only [ω,restoreSample,restoreUsers_succAbove] using! hb) true _ hs' Γ₀ rfl
  simpa only [seeded,numerical,ω,restoreSample,restoreUsers_succAbove] using! hh

omit n el in

theorem active_noLow_ae (b : Icc (1:ℝ) (E).U) (hl : ∀ r,kind r≠0) :
    ∀ᵐ w ∂μ,∀ u : unitInterval,
      deletedCount Γ i (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2) w=
        OrderedNativePayoffExperiment.rawOutcome K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b (commonRow E i kind w.1.1)) 0 false
          (u,(numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind w).2) := by
  filter_upwards [fiber_support D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare) kind,
    native_common_distinct D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b] with w hw hb
  intro u
  let ω:=restoreSample i w
  have hr:=restored_source_rivals D P t hdR H hUH N i w
    (fun r => (hw r).1)
  have hk:=restored_kind D P hdR H hUH N i w kind
    (fun r => (hw r).2)
  have hm (r : Fin N) : NativeMenuReports.MenuAction E (ω.1.1 (i.succAbove r)).1.2 :=
    NativeMenuReports.source_menu E P t _ (hr _ (Fin.succAbove_ne i r))
  have hs (j : Fin 2) := active_no_low_seed E i ω.1 hm b j G (by change ∀r,rivalKinds E i (restoreSample i w).1 r≠0;rw [hk];exact hl)
  change focalCount Γ i _ ω=_
  rw [sourceGame_focalCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare)]
  have hh:=OrderedNativePayoffActiveCoordinates.active_count K Q G
    (localData_publicChoice D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (castMarketRare hrare))
    P t i kind ω hr hk b
    (by simpa only [ω,restoreSample,restoreUsers_succAbove] using! hb) false u hs Γ₀ rfl
  simpa only [numerical,ω,restoreSample,restoreUsers_succAbove] using! hh

omit n el hA in
lemma measurable_insert_outcome (b : Icc (1:ℝ) (E).U) (low : Bool) :
    Measurable (fun x : (Fin A → Icc (1:ℝ) (E).U)×(unitInterval×RawPayload K H0 H1) =>
      OrderedNativePayoffExperiment.rawOutcome K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b x.1) 0 low x.2) := by
  exact measurable_cons_outcome K H0 H1 Q b low

omit n el in
def numericalCount (b : Icc (1:ℝ) (E).U) (low : Bool) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((M).prod ((volume : Measure unitInterval).prod ν))
    (fun x => OrderedNativePayoffExperiment.rawOutcome K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b x.1) 0 low x.2)
    (measurable_insert_outcome D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b low)

include n el in
theorem fiberCount_low (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) (b : Icc (1:ℝ) (E).U) :
    fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind i
      (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2)=
        numericalCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b true := by
  let T:=seeded D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el
  let f:=fun x : (Fin A → Icc (1:ℝ) (E).U)×(unitInterval×RawPayload K H0 H1) =>
    OrderedNativePayoffExperiment.rawOutcome K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b x.1) 0 true x.2
  have hf:=measurable_insert_outcome D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b true
  calc
    _=FiniteLaw.ofMeasure μ (f ∘ T) (hf.comp (measurable_seeded D P t ht hdR H hUH
      πL π upperBid hupperBid hfloor N hrare i kind n el)) :=
        FiniteLaw.ofMeasure_congr_ae _ _ _ _ _
          (active_seeded_ae D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el b)
    _=_ := FiniteLaw.ofMeasure_comp_measurePreserving _ _ T
      (seeded_preserves D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind n el cats L hL) f hf

omit n el in

theorem fiberCount_noLow (b : Icc (1:ℝ) (E).U) (hl : ∀ r,kind r≠0) :
    fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind i
      (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2)=
        numericalCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b false := by
  let T : unitInterval×DeletedSample N Seed →
      (Fin A → Icc (1:ℝ) (E).U)×(unitInterval×RawPayload K H0 H1) := fun x =>
    ((numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x.2).1,
      (x.1,(numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind x.2).2))
  have hp : MeasurePreserving T ((volume : Measure unitInterval).prod μ)
      ((M).prod ((volume : Measure unitInterval).prod ν)) :=
    (measurePreserving_prodAssoc M (volume : Measure unitInterval) ν).comp
      (((Measure.measurePreserving_swap («μ»:=(volume : Measure unitInterval)) («ν»:=M)).prod
        (MeasurePreserving.id ν)).comp
        ((measurePreserving_prodAssoc (volume : Measure unitInterval) M ν).symm.comp
          ((MeasurePreserving.id (volume : Measure unitInterval)).prod
            (numerical_preserves D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind))))
  let a:=RawRoutes.action b (le_trans (by norm_num) b.2.1) 2
  let f:=fun x : (Fin A → Icc (1:ℝ) (E).U)×(unitInterval×RawPayload K H0 H1) =>
    OrderedNativePayoffExperiment.rawOutcome K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b x.1) 0 false x.2
  have hf:=measurable_insert_outcome D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b false
  calc
    _=FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod μ)
      ((deletedCount Γ i a) ∘ Prod.snd) ((measurable_deletedCount Γ i a).comp measurable_snd) :=
        (FiniteLaw.ofMeasure_comp_measurePreserving _ _ Prod.snd
          (measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ))
          (deletedCount Γ i a) (measurable_deletedCount Γ i a)).symm
    _=FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod μ) (f ∘ T) (hf.comp hp.measurable) := by
      apply FiniteLaw.ofMeasure_congr_ae
      exact ((measurePreserving_snd («μ»:=(volume : Measure unitInterval)) («ν»:=μ)).quasiMeasurePreserving.ae
        (active_noLow_ae D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b hl)).mono
          (fun x hx => hx x.1)
    _=_ := FiniteLaw.ofMeasure_comp_measurePreserving _ _ T hp f hf

omit n el hA in

theorem numericalCount_expect (b : Icc (1:ℝ) (E).U) (low : Bool) (f : Fin 3 → ℝ) :
    (numericalCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b low).expect f=
      ∫ row,(IndependentCounts.bernoulli (Q).θ (Q).θ_nonneg (Q).θ_le_one).expect
        (fun reg => (OrderedNativePayoffExperiment.perRegime K H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b row) 0 reg low).expect f) ∂M := by
  erw [numericalCount,FiniteLaw.expect_ofMeasure,integral_prod _
    (HierarchicalFiniteSampler.integrable_finite_comp _ _
      (measurable_insert_outcome D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i kind b low) f)]
  apply integral_congr_ae
  exact ae_of_all _ fun row => by
    dsimp only []
    erw [←FiniteLaw.expect_ofMeasure,←OrderedNativePayoffExperiment.rawLaw,
      OrderedNativePayoffExperiment.rawLaw_regime K ρP (fun _ => rfl) H0 H1 Q (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b row) 0
        rfl rfl rfl rfl low,FiniteLaw.expect_finiteMix]
    exact OrderedNativePayoffExperiment.measurable_rawOutcome K H0 H1 Q
      (Fin.cons (α:=fun _=>Icc (1:ℝ) (E).U) b row) 0 low

end FCAppendix.Affine.Tail04.OrderedZeroActiveFiberLaw
