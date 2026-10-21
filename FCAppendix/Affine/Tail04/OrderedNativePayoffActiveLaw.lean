import FCAppendix.Affine.Tail04.OrderedNativePayoffActiveCoordinates
import FCAppendix.Affine.Tail04.OriginalNoiseProduct

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffActiveLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource OrderedNoisyNativeCategories
open NativeLocalPolicy NativeDeletedCounts OrderedNativePayoffBindings NativeActiveFiberCoordinates
open NativeHighExperiment PrivateRowSorting EqualPrivateUpper OriginalFiniteFibers
open PartialNativeCoordinates CompactSourceBidLaws NativeMenuReports

section Shuffle
variable {A X Z : Type*} [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Z]

def exposeCommon (z : unitInterval×((A×X)×Z)) : A×(unitInterval×(X×Z)) :=
  (z.2.1.1,(z.1,(z.2.1.2,z.2.2)))

lemma measurable_exposeCommon : Measurable (exposeCommon (A:=A) (X:=X) (Z:=Z)) :=
  measurable_snd.fst.fst.prodMk
    (measurable_fst.prodMk (measurable_snd.fst.snd.prodMk measurable_snd.snd))

lemma exposeCommon_preserves (μ : Measure A) (ν : Measure X) (ω : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ω] :
    MeasurePreserving exposeCommon ((volume : Measure unitInterval).prod ((μ.prod ν).prod ω))
      (μ.prod ((volume : Measure unitInterval).prod (ν.prod ω))) := by
  exact (measurePreserving_prodAssoc μ (volume : Measure unitInterval) (ν.prod ω)).comp
    (((Measure.measurePreserving_swap (μ:=(volume : Measure unitInterval)) (ν:=μ)).prod
      (MeasurePreserving.id (ν.prod ω))).comp
      ((measurePreserving_prodAssoc (volume : Measure unitInterval) μ (ν.prod ω)).symm.comp
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
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

def commonLaw : ProbabilityMeasure (Icc (1:ℝ) (regions D P hdR H hBH).U) :=
  bidMarginal (activePhysical D P t ht π).1

def privateLaw : ProbabilityMeasure
    (Ici (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E.H ⊕ Icc (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E.R (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E.Rp) :=
  NoisyNativeFiberProduct.privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor

variable (i : Fin (N+1)) (kind : Fin N → Fin 4)

abbrev Numerical := (Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U)×NativeHighExperiment.RawPayload (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))

def numerical (w : DeletedSample N Seed) : Numerical D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor N hrare i kind :=
  (commonRow (regions D P hdR H hBH) i kind w.1.1,
    ((privateRowRaw (regions D P hdR H hBH) i kind 2 w.1.1,privateRowRaw (regions D P hdR H hBH) i kind 3 w.1.1),(w.1.2,w.2)))

lemma measurable_numerical : Measurable
    (numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind) :=
  ((measurable_commonRow (regions D P hdR H hBH) i kind).comp measurable_fst.fst).prodMk
    ((((measurable_privateRowRaw (regions D P hdR H hBH) i kind 2).comp measurable_fst.fst).prodMk
      ((measurable_privateRowRaw (regions D P hdR H hBH) i kind 3).comp measurable_fst.fst)).prodMk
      (measurable_fst.snd.prodMk measurable_snd))

theorem numerical_preserves : MeasurePreserving
    (numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind)
    (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind) ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)))) := by
  let f := OriginalFiberProduct.fiberRows (Z:=NoisyNativeFiberProduct.RestSeeds) kind (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val
    (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind)
    (NoisyNativeFiberProduct.commonProjection D P hdR H hBH)
    (NoisyNativeFiberProduct.privateProjection D P hdR H hBH)
  have hf : Measurable (f ∘ NoisyNativeFiberProduct.associate N) :=
    (OriginalFiberProduct.measurable_fiberRows (Z:=NoisyNativeFiberProduct.RestSeeds) kind (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val
        (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind) _ _
      (NoisyNativeFiberProduct.measurable_commonProjection D P hdR H hBH)
      (NoisyNativeFiberProduct.measurable_privateProjection D P hdR H hBH)).comp
        (NoisyNativeFiberProduct.measurable_associate N)
  have hp : MeasurePreserving (f ∘ NoisyNativeFiberProduct.associate N) (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)
      ((OriginalFiberProduct.numericalLaw (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val (ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π)) (ProbabilityMeasure.toMeasure (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))).prod
        (NoisyNativeFiberProduct.restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)) :=
    by
      refine ⟨hf,?_⟩
      exact NoisyNativeFiberProduct.native_numerical_fibers D P t ht hdR H hBH πL π
        upperBid hupperBid hfloor N hrare kind (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val
        (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind)
  change MeasurePreserving (f ∘ NoisyNativeFiberProduct.associate N) (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind) (((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))).prod ((ProbabilityMeasure.toMeasure (originalIid (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))).prod (ProbabilityMeasure.toMeasure (originalIid (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))))).prod ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2))) at hp
  exact (measurePreserving_prodAssoc (Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π)))
    ((ProbabilityMeasure.toMeasure (originalIid (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))).prod (ProbabilityMeasure.toMeasure (originalIid (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))))
    ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2))).comp hp

variable (n : ℕ) (el : Fin (n+1) ≃ {r : Fin N // kind r=0})

def seeded (w : DeletedSample N Seed) :
    (Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U)×(unitInterval×NativeHighExperiment.RawPayload (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))) :=
  ((numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind w).1,
    (conditionalMinimumSeed (nativeLowBidLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) (regions D P hdR H hBH)) n (fun j => nativeBid (w.1.1 (el j))),
      (numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind w).2))

lemma measurable_seeded : Measurable
    (seeded D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el) :=
  (measurable_numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind).fst.prodMk
    (((measurable_conditionalMinimumSeed _ n).comp (measurable_pi_lambda _ fun j =>
      measurable_nativeBid.comp ((measurable_pi_apply (el j).val).comp measurable_fst.fst))).prodMk
      (measurable_numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind).snd)

theorem seeded_preserves (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) : MeasurePreserving
    (seeded D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el)
    (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind) ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))) := by
  have huser : userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare))=userLaw (NativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) := by
    rw [userLaw,userLaw]
    rw [OrderedNativeNoisySource.game_original_joint D P t ht hdR H hBH πL π
      upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare),
      NativeNoisySource.game_original_joint D P t ht hdR H hBH πL π
        upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)]
    rfl
  let f := (OriginalFiberProduct.seedRows (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare))) (regions D P hdR H hBH).coarseTag kind (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val
    (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind)
    (NoisyNativeFiberProduct.commonProjection D P hdR H hBH)
    (NoisyNativeFiberProduct.privateProjection D P hdR H hBH) nativeBid n el) ∘
      NoisyNativeFiberProduct.associate N
  have hf : Measurable f :=
    (OriginalFiberProduct.measurable_seedRows (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare))) (regions D P hdR H hBH).coarseTag kind (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val
        (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind) _ _
      (NoisyNativeFiberProduct.measurable_commonProjection D P hdR H hBH)
      (NoisyNativeFiberProduct.measurable_privateProjection D P hdR H hBH)
      nativeBid measurable_nativeBid n el).comp (NoisyNativeFiberProduct.measurable_associate N)
  have hp : MeasurePreserving f (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)
      ((volume : Measure unitInterval).prod
        ((OriginalFiberProduct.numericalLaw (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val (ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π)) (ProbabilityMeasure.toMeasure (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))).prod
          (NoisyNativeFiberProduct.restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))) :=
    by
      refine ⟨hf,?_⟩
      simpa only [f,huser] using! NoisyNativeFiberProduct.native_seed_numerical_fibers_of_C2 D P t ht hdR H hBH πL π
        upperBid hupperBid hfloor N hrare kind (commonSize i kind) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val
        (commonIndex i kind) (zeroIndex i kind) (oneIndex i kind) n el cats L hL
  change MeasurePreserving f (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind) ((volume : Measure unitInterval).prod (((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))).prod ((ProbabilityMeasure.toMeasure (originalIid (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))).prod (ProbabilityMeasure.toMeasure (originalIid (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))))).prod ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2)))) at hp
  exact (exposeCommon_preserves (Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π)))
    ((ProbabilityMeasure.toMeasure (originalIid (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)).val (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))).prod (ProbabilityMeasure.toMeasure (originalIid (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)).val (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare))))
    ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2))).comp hp

omit n el in
lemma common_distinct (b : Icc (1:ℝ) (regions D P hdR H hBH).U) :
    ∀ᵐ row ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))),Function.Injective (fun j => (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b row j:ℝ)) := by
  dsimp only [commonLaw]
  erw [NoisyCommonRowLaw.original_common_noisy_law D P t ht π]
  exact (OriginalNoiseProduct.ae_cons_physicalRow_distinct (by norm_num : (0:ℝ)<1)
    D.heps (commonSize i kind) ((installOriginal D P t ht).commonLaw (bidLaws D P t ht π)) (b:ℝ)).mono
      (fun row hr p q hpq => by
        have he (j : Fin (commonSize i kind+1)) :
            (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b row j:ℝ)=
              Fin.cons (α:=fun _=>ℝ) (b:ℝ) (fun k => (row k:ℝ)) j := by
          refine Fin.cases rfl (fun _=>rfl) j
        by_contra hn
        exact hr p q hn (by rw [←he,←he];exact hpq))

omit n el in
lemma native_common_distinct (b : Icc (1:ℝ) (regions D P hdR H hBH).U) :
    ∀ᵐ w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),Function.Injective (fun j => (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b (commonRow (regions D P hdR H hBH) i kind w.1.1) j:ℝ)) :=
  (((measurePreserving_fst (μ:=(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π)))) (ν:=(NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))).comp
    (numerical_preserves D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind)).quasiMeasurePreserving.ae
      (common_distinct D P t ht hdR H hBH π N i kind b))

theorem active_seeded_ae (b : Icc (1:ℝ) (regions D P hdR H hBH).U) :
    ∀ᵐ w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2) w=
      OrderedNativePayoffExperiment.rawOutcome (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor)
        (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b (seeded D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el w).1)
        0 true (seeded D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el w).2 := by
  filter_upwards [fiber_support D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind,
    native_common_distinct D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b] with w hw hb
  let ω:=restoreSample i w
  have hr:=restored_source_rivals D P t hdR H hBH N i w
    (fun r => (hw r).1)
  have hk:=restored_kind D P hdR H hBH N i w kind
    (fun r => (hw r).2)
  have hm (r : Fin N) : MenuAction (regions D P hdR H hBH) (ω.1.1 (i.succAbove r)).1.2 :=
    source_menu (regions D P hdR H hBH) P t _ (hr _ (Fin.succAbove_ne i r))
  let e : Fin (n+1) ≃ {r : Fin N // rivalKinds (regions D P hdR H hBH) i ω.1 r=0} := el.trans (Equiv.subtypeEquivRight (fun r => by rw [hk]))
  have hs' (j : Fin 2) : seedOnList (LowBody.realLowBidLaw πL.1 : Measure ℝ) ((regions D P hdR H hBH).roleList 0 (presentList ω.1 i b j))=
      some (conditionalMinimumSeed (nativeLowBidLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) (regions D P hdR H hBH)) n (fun j => nativeBid (w.1.1 (el j)))) := by
    have hs := active_low_seed_enumeration (regions D P hdR H hBH) i ω.1 hm b j (LowBody.realLowBidLaw πL.1 : Measure ℝ) n e
    rw [source_lowBidLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
    simpa only [e,Equiv.trans_apply,Equiv.subtypeEquivRight_apply,ω,restoreSample,
      restoreUsers_succAbove,nativeBid] using! hs
  change focalCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i _ ω=_
  rw [sourceGame_focalCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  have hh:=OrderedNativePayoffActiveCoordinates.active_count (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (LowBody.realLowBidLaw πL.1 : Measure ℝ)
    (localData_publicChoice D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
    P t i kind ω hr hk b
    (by simpa only [ω,restoreSample,restoreUsers_succAbove] using! hb) true _ hs' (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) rfl
  simpa only [seeded,numerical,ω,restoreSample,restoreUsers_succAbove] using! hh

omit n el in

theorem active_noLow_ae (b : Icc (1:ℝ) (regions D P hdR H hBH).U) (hl : ∀ r,kind r≠0) :
    ∀ᵐ w ∂(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind),∀ u : unitInterval,
      deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2) w=
        OrderedNativePayoffExperiment.rawOutcome (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b (commonRow (regions D P hdR H hBH) i kind w.1.1)) 0 false
          (u,(numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind w).2) := by
  filter_upwards [fiber_support D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind,
    native_common_distinct D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b] with w hw hb
  intro u
  let ω:=restoreSample i w
  have hr:=restored_source_rivals D P t hdR H hBH N i w
    (fun r => (hw r).1)
  have hk:=restored_kind D P hdR H hBH N i w kind
    (fun r => (hw r).2)
  have hm (r : Fin N) : MenuAction (regions D P hdR H hBH) (ω.1.1 (i.succAbove r)).1.2 :=
    source_menu (regions D P hdR H hBH) P t _ (hr _ (Fin.succAbove_ne i r))
  have hs (j : Fin 2) := active_no_low_seed (regions D P hdR H hBH) i ω.1 hm b j (LowBody.realLowBidLaw πL.1 : Measure ℝ) (by simpa only [ω,hk] using hl)
  change focalCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i _ ω=_
  rw [sourceGame_focalCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  have hh:=OrderedNativePayoffActiveCoordinates.active_count (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (LowBody.realLowBidLaw πL.1 : Measure ℝ)
    (localData_publicChoice D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
    P t i kind ω hr hk b
    (by simpa only [ω,restoreSample,restoreUsers_succAbove] using! hb) false u hs (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) rfl
  simpa only [numerical,ω,restoreSample,restoreUsers_succAbove] using! hh

omit n el in
lemma measurable_insert_outcome (b : Icc (1:ℝ) (regions D P hdR H hBH).U) (low : Bool) :
    Measurable (fun x : (Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U)×(unitInterval×RawPayload (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))) =>
      OrderedNativePayoffExperiment.rawOutcome (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b x.1) 0 low x.2) := by
  exact measurable_cons_outcome (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) b low

omit n el in
def numericalCount (b : Icc (1:ℝ) (regions D P hdR H hBH).U) (low : Bool) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)))))
    (fun x => OrderedNativePayoffExperiment.rawOutcome (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b x.1) 0 low x.2)
    (measurable_insert_outcome D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b low)

include n el in
theorem fiberCount_low (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) (b : Icc (1:ℝ) (regions D P hdR H hBH).U) :
    fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i
      (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2)=
        numericalCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b true := by
  let T:=seeded D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el
  let f:=fun x : (Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U)×(unitInterval×RawPayload (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))) =>
    OrderedNativePayoffExperiment.rawOutcome (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b x.1) 0 true x.2
  have hf:=measurable_insert_outcome D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b true
  calc
    _=FiniteLaw.ofMeasure (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind) (f ∘ T) (hf.comp (measurable_seeded D P t ht hdR H hBH
      πL π upperBid hupperBid hfloor N hrare i kind n el)) :=
        FiniteLaw.ofMeasure_congr_ae _ _ _ _ _
          (active_seeded_ae D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el b)
    _=_ := FiniteLaw.ofMeasure_comp_measurePreserving _ _ T
      (seeded_preserves D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind n el cats L hL) f hf

omit n el in

theorem fiberCount_noLow (b : Icc (1:ℝ) (regions D P hdR H hBH).U) (hl : ∀ r,kind r≠0) :
    fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i
      (RawRoutes.action b (le_trans (by norm_num) b.2.1) 2)=
        numericalCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b false := by
  let T : unitInterval×DeletedSample N Seed →
      (Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U)×(unitInterval×RawPayload (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))) := fun x =>
    ((numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x.2).1,
      (x.1,(numerical D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind x.2).2))
  have hp : MeasurePreserving T ((volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))
      ((Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))).prod ((volume : Measure unitInterval).prod (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))) :=
    (measurePreserving_prodAssoc (Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))) (volume : Measure unitInterval) (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)))).comp
      (((Measure.measurePreserving_swap (μ:=(volume : Measure unitInterval)) (ν:=(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))))).prod
        (MeasurePreserving.id (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))))).comp
        ((measurePreserving_prodAssoc (volume : Measure unitInterval) (Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))) (NativeHighExperiment.rawPayloadLaw (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)))).symm.comp
          ((MeasurePreserving.id (volume : Measure unitInterval)).prod
            (numerical_preserves D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind))))
  let a:=RawRoutes.action b (le_trans (by norm_num) b.2.1) 2
  let f:=fun x : (Fin (commonSize i kind) → Icc (1:ℝ) (regions D P hdR H hBH).U)×(unitInterval×RawPayload (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3))) =>
    OrderedNativePayoffExperiment.rawOutcome (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b x.1) 0 false x.2
  have hf:=measurable_insert_outcome D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b false
  calc
    _=FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))
      ((deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i a) ∘ Prod.snd) ((measurable_deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i a).comp measurable_snd) :=
        (FiniteLaw.ofMeasure_comp_measurePreserving _ _ Prod.snd
          (measurePreserving_snd (μ:=(volume : Measure unitInterval)) (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)))
          (deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i a) (measurable_deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)) i a)).symm
    _=FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)) (f ∘ T) (hf.comp hp.measurable) := by
      apply FiniteLaw.ofMeasure_congr_ae
      have ha := (measurePreserving_snd (μ:=(volume : Measure unitInterval))
        (ν:=(fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind))).quasiMeasurePreserving.ae
          (active_noLow_ae D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b hl)
      filter_upwards [ha] with x hx
      exact hx x.1
    _=_ := FiniteLaw.ofMeasure_comp_measurePreserving _ _ T hp f hf

omit n el in

theorem numericalCount_expect (b : Icc (1:ℝ) (regions D P hdR H hBH).U) (low : Bool) (f : Fin 3 → ℝ) :
    (numericalCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b low).expect f=
      ∫ row,(IndependentCounts.bernoulli (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_nonneg (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_le_one).expect
        (fun reg => (OrderedNativePayoffExperiment.perRegime (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b row) 0 reg low).expect f) ∂(Measure.pi (fun _ : Fin (commonSize i kind) => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hBH π))) := by
  erw [numericalCount,FiniteLaw.expect_ofMeasure,integral_prod _
    (HierarchicalFiniteSampler.integrable_finite_comp _ _
      (measurable_insert_outcome D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i kind b low) f)]
  apply integral_congr_ae
  exact ae_of_all _ fun row => by
    dsimp only []
    erw [←FiniteLaw.expect_ofMeasure,←OrderedNativePayoffExperiment.rawLaw,
      OrderedNativePayoffExperiment.rawLaw_regime (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (privateLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) (fun _ => rfl) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b row) 0
        rfl rfl rfl rfl low,FiniteLaw.expect_finiteMix]
    exact OrderedNativePayoffExperiment.measurable_rawOutcome (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (Fin.cons (α:=fun _=>Icc (1:ℝ) (regions D P hdR H hBH).U) b row) 0 low

end FCAppendix.Affine.Tail04.OrderedNativePayoffActiveLaw
