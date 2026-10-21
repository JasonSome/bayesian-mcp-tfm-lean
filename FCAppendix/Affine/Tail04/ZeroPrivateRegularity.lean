import FCAppendix.Affine.Tail04.ZeroNativeBindings
import FCAppendix.Affine.Tail04.OriginalPrivatePositiveLevels
import FCAppendix.Affine.Tail04.EqualSortedReceiptLaw
import FCAppendix.Affine.Tail04.ZeroPartialTerminal

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroPrivateRegularity
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation SourceTailNoisyFixedPoint
open NativeZeroNoiseSource ZeroNativeBindings OriginalPrivatePositiveLevels
open EqualPrivateSignal EqualPrivateUpper CompactSourceBidLaws PrivateRowSorting
open PrivatePayoffContinuity PrivatePartialSorting SortedAllNoise

theorem regular_update {A K c : ℕ} {R U B ξ : ℝ}
    (hR : 0< R) (common : Fin A→ Icc (1:ℝ) B)
    (prior : WeakProbability.Law (Signal K R U)) (row : Signal K R U)
    (j : Fin K) (price : Icc R U)
    (hc : ∀ i,EqualReceiptLaw.receipt (c:=c) (ξ:=ξ) prior common i≠(price:ℝ))
    (hp : ∀ l,l≠j→ partialBid (row l)≠(price:ℝ)) :
    policyInput (c:=c) (ξ:=ξ) (common,prior)
      (Function.update row j (Sum.inr price))∈Regular ξ j := by
  refine ⟨?_,?_⟩
  · simpa only [policyInput,Function.update_self,partialBid] using hR.trans_le price.2.1
  · intro a ha
    cases a with
    | inl i =>
      simpa only [policyInput,itemReceipt,Function.update_self,partialBid,
        EqualReceiptLaw.receipt,EqualPrivateMeasurable.bids] using! hc i
    | inr l =>
      have hlj : l≠j := fun he=> ha (congrArg Sum.inr he)
      simpa only [policyInput,itemReceipt,Function.update_self,
        Function.update_of_ne hlj,partialBid] using hp l hlj

theorem regular_focal {A K c : ℕ} {R U B H ξ : ℝ}
    (hR : 0< R) (common : Fin A→ Icc (1:ℝ) B)
    (prior : WeakProbability.Law (Signal K R U)) (row : Row K R U H)
    (j : Fin K) (price : Icc R U) (hj : row j=Sum.inr price)
    (hc : ∀ i,EqualReceiptLaw.receipt (c:=c) (ξ:=ξ) prior common i≠(price:ℝ))
    (hp : ∀ l,l≠j→ numericalEntry (row l)≠(price:ℝ)) :
    policyInput (c:=c) (ξ:=ξ) (common,prior) (signal row)∈Regular ξ j := by
  refine ⟨?_,?_⟩
  · simpa only [policyInput,signal,hj,signalEntry,partialBid] using hR.trans_le price.2.1
  · intro a ha
    cases a with
    | inl i =>
      simpa only [policyInput,itemReceipt,signal,hj,signalEntry,partialBid,
        EqualReceiptLaw.receipt,EqualPrivateMeasurable.bids] using! hc i
    | inr l =>
      have hlj : l≠j := fun he=> ha (congrArg Sum.inr he)
      have hn := hp l hlj
      cases he : row l with
      | inl v =>
        have hp0 : (0:ℝ)≠price := (hR.trans_le price.2.1).ne
        simpa only [policyInput,itemReceipt,signal,hj,he,signalEntry,partialBid] using hp0
      | inr b =>
        simpa only [policyInput,itemReceipt,signal,hj,he,signalEntry,partialBid,
          numericalEntry] using hn

theorem focalRow_no_ties {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c)
    (i : Fin (N+1)) (kind : Fin N→ Fin 4) (side : Bool)
    (rows : NativePartialTerminal.Rows K i kind) (price : Icc K.E.R K.E.Rp)
    (h0 : ∀ l,numericalEntry (rows.1 l)≠(price:ℝ))
    (h1 : ∀ l,numericalEntry (rows.2 l)≠(price:ℝ)) :
    ∀ l,l≠NativePartialTerminal.focalIndex K i kind side→
      numericalEntry (NativePartialTerminal.focalRow K i kind side price rows l)≠(price:ℝ) := by
  intro l hl
  cases side
  · let e := NativeFiberEnumerations.insert_card (PartialNativeCoordinates.rivalSet i kind 2) i
      (PartialNativeCoordinates.focal_not_mem_rivalSet i kind 2)
    have hz : Fin.cast e l≠0 := by
      intro hz
      apply hl
      apply Fin.ext
      change l.val=0
      exact congrArg (fun q => q.val) hz
    change numericalEntry (((Fin.cons (Sum.inr price) rows.1 : Fin ((PartialNativeCoordinates.rivalSet i kind 2).card+1)→Ici K.E.H⊕Icc K.E.R K.E.Rp)) (Fin.cast e l))≠(price:ℝ)
    exact Fin.cases (fun h=>(h rfl).elim) (fun q _=> h0 q) (Fin.cast e l) hz
  · let e := NativeFiberEnumerations.insert_card (PartialNativeCoordinates.rivalSet i kind 3) i
      (PartialNativeCoordinates.focal_not_mem_rivalSet i kind 3)
    have hz : Fin.cast e l≠0 := by
      intro hz
      apply hl
      apply Fin.ext
      change l.val=0
      exact congrArg (fun q => q.val) hz
    change numericalEntry (((Fin.cons (Sum.inr price) rows.2 : Fin ((PartialNativeCoordinates.rivalSet i kind 3).card+1)→Ici K.E.H⊕Icc K.E.R K.E.Rp)) (Fin.cast e l))≠(price:ℝ)
    exact Fin.cases (fun h=>(h rfl).elim) (fun q _=> h1 q) (Fin.cast e l) hz

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "E" => regions D P hdR H hUH
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "πA" => active D P t ht π
local notation "μA" => bidMarginal (Subtype.val πA)
local notation "μP" => bidMarginal (Subtype.val (π 2))
local notation "ρ" => OriginalPrivateSource.originalEntryLaw E P rfl t ht.le πL
  («partial» D P t ht π) πA upperBid hupperBid hfloor

variable [NullSingletonClass ((ProbabilityMeasure.toMeasure (Subtype.val (π 2))).map (fun x=>(x.2:ℝ)))]

lemma partial_real_singletons : NullSingletonClass ((ProbabilityMeasure.toMeasure μP).map Subtype.val) := by
  change NullSingletonClass (((ProbabilityMeasure.toMeasure (Subtype.val (π 2))).map Prod.snd).map Subtype.val)
  rw [Measure.map_map measurable_subtype_coe measurable_snd]
  change NullSingletonClass ((ProbabilityMeasure.toMeasure (Subtype.val (π 2))).map (fun x=>(x.2:ℝ)))
  infer_instance

theorem source_prior_levels (h : Fin (N+2)) :
    PositiveLevelNull (WeakProbability.toMeasure ((K).signalLaw h)) := by
  letI : NullSingletonClass ((ProbabilityMeasure.toMeasure (show ProbabilityMeasure (Icc (2-P.w) (2+P.w)×Icc (E).R (E).Rp) from Subtype.val («partial» D P t ht π))).map (fun x=>(x.2:ℝ))) := by
    change NullSingletonClass ((ProbabilityMeasure.toMeasure (Subtype.val (π 2))).map (fun x=>(x.2:ℝ)))
    infer_instance
  exact OriginalPrivatePositiveLevels.native_signal E P rfl t ht.le πL («partial» D P t ht π) πA
    upperBid hupperBid hfloor (N+1) D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) h

theorem source_entry_levels (price : Icc D.R D.Up) :
    ∀ᵐ r ∂(ProbabilityMeasure.toMeasure ρ),partialBid (signalEntry r)≠(price:ℝ) := by
  letI := partial_real_singletons D P t ht π
  have hh := entry_avoids (installOriginal D P t ht).upperShare μP (price:ℝ)
    (D.hR.trans_le price.2.1)
  have hs : MeasurableSet {s : Unit⊕Icc D.R D.Up | partialBid s≠(price:ℝ)} :=
    (measurableSet_eq_fun continuous_partialBid.measurable measurable_const).compl
  apply (ae_map_iff continuous_signalEntry.measurable.aemeasurable hs).mp
  have hm := ZeroNativeRowLaws.original_private_signal D P t ht hdR H hUH πL π upperBid hupperBid hfloor
  exact (congrArg (fun μ : Measure (Unit⊕Icc D.R D.Up) =>
    ∀ᵐ y ∂μ,partialBid y≠(price:ℝ)) hm).mpr hh

theorem source_entry_numerical (price : Icc D.R D.Up) :
    ∀ᵐ r ∂(ProbabilityMeasure.toMeasure ρ),numericalEntry r≠(price:ℝ) := by
  filter_upwards [source_entry_levels D P t ht hdR H hUH πL π upperBid hupperBid hfloor price]
    with r hr
  cases r with
  | inl v =>
    have hh : (price:ℝ)<(v:ℝ) := price.2.2.trans_lt ((E).Rp_lt_H.trans_le v.2)
    exact hh.ne'
  | inr b => exact hr

theorem source_raw_numerical (h : ℕ) (price : Icc D.R D.Up) :
    ∀ᵐ row ∂(ProbabilityMeasure.toMeasure (originalIid E h ρ)),∀ j,numericalEntry (row j)≠(price:ℝ) := by
  change ∀ᵐ row ∂Measure.pi (fun _ : Fin h=>(ProbabilityMeasure.toMeasure ρ)),∀ j,_
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval (fun _ : Fin h=>(ProbabilityMeasure.toMeasure ρ)) j).quasiMeasurePreserving.ae
    (source_entry_numerical D P t ht hdR H hUH πL π upperBid hupperBid hfloor price)

theorem source_raw_levels (h : ℕ) (price : Icc D.R D.Up) :
    ∀ᵐ row ∂(ProbabilityMeasure.toMeasure (originalIid E h ρ)),∀ j,partialBid (signal row j)≠(price:ℝ) := by
  change ∀ᵐ row ∂Measure.pi (fun _ : Fin h=>(ProbabilityMeasure.toMeasure ρ)),∀ j,_
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval (fun _ : Fin h=>(ProbabilityMeasure.toMeasure ρ)) j).quasiMeasurePreserving.ae
    (source_entry_levels D P t ht hdR H hUH πL π upperBid hupperBid hfloor price)

variable [NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (Subtype.val (active D P t ht π))))]

include t ht hdR H hUH πL π upperBid hupperBid hfloor hrare in
theorem source_common_receipts (A : ℕ) (h : Fin (N+2)) (price : Icc D.R D.Up) :
    ∀ᵐ common ∂Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μA)),∀ i,
      EqualReceiptLaw.receipt (c:=D.c) (ξ:=D.ξ) ((K).signalLaw h)
        (sortedBox common) i≠(price:ℝ) :=
  EqualSortedReceiptLaw.ae_sorted_receipts_ne D.hξ D.hξ1 ((K).signalLaw h)
    (source_prior_levels D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare h)
    μA (price:ℝ)

include hrare in
theorem source_regular (A : ℕ) (h : Fin (N+2)) (j : Fin h.val) (price : Icc D.R D.Up) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μA))).prod
      (ProbabilityMeasure.toMeasure (originalIid E h.val ρ)),
      policyInput (c:=D.c) (ξ:=D.ξ) (sortedBox x.1,(K).signalLaw h)
        (signal (Function.update x.2 j (Sum.inr price)))∈Regular D.ξ j := by
  have hc := (measurePreserving_fst
    (μ:=Measure.pi (fun _ : Fin A=>ProbabilityMeasure.toMeasure μA))
    (ν:=ProbabilityMeasure.toMeasure (originalIid E h.val ρ))).quasiMeasurePreserving.ae
      (source_common_receipts D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare A h price)
  have hp := (measurePreserving_snd
    (μ:=Measure.pi (fun _ : Fin A=>ProbabilityMeasure.toMeasure μA))
    (ν:=ProbabilityMeasure.toMeasure (originalIid E h.val ρ))).quasiMeasurePreserving.ae
      (source_raw_levels D P t ht hdR H hUH πL π upperBid hupperBid hfloor h.val price)
  filter_upwards [hc,hp] with x hc hp
  have hh := regular_update (c:=D.c) D.hR (sortedBox x.1) ((K).signalLaw h)
    (signal x.2) j price hc (fun l _=> hp l)
  have he : signal (Function.update x.2 j (Sum.inr price))=
      Function.update (signal x.2) j (Sum.inr price) := by
    funext l
    by_cases hl : l=j
    · subst l;simp only [signal,Function.update_self,signalEntry]
    · simp only [signal,Function.update_of_ne hl]
  exact (congrArg (fun row : Signal h.val D.R D.Up =>
    policyInput (c:=D.c) (ξ:=D.ξ) (sortedBox x.1,(K).signalLaw h) row∈Regular D.ξ j) he).mpr hh

end FCAppendix.Affine.Tail04.ZeroPrivateRegularity
