import FCAppendix.Affine.Tail04.NativeHighExperiment
import FCAppendix.Affine.Tail04.OrderedNativePayoffBindings

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffExperiment
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeSamplerCountLaw NativeHighExperiment
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy PrivateRowSorting SortedAllNoise
open scoped BigOperators

variable {m c A : ℕ} (K : NativeLocalPolicy.Data m c)
  (ρ : ProbabilityMeasure (Ici K.E.H ⊕ Icc K.E.R K.E.Rp))
  (hrows : ∀ H : Fin (m+1),K.originalPrivateRow H=sortedOriginalIid K.E H.val ρ)
  (H0 H1 : Fin (m+1))

abbrev Pairs :=
  (Row H0.val K.E.R K.E.Rp K.E.H×unitInterval)×
    (Row H1.val K.E.R K.E.Rp K.E.H×unitInterval)

def swapPairs (z : Pairs K H0 H1) : Pairs K H1 H0 := z.swap

lemma measurable_swapPairs : Measurable (swapPairs K H0 H1) := measurable_swap

theorem swapPairs_preserves : MeasurePreserving (swapPairs K H0 H1)
    (pairLaw K H0 H1) (pairLaw K H1 H0) :=
  Measure.measurePreserving_swap

variable (Q : PublicScenario.Data) (b : Fin A → Icc (1:ℝ) K.E.U) (i : Fin A)

def pairedOutcome (lowPresent : Bool) (z : unitInterval×Pairs K H0 H1) : Fin 3 :=
  let q := NativeHighExperiment.choice K H0 H1 Q b lowPresent z.1
  scenarioOutcome K A H0 H1 (sortedBox b) (focalRank (fun j => (b j:ℝ)) i)
    (q.1,(q.2,z.2))

lemma measurable_pairedOutcome (lowPresent : Bool) :
    Measurable (pairedOutcome K H0 H1 Q b i lowPresent) :=
  (measurable_scenarioOutcome K A H0 H1 (sortedBox b) _).comp
    (((NativeHighExperiment.measurable_choice K H0 H1 Q b lowPresent).fst.comp
      measurable_fst).prodMk
      (((NativeHighExperiment.measurable_choice K H0 H1 Q b lowPresent).snd.comp
        measurable_fst).prodMk measurable_snd))

lemma measurable_pairedOutcome_joint (lowPresent : Bool) :
    Measurable (fun z : (Fin A → Icc (1:ℝ) K.E.U)×
      (unitInterval×Pairs K H0 H1) =>
        pairedOutcome K H0 H1 Q z.1 i lowPresent z.2) := by
  let J := (Fin A → Icc (1:ℝ) K.E.U)×(unitInterval×Pairs K H0 H1)
  let bs : J → Fin A → Icc (1:ℝ) K.E.U := fun z => sortedBox z.1
  let ix : J → Fin A := fun z => focalRank (fun j => (z.1 j:ℝ)) i
  let q : J → Scenario A×unitInterval := fun z =>
    NativeHighExperiment.choice K H0 H1 Q z.1 lowPresent z.2.1
  let rp : J → Pairs K H0 H1 := fun z => z.2.2
  let p : J → Parameters A H0.val K.E.R K.E.Rp K.E.U :=
    fun z => (((q z).1,bs z),(K.signalLaw H0,(q z).2))
  have hbs : Measurable bs := continuous_sortedBox.measurable.comp measurable_fst
  have hix : Measurable ix := (measurable_focalRank i).comp
    (measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp measurable_fst).subtype_val)
  have hq : Measurable q := by
    cases lowPresent
    · exact measurable_const
    · exact (PublicScenario.measurable_draw Q A).comp
        (((measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp hbs).subtype_val).prodMk
          measurable_const).prodMk measurable_snd.fst)
  have hrp : Measurable rp := measurable_snd.snd
  have hp : Measurable p := (hq.fst.prodMk hbs).prodMk (measurable_const.prodMk hq.snd)
  have h0 := (K.zeroSampler_measurable A H0 H1).comp
    ((hp.prodMk hrp.fst.fst).prodMk hrp.fst.snd)
  have h1 := (K.oneSampler_measurable A H0 H1).comp
    ((hp.prodMk hrp.snd.fst).prodMk hrp.snd.snd)
  have ha0 : Measurable (fun z : J =>
      decide (Sum.inl (ix z)∈K.zeroSampler A H0 H1 (p z,(rp z).1.1) (rp z).1.2)) :=
    (measurable_of_countable (fun w : Fin A×Finset (Fin A⊕Fin H0.val) =>
      decide (Sum.inl w.1∈w.2))).comp (hix.prodMk h0)
  have ha1 : Measurable (fun z : J =>
      decide (Sum.inl (ix z)∈K.oneSampler A H0 H1 (p z,(rp z).2.1) (rp z).2.2)) :=
    (measurable_of_countable (fun w : Fin A×Finset (Fin A⊕Fin H1.val) =>
      decide (Sum.inl w.1∈w.2))).comp (hix.prodMk h1)
  exact (measurable_of_countable boolPairCount).comp (ha0.prodMk ha1)

def pairedLaw (lowPresent : Bool) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (pairLaw K H0 H1))
    (pairedOutcome K H0 H1 Q b i lowPresent)
    (measurable_pairedOutcome K H0 H1 Q b i lowPresent)

include hrows in

theorem pairedLaw_eq_nativeHighLaw (lowPresent : Bool) :
    pairedLaw K H0 H1 Q b i lowPresent=
      NativeHighExperiment.law K ρ H0 H1 Q b i lowPresent := by
  have hpres := (MeasurePreserving.id (volume : Measure unitInterval)).prod
    (NativeHighExperiment.sortedPairs_preserves K ρ hrows H0 H1)
  have he := FiniteLaw.ofMeasure_comp_measurePreserving
    ((volume : Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))
    ((volume : Measure unitInterval).prod (pairLaw K H0 H1))
    (Prod.map id (NativeHighExperiment.sortedPairs K H0 H1)) hpres
    (pairedOutcome K H0 H1 Q b i lowPresent)
    (measurable_pairedOutcome K H0 H1 Q b i lowPresent)
  exact he.symm

attribute [local irreducible] pairedOutcome

def orderedOutcome (lowPresent : Bool) (z : unitInterval×Pairs K H0 H1) : Fin 3 :=
  if H0.val≤H1.val then pairedOutcome K H0 H1 Q b i lowPresent z
  else pairedOutcome K H1 H0 Q b i lowPresent (z.1,swapPairs K H0 H1 z.2)

lemma measurable_orderedOutcome (lowPresent : Bool) :
    Measurable (orderedOutcome K H0 H1 Q b i lowPresent) := by
  unfold orderedOutcome
  split
  · exact measurable_pairedOutcome K H0 H1 Q b i lowPresent
  · exact (measurable_pairedOutcome K H1 H0 Q b i lowPresent).comp
      (measurable_fst.prodMk ((measurable_swapPairs K H0 H1).comp measurable_snd))

def orderedLaw (lowPresent : Bool) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (pairLaw K H0 H1))
    (orderedOutcome K H0 H1 Q b i lowPresent)
    (measurable_orderedOutcome K H0 H1 Q b i lowPresent)

theorem orderedLaw_eq (lowPresent : Bool) :
    orderedLaw K H0 H1 Q b i lowPresent=
      if H0.val≤H1.val then pairedLaw K H0 H1 Q b i lowPresent
      else pairedLaw K H1 H0 Q b i lowPresent := by
  by_cases h : H0.val≤H1.val
  · have ho : orderedOutcome K H0 H1 Q b i lowPresent=pairedOutcome K H0 H1 Q b i lowPresent := by
      funext z
      exact if_pos h
    simp only [orderedLaw,if_pos h,ho,pairedLaw]
  · rw [if_neg h]
    have ho : orderedOutcome K H0 H1 Q b i lowPresent=
        pairedOutcome K H1 H0 Q b i lowPresent ∘ Prod.map id (swapPairs K H0 H1) := by
      funext z
      exact if_neg h
    have hpres := (MeasurePreserving.id (volume : Measure unitInterval)).prod
      (swapPairs_preserves K H0 H1)
    have he := FiniteLaw.ofMeasure_comp_measurePreserving
      ((volume : Measure unitInterval).prod (pairLaw K H0 H1))
      ((volume : Measure unitInterval).prod (pairLaw K H1 H0))
      (Prod.map id (swapPairs K H0 H1)) hpres
      (pairedOutcome K H1 H0 Q b i lowPresent)
      (measurable_pairedOutcome K H1 H0 Q b i lowPresent)
    simpa only [orderedLaw,ho,pairedLaw] using! he

include hrows in
theorem orderedLaw_eq_nativeHighLaw (lowPresent : Bool) :
    orderedLaw K H0 H1 Q b i lowPresent=
      if H0.val≤H1.val then NativeHighExperiment.law K ρ H0 H1 Q b i lowPresent
      else NativeHighExperiment.law K ρ H1 H0 Q b i lowPresent := by
  rw [orderedLaw_eq]
  split <;> exact pairedLaw_eq_nativeHighLaw K ρ hrows _ _ Q b i lowPresent

def rawOutcome (lowPresent : Bool)
    (z : unitInterval×RawPayload K H0 H1) : Fin 3 :=
  orderedOutcome K H0 H1 Q b i lowPresent
    (z.1,NativeHighExperiment.sortedPairs K H0 H1 z.2)

lemma measurable_rawOutcome (lowPresent : Bool) :
    Measurable (rawOutcome K H0 H1 Q b i lowPresent) :=
  (measurable_orderedOutcome K H0 H1 Q b i lowPresent).comp
    (measurable_fst.prodMk
      ((NativeHighExperiment.measurable_sortedPairs K H0 H1).comp measurable_snd))

lemma measurable_orderedOutcome_joint (lowPresent : Bool) :
    Measurable (fun z : (Fin A → Icc (1:ℝ) K.E.U)×(unitInterval×Pairs K H0 H1) =>
      orderedOutcome K H0 H1 Q z.1 i lowPresent z.2) := by
  unfold orderedOutcome
  split
  · exact measurable_pairedOutcome_joint K H0 H1 Q i lowPresent
  · have ht : Measurable (fun z : (Fin A→Icc (1:ℝ) K.E.U)×(unitInterval×Pairs K H0 H1) =>
        (z.1,(z.2.1,swapPairs K H0 H1 z.2.2))) :=
      measurable_fst.prodMk (measurable_snd.fst.prodMk
        ((measurable_swapPairs K H0 H1).comp measurable_snd.snd))
    exact (measurable_pairedOutcome_joint K H1 H0 Q i lowPresent).comp ht

lemma measurable_rawOutcome_joint (lowPresent : Bool) :
    Measurable (fun z : (Fin A → Icc (1:ℝ) K.E.U)×
      (unitInterval×RawPayload K H0 H1) =>
        rawOutcome K H0 H1 Q z.1 i lowPresent z.2) := by
  have ht : Measurable (fun z : (Fin A→Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1) =>
      (z.1,(z.2.1,NativeHighExperiment.sortedPairs K H0 H1 z.2.2))) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk
      ((NativeHighExperiment.measurable_sortedPairs K H0 H1).comp measurable_snd.snd))
  exact (measurable_orderedOutcome_joint K H0 H1 Q i lowPresent).comp ht

def rawLaw (lowPresent : Bool) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))
    (rawOutcome K H0 H1 Q b i lowPresent)
    (measurable_rawOutcome K H0 H1 Q b i lowPresent)

include hrows in
theorem rawLaw_eq_orderedLaw (lowPresent : Bool) :
    rawLaw K ρ H0 H1 Q b i lowPresent=orderedLaw K H0 H1 Q b i lowPresent := by
  exact FiniteLaw.ofMeasure_comp_measurePreserving _ _
    (Prod.map id (NativeHighExperiment.sortedPairs K H0 H1))
    ((MeasurePreserving.id (volume : Measure unitInterval)).prod
      (NativeHighExperiment.sortedPairs_preserves K ρ hrows H0 H1))
    (orderedOutcome K H0 H1 Q b i lowPresent)
    (measurable_orderedOutcome K H0 H1 Q b i lowPresent)

include hrows in
theorem rawLaw_eq_nativeHighLaw (lowPresent : Bool) :
    rawLaw K ρ H0 H1 Q b i lowPresent=
      if H0.val≤H1.val then NativeHighExperiment.law K ρ H0 H1 Q b i lowPresent
      else NativeHighExperiment.law K ρ H1 H0 Q b i lowPresent := by
  rw [rawLaw_eq_orderedLaw K ρ hrows,
    orderedLaw_eq_nativeHighLaw K ρ hrows]

include hrows in

theorem rawLaw_statistic (lowPresent : Bool) (f : Fin 3 → ℝ) :
    (rawLaw K ρ H0 H1 Q b i lowPresent).expect f=
      if H0.val≤H1.val then
        (NativeHighExperiment.law K ρ H0 H1 Q b i lowPresent).expect f
      else (NativeHighExperiment.law K ρ H1 H0 Q b i lowPresent).expect f := by
  rw [rawLaw_eq_nativeHighLaw K ρ hrows]
  split <;> rfl

def perRegime (reg low : Bool) [Nonempty (Fin A)] : CountLaw 2 :=
  if H0.val≤H1.val then NativeHighExperiment.perRegime K H0 H1 Q b i reg low
  else NativeHighExperiment.perRegime K H1 H0 Q b i reg low

variable (hc : Q.c=c) (hξ : Q.ξ=K.ξ)
  (hν0 : Q.marksLaw H0.val=K.marksLaw H0)
  (hν1 : Q.marksLaw H1.val=K.marksLaw H1) [Nonempty (Fin A)]

include hrows hc hξ hν0 hν1 in
theorem rawLaw_regime (low : Bool) :
    rawLaw K ρ H0 H1 Q b i low=
      FiniteLaw.finiteMix (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one)
        (fun reg => perRegime K H0 H1 Q b i reg low) := by
  rw [rawLaw_eq_nativeHighLaw K ρ hrows]
  by_cases h : H0.val≤H1.val
  · simp only [if_pos h,perRegime]
    exact NativeHighExperiment.law_regime K ρ hrows H0 H1 Q b i hc hξ hν0 hν1 low
  · simp only [if_neg h,perRegime]
    exact NativeHighExperiment.law_regime K ρ hrows H1 H0 Q b i hc hξ hν1 hν0 low

end FCAppendix.Affine.Tail04.OrderedNativePayoffExperiment
