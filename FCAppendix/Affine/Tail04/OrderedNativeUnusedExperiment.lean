import FCAppendix.Affine.Tail04.OrderedNativeUnusedCoordinates
import FCAppendix.Affine.Tail04.NativeUnusedReference
import FCAppendix.Affine.Tail04.OrderedNativePayoffExperiment

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeUnusedExperiment
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeHighExperiment NativeSamplerCountLaw
open NativeObservationPair NativeCountCoordinates NativeUnusedCoordinates
open PartialNativeCoordinates NativeActiveFiberCoordinates
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy LocalHighCommon MenuError
open Hybrid NativeFlag NativeMenuReports
open OrderedNativePayoffExperiment (Pairs swapPairs measurable_swapPairs swapPairs_preserves)

section Numerical
variable {m c A : ℕ} (K : NativeLocalPolicy.Data m c)
  (H0 H1 : Fin (m+1)) (Q : PublicScenario.Data)

def Good (b : Fin A→Icc (1:ℝ) K.E.U) (u : unitInterval) : Prop :=
  if (H0).val≤(H1).val then NativeUnusedExperiment.Good K H0 H1 Q b u
  else NativeUnusedExperiment.Good K H1 H0 Q b u

lemma measurableSet_good : MeasurableSet
    {z : (Fin A→Icc (1:ℝ) K.E.U)×unitInterval | Good K H0 H1 Q z.1 z.2} := by
  unfold Good
  split <;> exact NativeUnusedExperiment.measurableSet_good K _ _ Q

def pairedOutcome (b : Fin A→Icc (1:ℝ) K.E.U) (y : ℝ)
    (z : unitInterval×Pairs K H0 H1) : Fin 3 :=
  originalPairCount (K.zeroFocal A H0 H1) (K.oneFocal A H0 H1)
    (NativeUnusedExperiment.parameter K H0 H1 Q b z.1,y) none none z.2

lemma measurable_pairedOutcome_joint (y : ℝ) :
    Measurable (fun z : (Fin A→Icc (1:ℝ) K.E.U)×(unitInterval×Pairs K H0 H1) =>
      pairedOutcome K H0 H1 Q z.1 y z.2) := by
  let T := (Fin A→Icc (1:ℝ) K.E.U)×(unitInterval×Pairs K H0 H1)
  let p : T→Parameters A (H0).val K.E.R K.E.Rp K.E.U×ℝ :=
    fun z => (NativeUnusedExperiment.parameter K H0 H1 Q z.1 z.2.1,y)
  let s : T→Pairs K H0 H1 := fun z => z.2.2
  have hp : Measurable p :=
    ((NativeUnusedExperiment.measurable_parameter K H0 H1 Q).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_const
  have hs : Measurable s := measurable_snd.snd
  have h0 := (K.measurable_zeroFocal A H0 H1).comp
    ((hp.prodMk hs.fst.fst).prodMk hs.fst.snd)
  have h1 := (K.measurable_oneFocal A H0 H1).comp
    ((hp.prodMk hs.snd.fst).prodMk hs.snd.snd)
  have ha0 := (measurable_of_countable (fun S : Finset (FocalInsertion.Target A (H0).val) =>
    decide (none∈S))).comp h0
  have ha1 := (measurable_of_countable (fun S : Finset (FocalInsertion.Target A (H1).val) =>
    decide (none∈S))).comp h1
  exact (measurable_of_countable boolPairCount).comp (ha0.prodMk ha1)

attribute [local irreducible] pairedOutcome

lemma measurable_pairedOutcome (b : Fin A→Icc (1:ℝ) K.E.U) (y : ℝ) :
    Measurable (pairedOutcome K H0 H1 Q b y) :=
  (measurable_pairedOutcome_joint K H0 H1 Q y).comp
    (measurable_const.prodMk measurable_id)

def orderedOutcome (b : Fin A→Icc (1:ℝ) K.E.U) (y : ℝ)
    (z : unitInterval×Pairs K H0 H1) : Fin 3 :=
  if (H0).val≤(H1).val then pairedOutcome K H0 H1 Q b y z
  else pairedOutcome K H1 H0 Q b y (z.1,swapPairs K H0 H1 z.2)

lemma measurable_orderedOutcome_joint (y : ℝ) :
    Measurable (fun z : (Fin A→Icc (1:ℝ) K.E.U)×(unitInterval×Pairs K H0 H1) =>
      orderedOutcome K H0 H1 Q z.1 y z.2) := by
  unfold orderedOutcome
  split
  · exact measurable_pairedOutcome_joint K H0 H1 Q y
  · exact (measurable_pairedOutcome_joint K H1 H0 Q y).comp
      (measurable_fst.prodMk (measurable_snd.fst.prodMk
        ((measurable_swapPairs K H0 H1).comp measurable_snd.snd)))

def outcome (b : Fin A→Icc (1:ℝ) K.E.U) (y : ℝ)
    (z : unitInterval×RawPayload K H0 H1) : Fin 3 :=
  orderedOutcome K H0 H1 Q b y (z.1,sortedPairs K H0 H1 z.2)

attribute [local irreducible] orderedOutcome

lemma measurable_outcome_joint (y : ℝ) :
    Measurable (fun z : (Fin A→Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1) =>
      outcome K H0 H1 Q z.1 y z.2) :=
  (measurable_orderedOutcome_joint K H0 H1 Q y).comp
    (measurable_fst.prodMk (measurable_snd.fst.prodMk
      ((measurable_sortedPairs K H0 H1).comp measurable_snd.snd)))

attribute [local irreducible] outcome

lemma measurable_outcome (b : Fin A→Icc (1:ℝ) K.E.U) (y : ℝ) :
    Measurable (outcome K H0 H1 Q b y) :=
  (measurable_outcome_joint K H0 H1 Q y).comp (measurable_const.prodMk measurable_id)

variable (ρ : ProbabilityMeasure (Ici K.E.H⊕Icc K.E.R K.E.Rp))
  (hrows : ∀H : Fin (m+1),K.originalPrivateRow H=PrivateRowSorting.sortedOriginalIid K.E H.val ρ)

def rowCount (b : Fin A→Icc (1:ℝ) K.E.U) (y : ℝ) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))
    (outcome K H0 H1 Q b y) (measurable_outcome K H0 H1 Q b y)

include hrows in
theorem rowCount_eq (b : Fin A→Icc (1:ℝ) K.E.U) (y : ℝ) :
    rowCount K H0 H1 Q ρ b y=
      if (H0).val≤(H1).val then NativeUnusedReference.rowCount K H0 H1 Q ρ b y
      else NativeUnusedReference.rowCount K H1 H0 Q ρ b y := by
  let paired (J0 J1 : Fin (m+1)) : CountLaw 2 :=
    FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (pairLaw K J0 J1))
      (pairedOutcome K J0 J1 Q b y) (measurable_pairedOutcome K J0 J1 Q b y)
  have hp (J0 J1 : Fin (m+1)) : paired J0 J1=
      NativeUnusedReference.rowCount K J0 J1 Q ρ b y := by
    symm
    have hh := FiniteLaw.ofMeasure_comp_measurePreserving _ _
      (Prod.map id (sortedPairs K J0 J1))
      ((MeasurePreserving.id (volume : Measure unitInterval)).prod
        (sortedPairs_preserves K ρ hrows J0 J1))
      (pairedOutcome K J0 J1 Q b y) (measurable_pairedOutcome K J0 J1 Q b y)
    calc
      _=FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (rawPayloadLaw K ρ J0 J1))
          ((pairedOutcome K J0 J1 Q b y) ∘ Prod.map id (sortedPairs K J0 J1))
          ((measurable_pairedOutcome K J0 J1 Q b y).comp
            (((MeasurePreserving.id (volume : Measure unitInterval)).prod
              (sortedPairs_preserves K ρ hrows J0 J1)).measurable)) := by
        apply FiniteLaw.ofMeasure_congr_ae
        exact ae_of_all _ fun z=>by
          unfold NativeUnusedExperiment.outcome pairedOutcome
          rfl
      _=paired J0 J1 := hh
  by_cases h : (H0).val≤(H1).val
  · rw [if_pos h]
    apply FiniteLaw.ofMeasure_congr_ae
    exact ae_of_all _ fun z=>by
      unfold outcome orderedOutcome
      rw [if_pos h]
      unfold pairedOutcome NativeUnusedExperiment.outcome
      rfl
  · rw [if_neg h,←hp H1 H0]
    have hpres := ((MeasurePreserving.id (volume : Measure unitInterval)).prod
      (swapPairs_preserves K H0 H1)).comp
      ((MeasurePreserving.id (volume : Measure unitInterval)).prod
        (sortedPairs_preserves K ρ hrows H0 H1))
    have hh := FiniteLaw.ofMeasure_comp_measurePreserving _ _
      (fun z : unitInterval×RawPayload K H0 H1 =>
        (z.1,swapPairs K H0 H1 (sortedPairs K H0 H1 z.2))) hpres
      (pairedOutcome K H1 H0 Q b y) (measurable_pairedOutcome K H1 H0 Q b y)
    calc
      _=FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))
          ((pairedOutcome K H1 H0 Q b y) ∘ (fun z : unitInterval×RawPayload K H0 H1 =>
            (z.1,swapPairs K H0 H1 (sortedPairs K H0 H1 z.2))))
          ((measurable_pairedOutcome K H1 H0 Q b y).comp hpres.measurable) := by
        apply FiniteLaw.ofMeasure_congr_ae
        exact ae_of_all _ fun z=>by
          unfold outcome orderedOutcome
          rw [if_neg h]
          rfl
      _=paired H1 H0 := hh
end Numerical

section OriginalNative
variable {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c)
  (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hQ : ∀A,K.publicChoice A=PublicScenario.localChoice K.E Q μL A)
  (Γ : FiniteGame (N+1) 2 c Seed) (hpolicy : Γ.policy=OrderedNativePolicy.policy K)
  (i : Fin (N+1)) (kind : Fin N→Fin 4) (ω : Sample (N+1) 2 Seed)
  (hr : ∀r : Fin N,MenuAction K.E (ω.1.1 (i.succAbove r)).1.2)
  (hk : rivalKinds K.E i ω.1=kind)
  (b : ℝ) (hb0 : 0≤b) (hb : K.E.localTag (some b)=1) (hbo : b∉Icc (1:ℝ) K.E.U)
local notation "H0" => K.finiteCount (rivalSet i kind 2)
local notation "H1" => K.finiteCount (rivalSet i kind 3)
local notation "row" => commonRow K.E i kind (fun r => (Prod.fst (Prod.fst ω)) (i.succAbove r))
local notation "payload" => ((privateRowRaw K.E i kind 2 (fun r => (Prod.fst (Prod.fst ω)) (i.succAbove r)),
  privateRowRaw K.E i kind 3 (fun r => (Prod.fst (Prod.fst ω)) (i.succAbove r))),(Prod.snd (Prod.fst ω),Prod.snd ω))

include hQ hr hk hb hbo in
lemma listPair_on_good (j : Fin 2) (u : unitInterval)
    (hseed : ∀s : Fin 2,seedOnList μL (K.E.roleList 0 (presentList ω.1 i b s))=some u)
    (hg : NativeUnusedExperiment.Good K
      (K.finiteCount (rivalSet i kind (NativeContinuation.upperTag j)))
      (K.finiteCount (rivalSet i kind (NativeContinuation.upperTag (Hybrid.otherProposer j)))) Q row u) :
    NativeCountCoordinates.listPairCount K (presentList ω.1 i b j)
      (presentList ω.1 i b (Hybrid.otherProposer j)) i (ω.1.2 j) (ω.1.2 (Hybrid.otherProposer j))=
      pairedOutcome K
        (K.finiteCount (rivalSet i kind (NativeContinuation.upperTag j)))
        (K.finiteCount (rivalSet i kind (NativeContinuation.upperTag (Hybrid.otherProposer j)))) Q row b
        (u,((PrivateRowSorting.sortRow K.E _
          (privateRowRaw K.E i kind (NativeContinuation.upperTag j) (fun r => ω.1.1 (i.succAbove r))),
          (ω.1.2 j).1),(PrivateRowSorting.sortRow K.E _
          (privateRowRaw K.E i kind (NativeContinuation.upperTag (Hybrid.otherProposer j))
            (fun r => ω.1.1 (i.succAbove r))),(ω.1.2 (Hybrid.otherProposer j)).1))) := by
  have hp := OrderedNativeUnusedCoordinates.sampler_pair K Q μL
    (fun A z => congrFun (hQ A) z) i kind ω.1 hr hk b hb hbo j u hseed hg
  unfold NativeCountCoordinates.listPairCount pairedOutcome originalPairCount localAccept
  apply congrArg boolPairCount
  apply Prod.ext
  · exact Bool.decide_congr (hp.1 (ω.1.2 j))
  · exact Bool.decide_congr (hp.2 (ω.1.2 (Hybrid.otherProposer j)))

include hQ hpolicy hr hk hb hbo in
theorem original_count_on_good (u : unitInterval)
    (hseed : ∀j : Fin 2,seedOnList μL (K.E.roleList 0 (presentList ω.1 i b j))=some u)
    (hg : Good K H0 H1 Q row u) :
    focalCount Γ i (RawRoutes.action b hb0 2) ω=outcome K H0 H1 Q row b (u,payload) := by
  let L : Fin 2→LocalList (N+1) := fun j => presentList ω.1 i b j
  have hc : K.E.Compatible (L 0) (L 1) :=
    OrderedNativeUnusedCoordinates.compatible K i ω.1 hr b hb
  have hs := raw_ids K.E i ω.1 hr b hb 0
  simp only [hk,NativeContinuation.upperTag,Hybrid.otherProposer,ite_true] at hs
  have hz : OrderedNativePolicy.role K.E 0 (L 0)=0 ↔ (H0).val≤(H1).val := by
    rw [OrderedNativeCountCoordinates.role_zero_iff,←LocalCoordinates.ids_card,
      K.E.otherPrivateCount_eq_missing,hs.2.2.1,hs.2.2.2]
    rfl
  have ho (j : Fin 2) : observe (deviated i (RawRoutes.action b hb0 2) ω) j=L j :=
    observe_deviated_of_mem i (RawRoutes.action b hb0 2) ω j
      (by simp [RawRoutes.action,Hybrid.firstK_full_two])
  unfold focalCount
  rw [hpolicy,OrderedNativeCountCoordinates.boundedCount_eq_pair,ho 0,ho 1,
    OrderedNativeCountCoordinates.pair_eq_restored K hc]
  by_cases h : (H0).val≤(H1).val
  · have hz0 := hz.mpr h
    have hg0 : NativeUnusedExperiment.Good K H0 H1 Q row u := by
      simpa only [Good,if_pos h] using hg
    simp only [OrderedNativeCountCoordinates.zeroList,OrderedNativeCountCoordinates.oneList,
      OrderedNativeCountCoordinates.zeroSeed,OrderedNativeCountCoordinates.oneSeed,if_pos hz0]
    simpa only [outcome,orderedOutcome,if_pos h,NativeHighExperiment.sortedPairs,
      NativeContinuation.upperTag,Hybrid.otherProposer,ite_true] using!
      listPair_on_good K Q μL hQ i kind ω hr hk b hb hbo 0 u hseed hg0
  · have hz0 : OrderedNativePolicy.role K.E 0 (L 0)≠0 := fun hh => h (hz.mp hh)
    have hg1 : NativeUnusedExperiment.Good K H1 H0 Q row u := by
      simpa only [Good,if_neg h] using hg
    simp only [OrderedNativeCountCoordinates.zeroList,OrderedNativeCountCoordinates.oneList,
      OrderedNativeCountCoordinates.zeroSeed,OrderedNativeCountCoordinates.oneSeed,if_neg hz0]
    simpa only [outcome,orderedOutcome,if_neg h,swapPairs,NativeHighExperiment.sortedPairs,
      NativeContinuation.upperTag,Hybrid.otherProposer,if_neg (by decide : (1:Fin 2)≠0),
      Prod.swap_prod_mk] using!
      listPair_on_good K Q μL hQ i kind ω hr hk b hb hbo 1 u hseed hg1

include hQ hpolicy hr hk hb hbo in
theorem original_count_error (u : unitInterval)
    (hseed : ∀j : Fin 2,seedOnList μL (K.E.roleList 0 (presentList ω.1 i b j))=some u)
    (f : Fin 3→ℝ) :
    |f (focalCount Γ i (RawRoutes.action b hb0 2) ω)-f (outcome K H0 H1 Q row b (u,payload))|≤
      2*MenuError.oscillation f*(if Good K H0 H1 Q row u then 0 else 1) := by
  by_cases hg : Good K H0 H1 Q row u
  · rw [original_count_on_good K Q μL hQ Γ hpolicy i kind ω hr hk b hb0 hb hbo u hseed hg]
    simp [hg]
  · have hh := count_expect_difference_bound
      (FiniteLaw.dirac (focalCount Γ i (RawRoutes.action b hb0 2) ω))
      (FiniteLaw.dirac (outcome K H0 H1 Q row b (u,payload))) f
    simpa only [FiniteLaw.expect_dirac,if_neg hg,mul_one] using hh
end OriginalNative
end FCAppendix.Affine.Tail04.OrderedNativeUnusedExperiment
