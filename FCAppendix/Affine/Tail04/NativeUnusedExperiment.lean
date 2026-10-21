import FCAppendix.Affine.Tail04.NativeUnusedCoordinates
import FCAppendix.Affine.Tail04.UnusedFocalCountError
import FCAppendix.Affine.Tail04.NativeHighExperiment

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeUnusedExperiment
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeHighExperiment NativeSamplerCountLaw
open NativeUnusedCoordinates NativeObservationPair NativeCountCoordinates
open PartialNativeCoordinates NativeActiveFiberCoordinates
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy LocalHighCommon
open MenuError UnusedFocalCountError Hybrid NativeFlag NativeMenuReports
open scoped BigOperators

section Numerical
variable {m c A : ℕ} (K : NativeLocalPolicy.Data m c)
  (H0 H1 : Fin (m+1)) (Q : PublicScenario.Data)

def parameter (b : Fin A→ Icc (1:ℝ) K.E.U) (u : unitInterval) :
    Parameters A H0.val K.E.R K.E.Rp K.E.U :=
  PartialNativePublicWeight.drawnParameter K Q A H0 H1 (SortedAllNoise.sortedBox b) u

lemma measurable_parameter : Measurable
    (fun z : (Fin A→ Icc (1:ℝ) K.E.U)×unitInterval => parameter K H0 H1 Q z.1 z.2) :=
  (PartialNativePublicWeight.measurable_drawnParameter K Q A H0 H1).comp
    (SortedAllNoise.continuous_sortedBox.measurable.prodMap measurable_id)

def Good (b : Fin A→ Icc (1:ℝ) K.E.U) (u : unitInterval) : Prop :=
  K.FocalUse A H0 H1 (parameter K H0 H1 Q b u)

lemma measurableSet_good : MeasurableSet
    {z : (Fin A→ Icc (1:ℝ) K.E.U)×unitInterval | Good K H0 H1 Q z.1 z.2} :=
  (K.measurableSet_focalUse A H0 H1).preimage (measurable_parameter K H0 H1 Q)

def outcome (b : Fin A→ Icc (1:ℝ) K.E.U) (y : ℝ)
    (z : unitInterval×RawPayload K H0 H1) : Fin 3 :=
  originalPairCount (K.zeroFocal A H0 H1) (K.oneFocal A H0 H1)
    (parameter K H0 H1 Q b z.1,y) none none (sortedPairs K H0 H1 z.2)

lemma measurable_outcome_joint (y : ℝ) :
    Measurable (fun z : (Fin A→ Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1) =>
      outcome K H0 H1 Q z.1 y z.2) := by
  let T := (Fin A→ Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1)
  let p : T→ Parameters A H0.val K.E.R K.E.Rp K.E.U×ℝ :=
    fun z => (parameter K H0 H1 Q z.1 z.2.1,y)
  let s : T→(Row H0.val K.E.R K.E.Rp K.E.H×unitInterval)×
      (Row H1.val K.E.R K.E.Rp K.E.H×unitInterval) :=
    fun z => sortedPairs K H0 H1 z.2.2
  have hp : Measurable p :=
    ((measurable_parameter K H0 H1 Q).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      measurable_const
  have hs : Measurable s := (measurable_sortedPairs K H0 H1).comp measurable_snd.snd
  have h0 := (K.measurable_zeroFocal A H0 H1).comp
    ((hp.prodMk hs.fst.fst).prodMk hs.fst.snd)
  have h1 := (K.measurable_oneFocal A H0 H1).comp
    ((hp.prodMk hs.snd.fst).prodMk hs.snd.snd)
  have ha0 := (measurable_of_countable (fun S : Finset (FocalInsertion.Target A H0.val) =>
    decide (none∈S))).comp h0
  have ha1 := (measurable_of_countable (fun S : Finset (FocalInsertion.Target A H1.val) =>
    decide (none∈S))).comp h1
  exact (measurable_of_countable boolPairCount).comp (ha0.prodMk ha1)

attribute [local irreducible] outcome

lemma measurable_outcome (b : Fin A→ Icc (1:ℝ) K.E.U) (y : ℝ) :
    Measurable (outcome K H0 H1 Q b y) :=
  (measurable_outcome_joint K H0 H1 Q y).comp
    ((show Measurable (fun _ : unitInterval×RawPayload K H0 H1 => b)
      from measurable_const).prodMk measurable_id)

variable (ρ : ProbabilityMeasure (Ici K.E.H⊕Icc K.E.R K.E.Rp))
  (hrows : ∀ H : Fin (m+1),K.originalPrivateRow H=PrivateRowSorting.sortedOriginalIid K.E H.val ρ)

include hrows in
theorem private_count (b : Fin A→ Icc (1:ℝ) K.E.U) (y : ℝ) (u : unitInterval) :
    FiniteLaw.ofMeasure (rawPayloadLaw K ρ H0 H1)
      (fun z => outcome K H0 H1 Q b y (u,z))
      ((measurable_outcome K H0 H1 Q b y).comp (measurable_const.prodMk measurable_id))=
      originalIndependentCountLaw (K.zeroFocal A H0 H1) (K.oneFocal A H0 H1)
        (K.measurable_zeroFocal A H0 H1) (K.measurable_oneFocal A H0 H1)
        (parameter K H0 H1 Q b u,y) (K.originalPrivateRow H0) (K.originalPrivateRow H1) none none := by
  unfold outcome
  exact FiniteLaw.ofMeasure_comp_measurePreserving _ _ (sortedPairs K H0 H1)
    (sortedPairs_preserves K ρ hrows H0 H1)
    (originalPairCount (K.zeroFocal A H0 H1) (K.oneFocal A H0 H1)
      (parameter K H0 H1 Q b u,y) none none)
    (measurable_originalPairCount _ _ (K.measurable_zeroFocal A H0 H1)
      (K.measurable_oneFocal A H0 H1) _ _ _)

include hrows in
theorem private_count_on_guard (b : Fin A→ Icc (1:ℝ) K.E.U) (y : ℝ) (u : unitInterval)
    (hg : FocalInsertion.PublicGuard A H0.val H1.val c K.ξ K.E.U K.E.R K.E.Rp
      (K.marksLaw H0) (K.marksLaw H1) (parameter K H0 H1 Q b u)) :
    let p:=parameter K H0 H1 Q b u
    let W:=mixedReciprocalSum (mixed p.1.1) (publicBids p)
    let L0:=TypicalHighPolicy.meanMultiplier A H0.val c K.ξ (regime p.1.1)
      (owner0 p.1.1) (mixed p.1.1) (publicBids p) (K.marksLaw H0)
    let L1:=TypicalHighPolicy.meanMultiplier A H1.val c K.ξ (regime p.1.1)
      (owner1 p.1.1) (mixed p.1.1) (publicBids p) (K.marksLaw H1)
    FiniteLaw.ofMeasure (rawPayloadLaw K ρ H0 H1)
      (fun z => outcome K H0 H1 Q b y (u,z))
      ((measurable_outcome K H0 H1 Q b y).comp (measurable_const.prodMk measurable_id))=
        actualCount K.ξ y W L0 L1 := by
  dsimp only
  rw [private_count K H0 H1 Q ρ hrows b y u]
  let p:=parameter K H0 H1 Q b u
  obtain ⟨hs,hg0,hg1,hp0,hp1⟩ := hg
  have hh := FocalInsertion.original_focal_count A H0.val H1.val c (regime p.1.1)
    (owner0 p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) y
    (ProbabilityMeasure.toMeasure (K.originalPrivateRow H0))
    (ProbabilityMeasure.toMeasure (K.originalPrivateRow H1))
    K.xi_pos K.xi_lt_one.le (fun j => (p.1.2 j).2) hs hg0 hg1
  exact hh

include hrows in
theorem private_count_on_good (b : Fin A→ Icc (1:ℝ) K.E.U) (y : ℝ) (u : unitInterval)
    (hg : Good K H0 H1 Q b u) :
    let p:=parameter K H0 H1 Q b u
    let W:=mixedReciprocalSum (mixed p.1.1) (publicBids p)
    let L0:=TypicalHighPolicy.meanMultiplier A H0.val c K.ξ (regime p.1.1)
      (owner0 p.1.1) (mixed p.1.1) (publicBids p) (K.marksLaw H0)
    let L1:=TypicalHighPolicy.meanMultiplier A H1.val c K.ξ (regime p.1.1)
      (owner1 p.1.1) (mixed p.1.1) (publicBids p) (K.marksLaw H1)
    FiniteLaw.ofMeasure (rawPayloadLaw K ρ H0 H1)
      (fun z => outcome K H0 H1 Q b y (u,z))
      ((measurable_outcome K H0 H1 Q b y).comp (measurable_const.prodMk measurable_id))=
        actualCount K.ξ y W L0 L1 := by
  dsimp only
  rw [private_count K H0 H1 Q ρ hrows b y u]
  let p:=parameter K H0 H1 Q b u
  obtain ⟨hs,hg0,hg1,hp0,hp1⟩ := hg.2
  have hh := FocalInsertion.original_focal_count A H0.val H1.val c (regime p.1.1)
    (owner0 p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) y
    (ProbabilityMeasure.toMeasure (K.originalPrivateRow H0))
    (ProbabilityMeasure.toMeasure (K.originalPrivateRow H1))
    K.xi_pos K.xi_lt_one.le (fun j => (p.1.2 j).2) hs hg0 hg1
  exact hh

end Numerical

section OriginalNative
variable {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c)
  (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hQ : ∀ A,K.publicChoice A=PublicScenario.localChoice K.E Q μL A)
  (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed) (hpolicy : Γ.policy=K.completedPolicy)
  (i : Fin (N+1)) (kind : Fin N→ Fin 4) (ω : Sample (N+1) 2 Seed)
  (hr : ∀ r : Fin N,NativeMenuReports.MenuAction K.E (ω.1.1 (i.succAbove r)).1.2)
  (hk : rivalKinds K.E i ω.1=kind)
  (b : ℝ) (hb0 : 0≤ b) (hb : K.E.localTag (some b)=1) (hbo : b∉Icc (1:ℝ) K.E.U)

local notation "H0" => K.finiteCount (rivalSet i kind 2)
local notation "H1" => K.finiteCount (rivalSet i kind 3)
set_option quotPrecheck false in
local notation "row" => commonRow K.E i kind (fun r => ω.1.1 (i.succAbove r))
set_option quotPrecheck false in
local notation "payload" => ((privateRowRaw K.E i kind 2 (fun r => ω.1.1 (i.succAbove r)),
  privateRowRaw K.E i kind 3 (fun r => ω.1.1 (i.succAbove r))),(ω.1.2,ω.2))

include hQ hpolicy hr hk hb hbo in
theorem original_count_on_good (u : unitInterval)
    (hseed : ∀ j : Fin 2,seedOnList μL (K.E.roleList 0 (presentList ω.1 i b j))=some u)
    (hg : Good K H0 H1 Q row u) :
    focalCount Γ i (RawRoutes.action b hb0 2) ω=outcome K H0 H1 Q row b (u,payload) := by
  have hp := actual_sampler_pair K Q μL (fun A z => congrFun (hQ A) z)
    i kind ω.1 hr hk b hb hbo u hseed hg
  have ho (j : Fin 2) : observe (deviated i (RawRoutes.action b hb0 2) ω) j=
      presentList ω.1 i b j :=
    observe_deviated_of_mem i (RawRoutes.action b hb0 2) ω j
      (by simp [RawRoutes.action,Hybrid.firstK_full_two])
  unfold focalCount
  rw [hpolicy,NativeCountCoordinates.boundedCount_eq_listPairCount K,ho 0,ho 1]
  unfold NativeCountCoordinates.listPairCount outcome originalPairCount localAccept
  simp only [hp.1 (ω.1.2 0),hp.2 (ω.1.2 1)]
  rfl

include hQ hpolicy hr hk hb hbo in
theorem original_count_error (u : unitInterval)
    (hseed : ∀ j : Fin 2,seedOnList μL (K.E.roleList 0 (presentList ω.1 i b j))=some u)
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
end FCAppendix.Affine.Tail04.NativeUnusedExperiment
