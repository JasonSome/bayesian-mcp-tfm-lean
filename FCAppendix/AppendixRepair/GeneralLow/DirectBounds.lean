import FCAppendix.AppendixRepair.GeneralLow.ReferenceContext
import FCAppendix.AppendixRepair.GeneralLow.DirectCopy
import FCAppendix.AppendixRepair.GeneralLow.SourceSupport
import FCAppendix.AppendixRepair.LowCounts

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.DirectBounds
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open Affine Affine.LowBody Affine.Hybrid Affine.Hybrid.NativeContinuation
open HigherPolicy HigherPosterior DirectGame
open Existence.Distributional
open Affine.AppendixRepair.TriangularLow
open scoped BigOperators

variable {N c : ℕ} {d U η : ℝ}

theorem guard_bidCompatible {κ : ℝ} (hdU : d ≤ U) (a : JointAction 2)
    (ha : lowActionGuard d U κ a) :
    BidCompatible (ReferenceContext.classifier d U) d κ a.bid := by
  by_cases hd : a.bid ≤ d
  · simp [BidCompatible, ReferenceContext.classifier, Information.thresholdClassifier, hd]
  · by_cases hU : a.bid ≤ U
    · have hfloor := ha.2 (lt_of_not_ge hd) hU
      simp [BidCompatible, ReferenceContext.classifier, Information.thresholdClassifier,
        hd, hU, hfloor]
    · have hfloor : d < a.bid := hdU.trans_lt (lt_of_not_ge hU)
      simp [BidCompatible, ReferenceContext.classifier, Information.thresholdClassifier,
        hd, hU, hfloor]

theorem guard_observe_compatible {κ : ℝ} (hdU : d ≤ U)
    (z : UserProfile (N+1) 2) (hz : ∀ i, lowActionGuard d U κ (z i).1.2)
    (j : Fin 2) :
    CompatibleList (ReferenceContext.classifier d U) d κ (observe (drawsRealization z) j) := by
  refine ⟨(feasibleObservedList_iff_nonnegative j _).mp ⟨z, rfl⟩, ?_⟩
  intro i
  unfold observe
  split
  · exact Or.inr (guard_bidCompatible hdU (z i).1.2 (hz i))
  · exact Or.inl rfl

theorem residual_deleted_eq (hdU : d ≤ U) (z : UserProfile (N+1) 2)
    (hz : z ∈ classifiedProfiles (N+1) U) (i : Fin (N+1))
    (hf : (z i).1.2.bid ≤ d) (c : ℕ) (j : Fin 2) :
    residual c j (actualContext U z) - (upperSet d (actualContext U z).1).card =
      c - classCount 1 (collapsedDeletedRow d U z i) -
        classCount (upperTag j) (collapsedDeletedRow d U z i) := by
  let e := focalIndex i
  let zn := z ∘ e
  let X := actualContext U z
  let A := upperSet d X.1
  have he0 : e 0 = i := focalIndex_zero i
  have hzn : zn ∈ classifiedProfiles (N+1) U := fun k => hz (e k)
  have hfn : (zn 0).1.2.bid ≤ d := by simpa only [zn, Function.comp_apply, he0] using hf
  have hctx : actualContext U zn = reindexContext e X := actualContext_reindex e U z
  have hrow : collapsedProfileRow d U zn = collapsedDeletedRow d U z i :=
    collapsedProfileRow_focalIndex d U z i
  have hcard : (upperSet d (actualContext U zn).1).card = A.card := by
    rw [hctx]
    change (upperSet d (X.1 ∘ e)).card = A.card
    rw [upperSet_reindex, Finset.card_map]
  have hr : residual c j (actualContext U zn) = residual c j X := by rw [hctx]; rfl
  have hh := (collapsed_context_data (c := c) hdU zn hzn hfn).2.2 j
  simpa only [hr, hcard, hrow] using hh

theorem selected_implies_local_underflow (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (hdU : d ≤ U)
    (HC : HigherSelector (m := N+1) (ReferenceContext.classifier d U) c unitInterval)
    (z : UserProfile (N+1) 2) (hz : z ∈ classifiedProfiles (N+1) U)
    (hcomp : ∀ j, CompatibleList (ReferenceContext.classifier d U) d (1 - ξ)
      (observe (drawsRealization z) j))
    (i : Fin (N+1)) (hf : (z i).1.2.bid ≤ d)
    (seed : Fin 2 → unitInterval) (j : Fin 2)
    (hsel : i ∈ allocation (drawsRealization z)
      (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) seed j) :
    classCount 1 (collapsedDeletedRow d U z i) +
      classCount (upperTag j) (collapsedDeletedRow d U z i) < c := by
  let C := ReferenceContext.classifier d U
  have hp : observe (drawsRealization z) j i ≠ none :=
    (DirectGame.selection_feasible C d ξ hξ hξ1 c HC j _ (seed j)).2 i hsel
  have ht : Information.tag C (observe (drawsRealization z) j i) = 0 := by
    have hr : j ∈ (drawsRealization z).recipients i := by
      by_contra hn
      exact hp (by simp [observe, hn])
    have hentry : observe (drawsRealization z) j i = some (z i).1.2.bid := by
      simp only [observe, if_pos hr]
      rfl
    rw [hentry]
    simp [Information.tag, C, ReferenceContext.classifier,
      Information.thresholdClassifier, hf]
  have hl := (DirectGame.selection_low_membership C d ξ hξ hξ1 c HC j _ (seed j)
    i (hcomp j) ht).mp hsel
  have hpos : 0 < Information.ownResidual C c (observe (drawsRealization z) j) :=
    (Finset.card_pos.mpr ⟨i, hl⟩).trans_le
      (DirectGame.lowSelect_feasible C ξ hξ hξ1 c _ (seed j)).1
  rw [ReferenceContext.ownResidual_eq hdU z hz c j,
    residual_deleted_eq hdU z hz i hf c j] at hpos
  omega

theorem positive_implies_higherUnderflow (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (hdU : d ≤ U)
    (HC : HigherSelector (m := N+1) (ReferenceContext.classifier d U) c unitInterval)
    (z : UserProfile (N+1) 2) (hz : z ∈ classifiedProfiles (N+1) U)
    (hcomp : ∀ j, CompatibleList (ReferenceContext.classifier d U) d (1 - ξ)
      (observe (drawsRealization z) j))
    (i : Fin (N+1)) (hf : (z i).1.2.bid ≤ d) (seed : Fin 2 → unitInterval)
    (hpos : 0 < inclusionCount (drawsRealization z)
      (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) seed i) :
    HigherUnderflow c (fun k => (collapsedDeletedRow d U z i k).1) := by
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hm := (Finset.mem_filter.mp hj).2
  have hu := selected_implies_local_underflow ξ hξ hξ1 c hdU HC z hz hcomp i hf seed j hm
  fin_cases j
  · left
    rw [sum_firstHigher]
    exact hu
  · right
    rw [sum_secondHigher]
    exact hu

theorem duplicate_implies_bothUnderflow (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (hdU : d ≤ U)
    (HC : HigherSelector (m := N+1) (ReferenceContext.classifier d U) c unitInterval)
    (z : UserProfile (N+1) 2) (hz : z ∈ classifiedProfiles (N+1) U)
    (hcomp : ∀ j, CompatibleList (ReferenceContext.classifier d U) d (1 - ξ)
      (observe (drawsRealization z) j))
    (i : Fin (N+1)) (hf : (z i).1.2.bid ≤ d) (seed : Fin 2 → unitInterval)
    (hdup : inclusionCount (drawsRealization z)
      (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) seed i = 2) :
    BothUnderflow c (fun k => (collapsedDeletedRow d U z i k).1) := by
  have hall : accepted (drawsRealization z)
      (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) seed i =
      Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin, inclusionCount] using hdup
  have hu (j : Fin 2) : classCount 1 (collapsedDeletedRow d U z i) +
      classCount (upperTag j) (collapsedDeletedRow d U z i) < c := by
    apply selected_implies_local_underflow ξ hξ hξ1 c hdU HC z hz hcomp i hf seed j
    have hm : j ∈ accepted (drawsRealization z)
        (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) seed i := by
      rw [hall]
      exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hm).2
  constructor
  · rw [sum_firstHigher]
    exact hu 0
  · rw [sum_secondHigher]
    exact hu 1

theorem underflow_common_conull
    (P : ProbabilityMeasure (ℝ × JointAction 2)) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hdU : d ≤ U)
    (HC : HigherSelector (m := N+1) (ReferenceContext.classifier d U) c unitInterval)
    (hprofiles : ∀ᵐ z ∂userProfileLaw
      (DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC),
        ∀ k, lowActionGuard d U ((1+η)/2) (z k).1.2) :
    let Gamma := DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC
    ∀ᵐ w ∂sampleLaw Gamma, ∀ i : Fin (N+1), ∀ a : JointAction 2, a.bid ≤ d →
      (0 < (focalCount Gamma i a w).val →
        HigherUnderflow c (fun k => (collapsedDeletedRow d U w.1.1 i k).1)) ∧
      ((focalCount Gamma i a w).val = 2 →
        BothUnderflow c (fun k => (collapsedDeletedRow d U w.1.1 i k).1)) := by
  dsimp only
  let Gamma := DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC
  let ξ := (1-η)/2
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hξ1 : ξ < 1 := by dsimp [ξ]; linarith
  have hpMP : MeasurePreserving (fun w : Sample (N+1) 2 unitInterval => w.1.1)
      (sampleLaw Gamma) (userProfileLaw Gamma) :=
    (measurePreserving_fst (μ := userProfileLaw Gamma)
      (ν := Measure.pi (fun _ : Fin 2 => Gamma.seedLaw))).comp
      (measurePreserving_fst (μ := backgroundLaw Gamma) (ν := permLaw 2))
  filter_upwards [hpMP.quasiMeasurePreserving.ae hprofiles] with w hw
  intro i a ha
  let full := broadcastAction a
  let z := Function.update w.1.1 i ((0, full), w.2)
  have hzguard := inserted_low_guard hdU w.1.1 hw i 0 full rfl ha w.2
  have hz : z ∈ classifiedProfiles (N+1) U := fun k => (hzguard k).1
  have hcomp : ∀ j, CompatibleList (ReferenceContext.classifier d U) d (1-ξ)
      (observe (drawsRealization z) j) := by
    have hk : 1-ξ = (1+η)/2 := by dsimp [ξ]; ring
    rw [hk]
    exact guard_observe_compatible hdU z hzguard
  have hf : (z i).1.2.bid ≤ d := by simpa only [z, Function.update_self, full, broadcastAction] using ha
  have hr : collapsedDeletedRow d U z i = collapsedDeletedRow d U w.1.1 i := by
    funext k
    simp only [collapsedDeletedRow, z, Function.update_of_ne (Fin.succAbove_ne i k)]
  have hc : inclusionCount (drawsRealization z) Gamma.policy w.1.2 i =
      (focalCount Gamma i full w).val :=
    (focalCount_eq_inserted_count Gamma i 0 full w.1.1 w.1.2 w.2).symm
  change inclusionCount (drawsRealization z)
    (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) w.1.2 i =
    (focalCount Gamma i full w).val at hc
  constructor
  · intro hpos
    have hfull : 0 < (focalCount Gamma i full w).val :=
      hpos.trans_le (focalCount_le_broadcast Gamma i a w)
    have hu := positive_implies_higherUnderflow ξ hξ hξ1 c hdU HC z hz hcomp i hf w.1.2
      (by rw [hc]; exact hfull)
    simpa only [hr] using hu
  · intro hdup
    change (focalCount Gamma i a w).val = 2 at hdup
    have hfull : (focalCount Gamma i full w).val = 2 := by
      have hmono := focalCount_le_broadcast Gamma i a w
      change (focalCount Gamma i a w).val ≤ (focalCount Gamma i full w).val at hmono
      have hle := (focalCount Gamma i full w).isLt
      omega
    have hu := duplicate_implies_bothUnderflow ξ hξ hξ1 c hdU HC z hz hcomp i hf w.1.2
      (by rw [hc]; exact hfull)
    simpa only [hr] using hu

theorem count_event_le {m : ℕ} (Gamma : FiniteGame m 2 c unitInterval)
    (i : Fin m) (a : JointAction 2)
    (row : UserProfile m 2 → Fin N → RowRival) (hrow : Measurable row)
    (nu : Measure (Fin N → RowRival)) (hlaw : (userProfileLaw Gamma).map row = nu)
    (E : Set (Fin N → RowRival)) (hE : MeasurableSet E) (Q : Fin 3 → Prop)
    (hpoint : ∀ᵐ w ∂sampleLaw Gamma, Q (focalCount Gamma i a w) → row w.1.1 ∈ E) :
    ((problem Gamma i).outcome a).prob Q ≤ nu.real E := by
  classical
  let A : Set (Sample m 2 unitInterval) := {w | row w.1.1 ∈ E}
  have hA : MeasurableSet A := hE.preimage (hrow.comp measurable_fst.fst)
  have hpMP : MeasurePreserving (fun w : Sample m 2 unitInterval => w.1.1)
      (sampleLaw Gamma) (userProfileLaw Gamma) :=
    (measurePreserving_fst (μ := userProfileLaw Gamma)
      (ν := Measure.pi (fun _ : Fin 2 => Gamma.seedLaw))).comp
      (measurePreserving_fst (μ := backgroundLaw Gamma) (ν := permLaw 2))
  rw [FiniteLaw.prob_eq_expect, problem_outcome, CountLaw.expect_ofMeasure]
  have hi := CountLaw.integrable_comp (sampleLaw Gamma) (focalCount Gamma i a)
    (measurable_focalCount Gamma i a) (fun r : Fin 3 => if Q r then (1 : ℝ) else 0)
  have hb : (∫ w, (if Q (focalCount Gamma i a w) then (1 : ℝ) else 0) ∂sampleLaw Gamma) ≤
      ∫ w, A.indicator (fun _ => (1 : ℝ)) w ∂sampleLaw Gamma := by
    apply integral_mono_ae hi ((integrable_const (1 : ℝ)).indicator hA)
    filter_upwards [hpoint] with w hw
    by_cases hq : Q (focalCount Gamma i a w)
    · have ha : w ∈ A := hw hq
      simp only [if_pos hq, Set.indicator_of_mem ha, le_refl]
    · rw [if_neg hq]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) w
  have hind := integral_indicator_one (μ := sampleLaw Gamma) hA
  have hone : (1 : Sample m 2 unitInterval → ℝ) = (fun _ => 1) := rfl
  rw [hone] at hind
  rw [hind] at hb
  have hmap : (sampleLaw Gamma).map
      (row ∘ (fun w : Sample m 2 unitInterval => w.1.1)) = nu := by
    rw [← Measure.map_map hrow hpMP.measurable, hpMP.map_eq, hlaw]
  have hm := Measure.map_apply (μ := sampleLaw Gamma) (hrow.comp hpMP.measurable) hE
  rw [hmap] at hm
  exact hb.trans_eq (congrArg ENNReal.toReal hm.symm)

theorem duplicates_eq_prob_two (μ : CountLaw 2) :
    μ.duplicates = μ.prob (fun r => r.val = 2) := by
  rw [CountLaw.duplicates_eq_expect, FiniteLaw.prob_eq_expect]
  apply μ.expect_congr
  intro r
  fin_cases r <;> norm_num [successIndicator]

theorem counts_le_underflow_of_guard
    (P : ProbabilityMeasure (ℝ × JointAction 2)) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hdU : d ≤ U)
    (HC : HigherSelector (m := N+1) (ReferenceContext.classifier d U) c unitInterval)
    (hprofiles : ∀ᵐ z ∂userProfileLaw
      (DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC),
        ∀ k, lowActionGuard d U ((1+η)/2) (z k).1.2)
    (i : Fin (N+1)) (row : UserProfile (N+1) 2 → Fin N → RowRival)
    (hrow : Measurable row) (hrowdef : ∀ z, row z = collapsedDeletedRow d U z i)
    (nu : Measure (Fin N → RowRival))
    (hlaw : (userProfileLaw
      (DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC)).map row = nu)
    (a : JointAction 2) (ha : a.bid ≤ d) :
    let Gamma := DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC
    ((problem Gamma i).outcome a).success ≤ nu.real (LowCounts.rowHigherUnderflow c) ∧
      ((problem Gamma i).outcome a).duplicates ≤ nu.real (rowBothUnderflow c) := by
  dsimp only
  let Gamma := DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC
  have hcommon := underflow_common_conull P hη0 hη1 hdU HC hprofiles
  constructor
  · rw [← LowCounts.prob_ne_zero_eq_success]
    apply count_event_le Gamma i a row hrow nu hlaw _
      (LowCounts.measurableSet_rowHigherUnderflow c) (fun r => r ≠ 0)
    filter_upwards [hcommon] with w hw hne
    change HigherUnderflow c (fun k => (row w.1.1 k).1)
    rw [hrowdef]
    apply (hw i a ha).1
    have hn : (focalCount Gamma i a w).val ≠ 0 := fun h => hne (Fin.ext h)
    exact Nat.pos_of_ne_zero hn
  · rw [duplicates_eq_prob_two]
    apply count_event_le Gamma i a row hrow nu hlaw _
      (measurableSet_rowBothUnderflow c) (fun r => r.val = 2)
    filter_upwards [hcommon] with w hw hdup
    change BothUnderflow c (fun k => (row w.1.1 k).1)
    rw [hrowdef]
    exact (hw i a ha).2 hdup

theorem population_counts_bound (_hd : 0 ≤ d) (hdU : d ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2)) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hactive : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+η)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount=1)
    (HC : HigherSelector (m := N+1) (ReferenceContext.classifier d U) c unitInterval)
    (i : Fin (N+1)) (act : JointAction 2) (hbd : act.bid ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
    let Gamma := DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC
    ((problem Gamma i).outcome act).success ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (HigherUnderflow c) ∧
    ((problem Gamma i).outcome act).duplicates ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c) := by
  dsimp only
  let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
  let Native := PopulationGame.game (N+1) c P η hη0 hη1 U
  let Gamma := DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC
  let row : UserProfile (N+1) 2 → Fin N → RowRival :=
    fun z j => nativeRowRival Native d U (z (i.succAbove j))
  have hrow : Measurable row := measurable_pi_lambda _ (fun j =>
    (measurable_nativeRowRival Native d U).comp (measurable_pi_apply (i.succAbove j)))
  have hκ : ((1+η)/2) ≤ 1 := by linarith
  have hac : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+η)/2)*x.2.bid ∧ d < x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2 := by
    filter_upwards [hactive] with x hx
    exact ⟨hx.1, hx.1.trans_le (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hκ) x.2.bid_nonneg]), hx.2⟩
  have hp : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)), lowActionGuard d U ((1+η)/2) x.2 :=
    population_lowActionGuard hdU s a h mu pi PA PH hac hupper
  have hprofiles : ∀ᵐ z ∂userProfileLaw Gamma,
      ∀ k, lowActionGuard d U ((1+η)/2) (z k).1.2 :=
    profile_lowActionGuard (N := N) (c := c) P hη0 hη1 hp
  have hphysical : (userLaw Native).map (nativeRowRival Native d U) =
      rivalLaw s a h (realLowBidLaw pi.1 : Measure ℝ) :=
    native_population_row hdU s a h hs ha hh hsum mu pi PA PH
      (hac.mono (fun _ hx => ⟨hx.2.1, hx.2.2.1⟩))
      (hupper.mono (fun _ hx => hx.1)) η hη0 hη1
  have hlaw : (userProfileLaw Gamma).map row =
      Measure.pi (fun _ : Fin N => rivalLaw s a h (realLowBidLaw pi.1 : Measure ℝ)) :=
    deleted_rival_rows_law Native i (nativeRowRival Native d U)
      (measurable_nativeRowRival Native d U) _ hphysical
  have hb := counts_le_underflow_of_guard P hη0 hη1 hdU HC hprofiles
    i row hrow (fun _ => rfl) _ hlaw act hbd
  rw [LowCounts.rowHigherUnderflow_probability s a h hs ha hh hsum
      (realLowBidLaw pi.1 : Measure ℝ) N c,
    rowBothUnderflow_probability s a h hs ha hh hsum (realLowBidLaw pi.1 : Measure ℝ) N c,
    categoryLaw_eq_low_law s a h hs ha hh hsum (realLowBidLaw pi.1 : Measure ℝ) Gref] at hb
  exact hb

theorem population_low_duplicate_bound (hd : 0 ≤ d) (hdU : d ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2)) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (HC : HigherSelector (m := N+1) (ReferenceContext.classifier d U) c unitInterval)
    (hactive : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+η)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount=1)
    (i : Fin (N+1)) (act : JointAction 2) (_hk : act.routeCount=2) (hbd : act.bid ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
    let Gamma := DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC
    ((problem Gamma i).outcome act).duplicates ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c) :=
  (population_counts_bound hd hdU s a h hs ha hh hsum Gref mu pi PA PH
    hη0 hη1 hactive hupper HC i act hbd).2

theorem population_low_success_bound (hd : 0 ≤ d) (hdU : d ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2)) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (HC : HigherSelector (m := N+1) (ReferenceContext.classifier d U) c unitInterval)
    (hactive : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+η)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount=1)
    (i : Fin (N+1)) (act : JointAction 2) (hbd : act.bid ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
    let Gamma := DirectGame.game (N+1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC
    ((problem Gamma i).outcome act).success ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (HigherUnderflow c) :=
  (population_counts_bound hd hdU s a h hs ha hh hsum Gref mu pi PA PH
    hη0 hη1 hactive hupper HC i act hbd).1

theorem source_counts_bound (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1+η)/2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : HigherSelector (m := N+1) B.classifier c unitInterval)
    (i : Fin (N+1)) (act : JointAction 2) (hbd : act.bid ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw
    let Gamma := DirectGame.game (N+1) c P η hη0 hη1 B.classifier d HC
    ((problem Gamma i).outcome act).success ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (HigherUnderflow c) ∧
    ((problem Gamma i).outcome act).duplicates ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c) := by
  dsimp only
  let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw
  have hA' : ∀ b ∈ B.activeSet, d < (1-(1-η)/2) * b := by
    intro b hb
    convert hA b hb using 1
    ring
  have hp : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)),
      BidCompatible B.classifier d (1-(1-η)/2) x.2.bid :=
    population_bidCompatible B H hA' hP s a h hs ha hh hsum mu pi
  let copy := (DirectCopy.allocationReproduction P η hη0 hη1 B.classifier d hd HC
    (fun b hb0 hbd => B.classifier_low_bid hb0 hbd) hp).toCounts
  rw [copy.outcome_eq i act hbd]
  have hpop : DirectCopy.referencePopulation B.classifier d hd P =
      populationLaw s a h hs ha hh hsum (lowJoint mu pi)
        (H.referenceActive hd) (H.referencePrivate hd) := by
    apply Subtype.ext
    exact recode_population B hd H s a h hs ha hh hsum mu pi
  unfold DirectCopy.referenceGame
  rw [hpop]
  exact population_counts_bound hd (Tail.reference_bid_guards hd hη0).1
    s a h hs ha hh hsum Gref mu pi (H.referenceActive hd) (H.referencePrivate hd)
    hη0 hη1 (H.referenceActive_support hd hη0) (H.referencePrivate_support hd)
    (emptyHigher (DirectCopy.referenceClassifier d) c) i act hbd

end FCAppendix.Appendix08.GeneralLow.DirectBounds
