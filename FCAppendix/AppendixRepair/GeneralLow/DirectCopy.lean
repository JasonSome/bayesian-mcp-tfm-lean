import FCAppendix.AppendixRepair.GeneralLow.DirectGame
import FCAppendix.AppendixRepair.TailApplication

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.DirectCopy
open MeasureTheory ProbabilityTheory Set Game Bayes Information
open Affine Affine.Hybrid HigherPolicy HigherPosterior DirectGame
open scoped BigOperators

variable {m c : ℕ}

def referenceClassifier (d : ℝ) : Classifier :=
  thresholdClassifier d (Tail.referenceActiveBid d)

def referencePopulation (C : Classifier) (d : ℝ) (hd : 0 ≤ d)
    (P : ProbabilityMeasure (ℝ × JointAction 2)) : ProbabilityMeasure (ℝ × JointAction 2) :=
  Tail.recodePopulation C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d)
    (Tail.referenceActiveBid_nonneg hd) (Tail.referencePrivateBid_nonneg hd) P

def referenceGame (m c : ℕ) (P : ProbabilityMeasure (ℝ × JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (C : Classifier) (d : ℝ) (hd : 0 ≤ d) :
    FiniteGame m 2 c unitInterval :=
  DirectGame.game m c (referencePopulation C d hd P) η hη0 hη1
    (referenceClassifier d) d (emptyHigher (referenceClassifier d) c)

theorem reference_active_gt {d : ℝ} (hd : 0 ≤ d) : d < Tail.referenceActiveBid d := by
  dsimp [Tail.referenceActiveBid]
  linarith

theorem recode_label (C : Classifier) {d b : ℝ} (hd : 0 ≤ d)
    (hb : C.label b = 0 → b ≤ d) :
    (referenceClassifier d).label
      (Tail.recodeBid C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) b) =
        C.label b := by
  have hA := reference_active_gt hd
  have hP : Tail.referenceActiveBid d < Tail.referencePrivateBid d := by
    dsimp [Tail.referencePrivateBid]
    linarith
  rcases hk : C.label b with ⟨k, hklt⟩
  interval_cases k
  · have hbd := hb (by simp [hk])
    simp [Tail.recodeBid, hk, referenceClassifier, thresholdClassifier, hbd]
  · simp [Tail.recodeBid, hk, referenceClassifier, thresholdClassifier,
      not_le.mpr hA]
  · simp [Tail.recodeBid, hk, referenceClassifier, thresholdClassifier,
      not_le.mpr (hA.trans hP), not_le.mpr hP]

theorem recode_bidCompatible (C : Classifier) {d κ b : ℝ} (hd : 0 ≤ d)
    (hA : d < κ * Tail.referenceActiveBid d)
    (hb : C.label b = 0 → b ≤ d) :
    BidCompatible (referenceClassifier d) d κ
      (Tail.recodeBid C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) b) := by
  have hl := recode_label C hd hb
  have hP : d < Tail.referencePrivateBid d := by
    have ha := reference_active_gt hd
    dsimp [Tail.referencePrivateBid]
    linarith
  rcases hk : C.label b with ⟨k, hklt⟩
  interval_cases k
  · have hbd := hb (by simp [hk])
    simp only [BidCompatible, hl]
    simp [hk, Tail.recodeBid, hbd]
  · simp only [BidCompatible, hl]
    simpa [hk, Tail.recodeBid] using hA
  · simp only [BidCompatible, hl]
    simpa [hk, Tail.recodeBid] using hP

theorem recode_tag (C : Classifier) {d κ : ℝ} (hd : 0 ≤ d)
    (L : LocalList m) (hL : CompatibleList C d κ L) (i : Fin m) :
    tag C (L i) = tag (referenceClassifier d)
      (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L i) := by
  cases hi : L i with
  | none => simp [Tail.recodeLocalList, hi, tag]
  | some b =>
      have hb := ((compatibleList_iff C d κ L hL.1).mp hL i b hi).1
      simp only [Tail.recodeLocalList, hi, Option.map_some, tag]
      rw [recode_label C hd hb]

theorem recode_counts (C : Classifier) {d κ : ℝ} (hd : 0 ≤ d)
    (L : LocalList m) (hL : CompatibleList C d κ L) (k : Fin 4) :
    localCount C L k = localCount (referenceClassifier d)
      (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L) k := by
  unfold localCount
  apply Finset.sum_congr rfl
  intro i _
  rw [recode_tag C hd L hL i]

theorem recode_low_list (C : Classifier) {d κ : ℝ} (hd : 0 ≤ d)
    (L : LocalList m) (hL : CompatibleList C d κ L) :
    part C 0 L = part (referenceClassifier d) 0
      (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L) := by
  funext i
  cases hi : L i with
  | none => simp [part, Tail.recodeLocalList, hi, tag]
  | some b =>
      have hb := ((compatibleList_iff C d κ L hL.1).mp hL i b hi).1
      have hl := recode_label C hd hb
      by_cases hc : C.label b = 0
      · simp only [part, Tail.recodeLocalList, hi, Option.map_some, tag, hl, hc]
        simp [Tail.recodeBid, hc]
      · simp only [part, Tail.recodeLocalList, hi, Option.map_some, tag, hl]
        have hcast : (C.label b).castSucc ≠ (0 : Fin 4) := by
          intro h
          apply hc
          apply Fin.ext
          exact congrArg (fun x : Fin 4 => x.val) h
        simp only [if_neg hcast]

theorem recode_nonnegative (C : Classifier) {d : ℝ} (hd : 0 ≤ d)
    (L : LocalList m) (hL : NonnegativeList L) :
    NonnegativeList
      (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L) := by
  intro i
  cases hi : L i with
  | none => simp [Tail.recodeLocalList, hi, entryBid]
  | some b =>
      have hb : 0 ≤ b := by simpa only [hi, entryBid] using hL i
      simpa only [Tail.recodeLocalList, hi, Option.map_some, entryBid] using
        Tail.recodeBid_nonneg C (Tail.referenceActiveBid_nonneg hd)
          (Tail.referencePrivateBid_nonneg hd) hb

theorem recode_compatible (C : Classifier) {d κ : ℝ} (hd : 0 ≤ d)
    (hA : d < κ * Tail.referenceActiveBid d)
    (L : LocalList m) (hL : CompatibleList C d κ L) :
    CompatibleList (referenceClassifier d) d κ
      (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L) := by
  refine ⟨recode_nonnegative C hd L hL.1, ?_⟩
  intro i
  cases hi : L i with
  | none => exact Or.inl (by simp [Tail.recodeLocalList, hi])
  | some b =>
      right
      simp only [Tail.recodeLocalList, hi, Option.map_some, entryBid]
      exact recode_bidCompatible C hd hA
        (((compatibleList_iff C d κ L hL.1).mp hL i b hi).1)

theorem lowSelect_recode (C : Classifier) {d ξ : ℝ} (hd : 0 ≤ d)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (L : LocalList m) (hL : CompatibleList C d (1 - ξ) L) (z : unitInterval) :
    lowSelect C ξ hξ hξ1 c L z =
      lowSelect (referenceClassifier d) ξ hξ hξ1 c
        (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L) z := by
  have hl := recode_low_list C hd L hL
  have ho : ownResidual C c L = ownResidual (referenceClassifier d) c
      (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L) := by
    simp only [ownResidual, recode_counts C hd L hL]
  have ht : otherResidual C c L = otherResidual (referenceClassifier d) c
      (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L) := by
    simp only [otherResidual, recode_counts C hd L hL]
  simp only [lowSelect, hl, ho, ht]

theorem selection_low_recode (C : Classifier) {d ξ : ℝ} (hd : 0 ≤ d)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (hA : d < (1 - ξ) * Tail.referenceActiveBid d)
    (HC : HigherSelector (m := m) C c unitInterval)
    (HR : HigherSelector (m := m) (referenceClassifier d) c unitInterval)
    (j : Fin 2) (L : LocalList m) (hL : CompatibleList C d (1 - ξ) L)
    (z : unitInterval) (i : Fin m) (hi : tag C (L i) = 0) :
    i ∈ DirectGame.selection C d ξ hξ hξ1 c HC j L z ↔
      i ∈ DirectGame.selection (referenceClassifier d) d ξ hξ hξ1 c HR j
        (Tail.recodeLocalList C (Tail.referenceActiveBid d) (Tail.referencePrivateBid d) L) z := by
  have hR := recode_compatible C hd hA L hL
  have htag := (recode_tag C hd L hL i).symm.trans hi
  rw [DirectGame.selection, if_pos hL, DirectGame.selection, if_pos hR,
    rawSelection_low_membership C ξ hξ hξ1 c HC j L z i hi,
    rawSelection_low_membership (referenceClassifier d) ξ hξ hξ1 c HR j _ z i htag,
    lowSelect_recode C hd hξ hξ1 c L hL z]

theorem sample_bidCompatible (Gamma : FiniteGame m 2 c unitInterval)
    (C : Classifier) (d κ : ℝ)
    (hpop : ∀ᵐ x ∂Gamma.F ⊗ₘ Gamma.σ, BidCompatible C d κ x.2.bid) :
    ∀ᵐ w ∂sampleLaw Gamma, ∀ i : Fin m, BidCompatible C d κ (w.1.1 i).1.2.bid := by
  have hu : ∀ᵐ u ∂userLaw Gamma, BidCompatible C d κ u.1.2.bid :=
    (measurePreserving_fst (μ := Gamma.F ⊗ₘ Gamma.σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hpop
  have hp : ∀ᵐ x ∂userProfileLaw Gamma, ∀ i : Fin m, BidCompatible C d κ (x i).1.2.bid :=
    ae_all_iff.mpr (fun i =>
      (measurePreserving_eval (fun _ : Fin m => userLaw Gamma) i).quasiMeasurePreserving.ae hu)
  have hb : ∀ᵐ w ∂backgroundLaw Gamma, ∀ i : Fin m, BidCompatible C d κ (w.1 i).1.2.bid :=
    (measurePreserving_fst (μ := userProfileLaw Gamma)
      (ν := Measure.pi (fun _ : Fin 2 => Gamma.seedLaw))).quasiMeasurePreserving.ae hp
  exact (measurePreserving_fst (μ := backgroundLaw Gamma) (ν := permLaw 2)).quasiMeasurePreserving.ae hb

theorem deviated_compatible (C : Classifier) (d κ : ℝ)
    (hlow : ∀ b : ℝ, 0 ≤ b → b ≤ d → C.label b = 0)
    (w : Sample m 2 unitInterval)
    (hw : ∀ k : Fin m, BidCompatible C d κ (w.1.1 k).1.2.bid)
    (i : Fin m) (a : JointAction 2) (ha : a.bid ≤ d) (j : Fin 2) :
    CompatibleList C d κ (observe (deviated i a w) j) := by
  have hn : NonnegativeList (observe (deviated i a w) j) := by
    intro k
    unfold observe
    split
    · exact ((deviated i a w).action k).bid_nonneg
    · exact le_rfl
  apply (compatibleList_iff C d κ _ hn).mpr
  intro k b hkb
  have hbid : BidCompatible C d κ ((deviated i a w).action k).bid := by
    by_cases hk : k = i
    · subst k
      rw [deviated_bid_self]
      simp [BidCompatible, hlow a.bid a.bid_nonneg ha, ha]
    · rw [deviated_bid_other i k hk]
      exact hw k
  unfold observe at hkb
  split_ifs at hkb with hrec
  exact (Option.some.inj hkb) ▸ hbid

def allocationReproduction (P : ProbabilityMeasure (ℝ × JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (C : Classifier) (d : ℝ) (hd : 0 ≤ d)
    (HC : HigherSelector (m := m) C c unitInterval)
    (hlow : ∀ b : ℝ, 0 ≤ b → b ≤ d → C.label b = 0)
    (hpop : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)),
      BidCompatible C d (1 - (1 - η) / 2) x.2.bid) :
    LowAllocationReproduction (DirectGame.game m c P η hη0 hη1 C d HC)
      (referenceGame m c P η hη0 hη1 C d hd) d := by
  let Gamma := DirectGame.game m c P η hη0 hη1 C d HC
  let Reference := referenceGame m c P η hη0 hη1 C d hd
  let bA := Tail.referenceActiveBid d
  let bP := Tail.referencePrivateBid d
  let f := Tail.recodeSample (m := m) (Seed := unitInterval) C bA bP
    (Tail.referenceActiveBid_nonneg hd) (Tail.referencePrivateBid_nonneg hd)
  have hjoint : (Gamma.F ⊗ₘ Gamma.σ).map
      (Tail.recodeJoint C bA bP (Tail.referenceActiveBid_nonneg hd)
        (Tail.referencePrivateBid_nonneg hd)) = Reference.F ⊗ₘ Reference.σ := by
    dsimp only [Gamma, Reference, referenceGame]
    rw [DirectGame.joint_law, DirectGame.joint_law]
    rfl
  refine ⟨f, Tail.measurePreserving_recodeSample Gamma Reference C bA bP
    (Tail.referenceActiveBid_nonneg hd) (Tail.referencePrivateBid_nonneg hd) hjoint rfl, ?_⟩
  intro i
  have hp : ∀ᵐ x ∂Gamma.F ⊗ₘ Gamma.σ,
      BidCompatible C d (1 - (1 - η) / 2) x.2.bid := by
    rw [show Gamma.F ⊗ₘ Gamma.σ = (P : Measure (ℝ × JointAction 2)) from
      DirectGame.joint_law P η hη0 hη1 C d HC]
    exact hpop
  filter_upwards [sample_bidCompatible Gamma C d (1 - (1 - η) / 2) hp] with w hw
  intro a ha j
  have hC := deviated_compatible C d (1 - (1 - η) / 2) hlow w hw i a ha j
  have hobs := Tail.observe_deviated_recode C bA bP
    (Tail.referenceActiveBid_nonneg hd) (Tail.referencePrivateBid_nonneg hd)
    i a (hlow a.bid a.bid_nonneg ha) w j
  change (i ∈ (Gamma.policy j (observe (deviated i a w) j) (w.1.2 j)).val) ↔
    (i ∈ (Reference.policy j (observe (deviated i a (f w)) j) (w.1.2 j)).val)
  rw [hobs]
  by_cases hrec : j ∈ firstK w.2 a.routeCount
  · have htag : tag C (observe (deviated i a w) j i) = 0 := by
      simp [observe, deviated_recipients_self, deviated_bid_self, hrec, tag,
        hlow a.bid a.bid_nonneg ha]
    have hA : d < (1 - (1 - η) / 2) * Tail.referenceActiveBid d := by
      convert (Tail.reference_bid_guards hd hη0).2.1 using 1
      ring
    exact selection_low_recode C hd (by linarith) (by linarith) c hA HC
      (emptyHigher (referenceClassifier d) c) j _ hC (w.1.2 j) i htag
  · have hn : observe (deviated i a w) j i = none := by
      simp [observe, deviated_recipients_self, hrec]
    have hn' : Tail.recodeLocalList C bA bP (observe (deviated i a w) j) i = none := by
      simp [Tail.recodeLocalList, hn]
    constructor
    · intro hi
      exact ((Gamma.policy j _ _).property.2 i hi hn).elim
    · intro hi
      exact ((Reference.policy j _ _).property.2 i hi hn').elim

end FCAppendix.Appendix08.GeneralLow.DirectCopy
