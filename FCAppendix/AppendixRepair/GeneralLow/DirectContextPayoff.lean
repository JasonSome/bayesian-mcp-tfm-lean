import FCAppendix.AppendixRepair.GeneralLow.DirectGame
import FCAppendix.AppendixRepair.GeneralLow.ExactLowPayoff
import FCAppendix.AppendixRepair.GeneralLow.ReferenceContext
import FCAppendix.Affine.Hybrid.NativeLowPopulation
import FCAppendix.Affine.Hybrid.NativeRealizedContext

set_option maxHeartbeats 1400000
noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.DirectContextPayoff
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Affine.Hybrid.NativeContinuation
open Existence.PayOnceBounded (listBids)
open FCAppendix.AppendixRepair.GeneralLow
open scoped BigOperators

attribute [local irreducible] Hybrid.NativeEqual.sample

variable {m c : ℕ}

def lowList (d U : ℝ) (z : UserProfile m 2) : LocalList m :=
  eraseActiveList (upperSet d (actualContext U z).1) (actualContext U z).1

def budget (d U : ℝ) (c : ℕ) (z : UserProfile m 2) (j : Fin 2) : ℕ :=
  min (ExactLow.visible (lowList d U z)).card
    (residual c j (actualContext U z) - (upperSet d (actualContext U z).1).card)

theorem guard_profiles {d U κ : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : ∀ k, lowActionGuard d U κ (z k).1.2) :
    z ∈ HigherPosterior.profiles (ReferenceContext.classifier d U) d κ := by
  intro k
  let a := (z k).1.2
  have ha := hz k
  change HigherPosterior.ActionCompatible (ReferenceContext.classifier d U) d κ a
  by_cases hlow : a.bid ≤ d
  · have hc : (ReferenceContext.classifier d U).label a.bid = 0 := by
      simp [ReferenceContext.classifier, Information.thresholdClassifier, hlow]
    have hr : a.routeCount = 2 := by
      rcases ha.1 with h | h
      · exact h.2
      · exact False.elim (not_lt_of_ge (hlow.trans hdU) h.1)
    simp [HigherPosterior.ActionCompatible, HigherPosterior.BidCompatible, hc, hlow, hr]
  · by_cases hactive : a.bid ≤ U
    · have hc : (ReferenceContext.classifier d U).label a.bid = 1 := by
        simp [ReferenceContext.classifier, Information.thresholdClassifier, hlow, hactive]
      have hr : a.routeCount = 2 := by
        rcases ha.1 with h | h
        · exact h.2
        · exact False.elim (not_lt_of_ge hactive h.1)
      have hg : d < κ * a.bid := ha.2 (lt_of_not_ge hlow) hactive
      simp [HigherPosterior.ActionCompatible, HigherPosterior.BidCompatible, hc, hg, hr]
    · have hc : (ReferenceContext.classifier d U).label a.bid = 2 := by
        simp [ReferenceContext.classifier, Information.thresholdClassifier, hlow, hactive]
      have hr : a.routeCount = 1 := by
        rcases ha.1 with h | h
        · exact False.elim (hactive h.1)
        · exact h.2
      have hg : d < a.bid := hdU.trans_lt (lt_of_not_ge hactive)
      simp [HigherPosterior.ActionCompatible, HigherPosterior.BidCompatible, hc, hg, hr]

theorem focal_tag {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (i : Fin m) (hi : (z i).1.2.bid ≤ d)
    (j : Fin 2) :
    Information.tag (ReferenceContext.classifier d U) (observe (drawsRealization z) j i) = 0 := by
  have hk : (z i).1.2.routeCount = 2 := by
    rcases hz i with h | h
    · exact h.2
    · exact False.elim (not_lt_of_ge (hi.trans hdU) h.1)
  simp [observe, drawsRealization, hk, firstK_full_two, Information.tag,
    ReferenceContext.classifier, Information.thresholdClassifier, hi]

theorem lowList_focal {d U : ℝ} (hdU : d ≤ U) (z : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (i : Fin m) (hi : (z i).1.2.bid ≤ d) :
    lowList d U z i = some (z i).1.2.bid := by
  have hk : (z i).1.2.routeCount = 2 := by
    rcases hz i with h | h
    · exact h.2
    · exact False.elim (not_lt_of_ge (hi.trans hdU) h.1)
  have he := congrFun (ReferenceContext.lowPart_actual hdU z hz 0) i
  change Information.part (ReferenceContext.classifier d U) 0
    (observe (drawsRealization z) 0) i = lowList d U z i at he
  rw [← he]
  simp only [Information.part, focal_tag hdU z hz i hi 0, if_true]
  simp [observe, drawsRealization, hk, firstK_full_two]

theorem lowSelect_profile {d U ξ : ℝ} (hdU : d ≤ U) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (z : UserProfile m 2) (hz : z ∈ classifiedProfiles m U)
    (c : ℕ) (j : Fin 2) (s : unitInterval) :
    DirectGame.lowSelect (ReferenceContext.classifier d U) ξ hξ hξ1 c
      (observe (drawsRealization z) j) s =
      ExactLow.select ξ hξ hξ1 (lowList d U z)
        (budget d U c z j) (budget d U c z (Information.other j)) s := by
  rw [DirectGame.lowSelect, ReferenceContext.lowPart_actual hdU z hz j,
    ReferenceContext.ownResidual_eq hdU z hz c j,
    ReferenceContext.otherResidual_eq hdU z hz c j]
  rfl

theorem allocation_low_mem_iff {d U ξ : ℝ} (hdU : d ≤ U) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (HC : HigherPolicy.HigherSelector (m := m) (ReferenceContext.classifier d U) c unitInterval)
    (z : UserProfile m 2) (hz : ∀ k, lowActionGuard d U (1 - ξ) (z k).1.2)
    (i : Fin m) (hi : (z i).1.2.bid ≤ d) (s : Fin 2 → unitInterval) (j : Fin 2) :
    i ∈ allocation (drawsRealization z)
      (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) s j ↔
      i ∈ ExactLow.select ξ hξ hξ1 (lowList d U z)
        (budget d U c z j) (budget d U c z (Information.other j)) (s j) := by
  have hclassified : z ∈ classifiedProfiles m U := fun k => (hz k).1
  have hcomp := HigherPosterior.observe_compatible (ReferenceContext.classifier d U)
    d (1 - ξ) z (guard_profiles hdU z hz) j
  change i ∈ DirectGame.selection (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC j
    (observe (drawsRealization z) j) (s j) ↔ _
  rw [DirectGame.selection_low_membership (ReferenceContext.classifier d U) d ξ hξ hξ1 c
    HC j _ (s j) i hcomp (focal_tag hdU z hclassified i hi j),
    lowSelect_profile hdU hξ hξ1 z hclassified c j (s j)]

theorem inclusionCount_eq_focalCopy {d U ξ : ℝ} (hdU : d ≤ U) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (HC : HigherPolicy.HigherSelector (m := m) (ReferenceContext.classifier d U) c unitInterval)
    (z : UserProfile m 2) (hz : ∀ k, lowActionGuard d U (1 - ξ) (z k).1.2)
    (i : Fin m) (hi : (z i).1.2.bid ≤ d) (s : Fin 2 → unitInterval) :
    inclusionCount (drawsRealization z)
      (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) s i =
      (focalCopy
        (ExactLow.select ξ hξ hξ1 (lowList d U z) (budget d U c z 0) (budget d U c z 1) (s 0),
         ExactLow.select ξ hξ hξ1 (lowList d U z) (budget d U c z 1) (budget d U c z 0) (s 1)) i).val := by
  rw [inclusionCount_eq_sum, Fin.sum_univ_two]
  simp only [allocation_low_mem_iff hdU hξ hξ1 HC z hz i hi s,
    Information.other, Fin.isValue, ite_true, Fin.reduceEq, ite_false]
  by_cases h0 : i ∈ ExactLow.select ξ hξ hξ1 (lowList d U z)
      (budget d U c z 0) (budget d U c z 1) (s 0) <;>
    by_cases h1 : i ∈ ExactLow.select ξ hξ hξ1 (lowList d U z)
      (budget d U c z 1) (budget d U c z 0) (s 1) <;>
    simp [focalCopy, h0, h1]

theorem realized_payoff (P : ProbabilityMeasure (ℝ × JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) {d U : ℝ} (hdU : d ≤ U)
    (HC : HigherPolicy.HigherSelector (m := m) (ReferenceContext.classifier d U) c unitInterval)
    (i : Fin m) (v : ℝ) (a : JointAction 2) (ha : a.bid ≤ d)
    (profile : UserProfile m 2) (s : Fin 2 → unitInterval) (tau : Equiv.Perm (Fin 2))
    (hz : ∀ k, lowActionGuard d U ((1 + η) / 2)
      ((Function.update profile i ((v, a), tau)) k).1.2) :
    let ξ := (1 - η) / 2
    let hξ : 0 < ξ := by dsimp only [ξ]; linarith
    let hξ1 : ξ < 1 := by dsimp only [ξ]; linarith
    let z := Function.update profile i ((v, a), tau)
    nativeRealizedPayoff
      (DirectGame.game m c P η hη0 hη1 (ReferenceContext.classifier d U) d HC)
      i v a ((profile, s), tau) =
      purePayoff (1 - ξ) v (listBids (lowList d U z))
        (ExactLow.select ξ hξ hξ1 (lowList d U z) (budget d U c z 0) (budget d U c z 1) (s 0),
         ExactLow.select ξ hξ hξ1 (lowList d U z) (budget d U c z 1) (budget d U c z 0) (s 1)) i := by
  dsimp only
  let ξ := (1 - η) / 2
  let z := Function.update profile i ((v, a), tau)
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hξ1 : ξ < 1 := by dsimp [ξ]; linarith
  have heκ : (1 + η) / 2 = 1 - ξ := by dsimp [ξ]; ring
  have hguard : ∀ k, lowActionGuard d U (1 - ξ) (z k).1.2 := by
    simpa only [← heκ] using hz
  have hclassified : z ∈ classifiedProfiles m U := fun k => (hguard k).1
  have hf : (z i).1.2.bid ≤ d := by simpa only [z, Function.update_self] using ha
  have hbid : listBids (lowList d U z) i = a.bid := by
    rw [listBids, lowList_focal hdU z hclassified i hf]
    simp only [Option.getD_some, z, Function.update_self]
  change userPayoff v a.bid 0 (Schedule.affine 2 η hη0 hη1.le).charge
    (Schedule.once 2).charge
    (focalCount (DirectGame.game m c P η hη0 hη1 (ReferenceContext.classifier d U) d HC)
      i a ((profile, s), tau)).val = _
  rw [focalCount_eq_inserted_count
    (DirectGame.game m c P η hη0 hη1 (ReferenceContext.classifier d U) d HC)
    i v a profile s tau]
  change userPayoff v a.bid 0 (Schedule.affine 2 η hη0 hη1.le).charge
    (Schedule.once 2).charge
    (inclusionCount (drawsRealization z)
      (DirectGame.localPolicy (ReferenceContext.classifier d U) d ξ hξ hξ1 c HC) s i) = _
  rw [inclusionCount_eq_focalCopy hdU hξ hξ1 HC z hguard i hf s, ← hbid,
    affine_count_payoff_eq_pure η hη0 hη1.le]
  rw [heκ]

theorem seed_average_payoff (P : ProbabilityMeasure (ℝ × JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) {d U : ℝ} (hdU : d ≤ U)
    (HC : HigherPolicy.HigherSelector (m := m) (ReferenceContext.classifier d U) c unitInterval)
    (i : Fin m) (v : ℝ) (a : JointAction 2) (ha : a.bid ≤ d)
    (profile : UserProfile m 2) (tau : Equiv.Perm (Fin 2))
    (hz : ∀ k, lowActionGuard d U ((1 + η) / 2)
      ((Function.update profile i ((v, a), tau)) k).1.2) :
    let ξ := (1 - η) / 2
    let hξ : 0 < ξ := by dsimp only [ξ]; linarith
    let hξ1 : ξ < 1 := by dsimp only [ξ]; linarith
    let z := Function.update profile i ((v, a), tau)
    (∫ s : Fin 2 → unitInterval,
      nativeRealizedPayoff
        (DirectGame.game m c P η hη0 hη1 (ReferenceContext.classifier d U) d HC)
        i v a ((profile, s), tau)
      ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) =
      ExactLow.seedAveragePayoff ξ hξ hξ1 (lowList d U z)
        (budget d U c z 0) (budget d U c z 1) i v := by
  dsimp only [ExactLow.seedAveragePayoff]
  apply integral_congr_ae
  exact ae_of_all _ (fun s => realized_payoff P η hη0 hη1 hdU HC i v a ha profile s tau hz)

end FCAppendix.Appendix08.GeneralLow.DirectContextPayoff
