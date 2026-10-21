import FCAppendix.AppendixRepair.GeneralLow.SaturatedReceipts
import FCAppendix.AppendixRepair.GeneralLow.LowReceipts
import FCAppendix.Affine.Hybrid.ClassifiedOptimality

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.ProposerOptimality
open MeasureTheory ProbabilityTheory Game Bayes Set Filter
open HigherPolicy HigherPosterior HigherReceipts Continuation
open FCAppendix.AppendixRepair.GeneralLow
open scoped BigOperators

variable {m c : ℕ}
variable (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
  (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
  (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
  (H : HC Γ C d (1-ξ) R hfull)

local notation "Delta" => Implementation.game Γ C d ξ R hξ hξ1 hfull H
local notation "Bel" => Implementation.belief Γ C d ξ R hξ hξ1 hfull H
local notation "NormH" => NormalizedContinuation.selector Γ C d (1-ξ) R hfull H.selector

theorem class_support (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d (1-ξ) L)
    (hnot : L ∉ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j) :
    ∀ᵐ x ∂(Bel).posterior j L,
      observe (drawsRealization x) j = L ∧ x ∈ profiles C d (1-ξ) := by
  rw [Implementation.belief_eq_original Γ C d ξ R hξ hξ1 hfull H j L hnot]
  exact posterior_support Γ C d (1-ξ) R hR hRC hdR hfull j L hL hcomp

theorem private_receipt (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d (1-ξ) L) (i : Fin m) (b : ℝ)
    (hi : L i = some b) (hb : C.label b = 2) :
    Finite.conditionalReceipt (Delta).A (posteriorCountBelief Delta Bel j L i) b = b := by
  have hm : Affine.Hybrid.posteriorOtherMean Delta Bel j L i = 0 := by
    by_cases hbad : L ∈ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j
    · exact mean_of_private_posterior Delta Bel j L
        (Implementation.belief_eq_private_of_bad Γ C d ξ R hξ hξ1 hfull H j L hbad) i
    · exact private_mean_of_support Delta Bel C d (1-ξ) j L
        (class_support Γ C d ξ R hξ hξ1 hfull H hR hRC hdR j L hL hcomp hbad) i b hi hb
  rw [Affine.Hybrid.posterior_affine_receipt Delta Bel η hη0 hη1 hA, hm]
  ring

theorem high_receipt_gt (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hξeq : ξ = (1-η)/2)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d (1-ξ) L) (i : Fin m) (hi : i ∈ highSet C L) :
    d < beliefReceipts (Delta).A (posteriorCountBelief Delta Bel j L) L i := by
  cases he : L i with
  | none => exact False.elim (highSet_present C L i hi he)
  | some b =>
      have hb0 : 0 ≤ b := by
        simpa only [he, entryBid] using
          (feasibleObservedList_iff_nonnegative j L).mp hL i
      have hc := (compatibleList_iff C d (1-ξ) L hcomp.1).mp hcomp i b he
      have ht := (mem_highSet C L i).mp hi
      simp only [he, Information.tag] at ht
      rcases ht with ht | ht
      · have hb : C.label b = 1 := Fin.ext (congrArg (fun k : Fin 4 => k.val) ht)
        have hlow := (affine_receipt_bounds Delta Bel η hη0 hη1 hA j L i b hb0).1
        have hbc := hc.2.1 hb
        have hkeq : (1+η)/2 = 1-ξ := by rw [hξeq]; ring
        rw [hkeq] at hlow
        simpa only [beliefReceipts, he] using hbc.trans_le hlow
      · have hb : C.label b = 2 := Fin.ext (congrArg (fun k : Fin 4 => k.val) ht)
        simp only [beliefReceipts, he]
        rw [private_receipt Γ C d ξ R hξ hξ1 hfull H η hη0 hη1 hA
          hR hRC hdR j L hL hcomp i b he hb]
        exact hc.2.2 hb

theorem low_receipt_le (hd : 0 ≤ d) (j : Fin 2) (L : LocalList m)
    (hL : FeasibleObservedList j L) (hcomp : CompatibleList C d (1-ξ) L)
    (i : Fin m) (hi : i ∉ highSet C L) :
    beliefReceipts (Delta).A (posteriorCountBelief Delta Bel j L) L i ≤ d := by
  cases he : L i with
  | none => simpa only [beliefReceipts, he] using hd
  | some b =>
      have hc := (compatibleList_iff C d (1-ξ) L hcomp.1).mp hcomp i b he
      have hb : C.label b = 0 := by
        rcases hk : C.label b with ⟨k,hklt⟩
        interval_cases k
        · rfl
        · exact False.elim (hi ((mem_highSet C L i).mpr (Or.inl (by simp [he, Information.tag, hk]))))
        · exact False.elim (hi ((mem_highSet C L i).mpr (Or.inr (by simp [he, Information.tag, hk]))))
      have hh := (Affine.Hybrid.beliefReceipts_nonneg_le Delta Bel j L
        ((feasibleObservedList_iff_nonnegative j L).mp hL) i).2
      exact hh.trans (by simpa only [he, entryBid] using hc.1 hb)

theorem low_visible_card (L : LocalList m) :
    (ExactLow.visible (Information.part C 0 L)).card = Information.localCount C L 0 := by
  classical
  simp only [ExactLow.visible, Finset.card_eq_sum_ones, Finset.sum_filter,
    Information.localCount]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : Information.tag C (L i) = 0
  · have hp : L i ≠ none := by
      intro hn
      simp [hn, Information.tag] at ht
    simp [Information.part, ht, hp]
  · simp [Information.part, ht]

theorem low_vector (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hξeq : ξ = (1-η)/2)
    (hseed : Γ.seedLaw = volume)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d (1-ξ) L)
    (hnot : L ∉ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j) :
    (fun i => if i ∈ highSet C L then 0 else
      beliefReceipts (Delta).A (posteriorCountBelief Delta Bel j L) L i) =
      ExactLow.receipt ξ hξ hξ1 (Information.part C 0 L)
        (Information.ownResidual C c L) (Information.otherResidual C c L) := by
  classical
  funext i
  by_cases hh : i ∈ highSet C L
  · have ht := highSet_not_low C L i hh
    simp [if_pos hh, ExactLow.receipt, Information.part, ht,
      Existence.PayOnceBounded.listBids]
  · rw [if_neg hh]
    cases he : L i with
    | none => simp [beliefReceipts, he, ExactLow.receipt, Information.part,
        Information.tag, Existence.PayOnceBounded.listBids]
    | some b =>
        have hb : C.label b = 0 := by
          rcases hk : C.label b with ⟨k,hklt⟩
          interval_cases k
          · rfl
          · exact False.elim (hh ((mem_highSet C L i).mpr (Or.inl (by simp [he, Information.tag, hk]))))
          · exact False.elim (hh ((mem_highSet C L i).mpr (Or.inr (by simp [he, Information.tag, hk]))))
        simp only [beliefReceipts, he]
        exact LowReceipts.low_receipt Delta Bel hseed C d ξ η hξ hξ1 hη0 hη1 hA hξeq
          (LowReceipts.implementation_low_factors Γ C d ξ R hξ hξ1 hfull H) j L
          (class_support Γ C d ξ R hξ hξ1 hfull H hR hRC hdR j L hL hcomp hnot)
          i b he hb

theorem low_optimal (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hξeq : ξ = (1-η)/2)
    (hseed : Γ.seedLaw = volume)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d (1-ξ) L) (z : unitInterval) :
    Finite.Optimal (c - (highSet C L).card)
      (fun i => if i ∈ highSet C L then 0 else
        beliefReceipts (Delta).A (posteriorCountBelief Delta Bel j L) L i)
      (DirectGame.lowSelect C ξ hξ hξ1 c L z) := by
  classical
  by_cases hs : c ≤ (highSet C L).card
  · have hz := DirectGame.lowSelect_empty_of_high_saturated C ξ hξ hξ1 c L z hs
    rw [hz, Nat.sub_eq_zero_of_le hs]
    refine ⟨by simp, ?_⟩
    intro T hT
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hT)
    simp only [hT0, Finset.sum_empty, le_refl]
  · have hnot : L ∉ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j :=
      fun hb => hs hb.1.1
    rw [low_vector Γ C d ξ R hξ hξ1 hfull H η hη0 hη1 hA hξeq hseed
      hR hRC hdR j L hL hcomp hnot]
    have he : min (ExactLow.visible (Information.part C 0 L)).card
        (c - (highSet C L).card) = Information.ownResidual C c L := by
      rw [low_visible_card C L, highSet_card]
      unfold Information.ownResidual
      omega
    have hh := ExactLow.select_optimal_clipped ξ hξ hξ1 (Information.part C 0 L)
      (c - (highSet C L).card) (Information.otherResidual C c L) z
    rw [he] at hh
    exact hh

theorem spare_high_vector (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hξeq : ξ = (1-η)/2)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d (1-ξ) L) (hspare : otherHigh C L < c)
    (i : Fin m) (hi : i ∈ highSet C L) :
    beliefReceipts (Delta).A (posteriorCountBelief Delta Bel j L) L i =
      highWeight C (1-ξ) L i := by
  have hnot : L ∉ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j :=
    fun hb => (not_le.mpr hspare) hb.1.2
  have hpost : (Bel).posterior j L =
      (HigherPosterior.posterior Delta C d (1-ξ) R hfull).posterior j L :=
    Implementation.belief_eq_original Γ C d ξ R hξ hξ1 hfull H j L hnot
  have hcount := countBelief_congr Delta Bel (HigherPosterior.posterior Delta C d (1-ξ) R hfull)
    j L hpost
  rw [hcount]
  cases he : L i with
  | none => exact False.elim (highSet_present C L i hi he)
  | some b =>
      have ht := (mem_highSet C L i).mp hi
      simp only [he, Information.tag] at ht
      rcases ht with ht | ht
      · have hb : C.label b = 1 := Fin.ext (congrArg (fun k : Fin 4 => k.val) ht)
        simp only [beliefReceipts, he]
        have hκ : 1-ξ = (1+η)/2 := by rw [hξeq]; ring
        rw [posterior_active_receipt_of_spare Delta C d (1-ξ) R η hη0 hη1 hA hκ
          hR hRC hdR hfull NormH
          (Implementation.policy_high_factors Γ C d ξ R hξ hξ1 hfull H)
          j L hL hcomp hspare i b he hb]
        simp [highWeight, he, Information.tag, hb, entryBid]
      · have hb : C.label b = 2 := Fin.ext (congrArg (fun k : Fin 4 => k.val) ht)
        simp only [beliefReceipts, he]
        rw [posterior_private_receipt Delta C d (1-ξ) R η hη0 hη1 hA
          hR hRC hdR hfull j L hL hcomp i b he hb]
        simp [highWeight, he, Information.tag, hb, entryBid]

theorem saturated_high_optimal (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d (1-ξ) L) (hsat : BothSaturated C c L)
    (z : unitInterval) :
    Finite.Optimal c
      (fun i => if i ∈ highSet C L then
        beliefReceipts (Delta).A (posteriorCountBelief Delta Bel j L) L i else 0)
      ((NormH).select j L z) := by
  classical
  by_cases hg : L ∈ Continuation.core Γ C d (1-ξ) R hfull H.selector j
  · change Finite.Optimal c
      (fun i => if i ∈ highSet C L then
        beliefReceipts Γ.A (posteriorCountBelief Delta Bel j L) L i else 0)
      ((NormH).select j L z)
    rw [SaturatedReceipts.high_receipt_eq_on_core Γ C d ξ R η hξ hξ1
      hη0 hη1 hA hR hRC hdR hfull H j L hL hcomp hg hsat]
    exact NormalizedContinuation.select_optimal_core Γ C d (1-ξ) R hfull H.selector j L hg hsat z
  · have hbad : L ∈ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j := ⟨hsat,hg⟩
    have hr := receipts_of_private_posterior Delta Bel η hη0 hη1 hA j L
      (Implementation.belief_eq_private_of_bad Γ C d ξ R hξ hξ1 hfull H j L hbad)
    rw [hr]
    change Finite.Optimal c (fun i => if i ∈ highSet C L then entryBid (L i) else 0)
      (NormalizedContinuation.select Γ C d (1-ξ) R hfull H.selector j L z)
    rw [NormalizedContinuation.select, if_pos hsat, if_neg hg]
    have he : (fun i => if i ∈ highSet C L then entryBid (L i) else 0) =
        fun i => entryBid (weightedPart C 1 L i) := by
      funext i
      rw [weightedPart_receipt]
      simp only [highWeight, one_mul, ite_self]
    rw [he]
    exact HighestBid.selection_optimal (weightedPart C 1 L) c

theorem proposer_optimal (hd : 0 ≤ d) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hξeq : ξ = (1-η)/2)
    (hseed : Γ.seedLaw = volume)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R) :
    ∀ j L z,
      Finite.Optimal c (beliefReceipts (Delta).A (posteriorCountBelief Delta Bel j L) L)
        ((Delta).policy j L z).val := by
  classical
  intro j L z
  by_cases hcomp : CompatibleList C d (1-ξ) L
  · have hL : FeasibleObservedList j L :=
      (feasibleObservedList_iff_nonnegative j L).mpr hcomp.1
    let r := beliefReceipts (Delta).A (posteriorCountBelief Delta Bel j L) L
    have hr : ∀ i, 0 ≤ r i := fun i =>
      (Affine.Hybrid.beliefReceipts_nonneg_le Delta Bel j L
        ((feasibleObservedList_iff_nonnegative j L).mp hL) i).1
    have hhigh : ∀ i ∈ highSet C L, d < r i :=
      high_receipt_gt Γ C d ξ R hξ hξ1 hfull H η hη0 hη1 hA hξeq
        hR hRC hdR j L hL hcomp
    have hpriority : ∀ i ∈ highSet C L, ∀ k ∉ highSet C L, r k ≤ r i := by
      intro i hi k hk
      exact (low_receipt_le Γ C d ξ R hξ hξ1 hfull H hd j L hL hcomp k hk).trans
        (hhigh i hi).le
    have hdisj : Disjoint (highSet C L) (DirectGame.lowSelect C ξ hξ hξ1 c L z) := by
      apply Finset.disjoint_left.mpr
      intro i hi hl
      exact highSet_not_low C L i hi (DirectGame.lowSelect_present C ξ hξ hξ1 c L z i hl).2
    change Finite.Optimal c r (DirectGame.selection C d ξ hξ hξ1 c NormH j L z)
    rw [DirectGame.selection, if_pos hcomp]
    exact union_optimal C (1-ξ) c NormH j L z r
      (DirectGame.lowSelect C ξ hξ hξ1 c L z) hr
      (fun i hi => hd.trans_lt (hhigh i hi)) hpriority hdisj
      (low_optimal Γ C d ξ R hξ hξ1 hfull H η hη0 hη1 hA hξeq hseed
        hR hRC hdR j L hL hcomp z)
      (fun hs => spare_high_vector Γ C d ξ R hξ hξ1 hfull H η hη0 hη1 hA hξeq
        hR hRC hdR j L hL hcomp hs)
      (fun hown hother => saturated_high_optimal Γ C d ξ R hξ hξ1 hfull H η hη0 hη1 hA
        hR hRC hdR j L hL hcomp ⟨hown,hother⟩ z)
  · have hpost := Implementation.belief_eq_private_of_incompatible Γ C d ξ R hξ hξ1 hfull H j L hcomp
    rw [receipts_of_private_posterior Delta Bel η hη0 hη1 hA j L hpost]
    change Finite.Optimal c (fun i => entryBid (L i))
      (DirectGame.selection C d ξ hξ hξ1 c NormH j L z)
    rw [DirectGame.selection, if_neg hcomp]
    exact HighestBid.selection_optimal L c

end FCAppendix.Appendix08.GeneralLow.ProposerOptimality
