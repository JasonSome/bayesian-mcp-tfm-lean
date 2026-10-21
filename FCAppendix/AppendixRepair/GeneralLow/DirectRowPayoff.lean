import FCAppendix.AppendixRepair.GeneralLow.ExactLowPayoff
import FCAppendix.Affine.Hybrid.NativeFocalReindex

set_option maxHeartbeats 1800000
noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Affine.Hybrid.NativeContinuation
open FCAppendix.AppendixRepair.GeneralLow
open Existence.PayOnceBounded (listBids)

variable {N : ℕ}

theorem direct_focal_low_payoff (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    {d U : ℝ} (hdU : d ≤ U) (z : UserProfile (N + 1) 2)
    (hz : z ∈ classifiedProfiles (N + 1) U) (i : Fin (N + 1))
    (hf : (z i).1.2.bid ≤ d) (w : ℝ)
    (hgeneric : rowCopyGeneric (1 - ξ) (z i).1.2.bid (collapsedDeletedRow d U z i)) :
    let X := actualContext U z
    let A := upperSet d X.1
    let L := eraseActiveList A X.1
    ExactLow.seedAveragePayoff ξ hξ hξ1 L
      (min (ExactLow.visible L).card (residual c 0 X - A.card))
      (min (ExactLow.visible L).card (residual c 1 X - A.card)) i w =
        literalRowPayoff ξ c w ((z i).1.2.bid, collapsedDeletedRow d U z i) := by
  dsimp only
  let e := focalIndex i
  let zn := z ∘ e
  let X := actualContext U z
  let A := upperSet d X.1
  let L := eraseActiveList A X.1
  let T := (receivedTemplate L (residual c 0 X - A.card)
    (residual c 1 X - A.card)).clipped
  let b := ResidualPotential.bid L
  let omega := collapsedDeletedRow d U z i
  let bn := rowBids (z i).1.2.bid omega
  have he0 : e 0 = i := focalIndex_zero i
  have hzn : zn ∈ classifiedProfiles (N + 1) U := fun k => hz (e k)
  have hfn : (zn 0).1.2.bid ≤ d := by simpa only [zn, Function.comp_apply, he0] using hf
  have hctx : actualContext U zn = reindexContext e X := actualContext_reindex e U z
  have hrow : collapsedProfileRow d U zn = omega := collapsedProfileRow_focalIndex d U z i
  have htn : T.relabel e.symm = patternTemplate c (fun j => (omega j).1) := by
    have ht := collapsed_clipped_template (c := c) hdU zn hzn hfn
    rw [hctx] at ht
    dsimp only at ht
    rw [clipped_template_reindex] at ht
    exact ht.trans (by rw [hrow])
  have hbn : b ∘ e = bn := by
    have hh := collapsed_low_bid hdU zn hzn hfn
    rw [hctx] at hh
    change ResidualPotential.bid (eraseActiveList (upperSet d (X.1 ∘ e)) (X.1 ∘ e)) = _ at hh
    rw [erasedList_reindex] at hh
    change b ∘ e = _ at hh
    simpa only [zn, Function.comp_apply, he0, hrow] using hh
  have hb : b = bn ∘ e.symm := by
    funext k
    have hh := congrFun hbn (e.symm k)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh
  have hgen : ∀ P Q, T.Feasible P → T.Feasible Q →
      CompleteInformation.potential (1 - ξ) b P.1 P.2 =
        CompleteInformation.potential (1 - ξ) b Q.1 Q.2 → focalCopy P i = focalCopy Q i := by
    intro P Q _ _ he
    have hp := potential_relabel (1 - ξ) b e.symm P
    have hq := potential_relabel (1 - ξ) b e.symm Q
    change CompleteInformation.potential (1 - ξ) (b ∘ e) _ _ = _ at hp hq
    rw [hbn] at hp hq
    have hc := hgeneric (relabelPair e.symm P) (relabelPair e.symm Q)
      (hp.trans (he.trans hq.symm))
    have h0 : e.symm i = 0 := by rw [← he0]; exact e.symm_apply_apply 0
    have hpC := focalCopy_relabel e.symm P i
    have hqC := focalCopy_relabel e.symm Q i
    rw [h0] at hpC hqC
    exact hpC.symm.trans (hc.trans hqC)
  have hnonneg : NonnegativeList L := by
    intro k
    by_cases hk : k ∈ A
    · simp [L, eraseActiveList, hk, entryBid]
    · simpa [L, eraseActiveList, hk] using actualContext_nonnegative U z hz k
  have hbid : listBids L = b := ExactLow.listBids_eq_residualBid L hnonneg
  have hT : ExactLow.template L
      (min (ExactLow.visible L).card (residual c 0 X - A.card))
      (min (ExactLow.visible L).card (residual c 1 X - A.card)) = T := rfl
  have hout := ExactLow.seed_average_payoff_eq_residualPayoff ξ hξ hξ1 L
    (min (ExactLow.visible L).card (residual c 0 X - A.card))
    (min (ExactLow.visible L).card (residual c 1 X - A.card)) i w
    (by simpa only [hT, hbid] using hgen)
  change ExactLow.seedAveragePayoff ξ hξ hξ1 L _ _ i w = _
  rw [hout, hT, hbid]
  change T.userPayoff ξ w b i = _
  let S := patternTemplate c (fun j => (omega j).1)
  have ht : T = S.relabel e := by
    change T = (patternTemplate c (fun j => (omega j).1)).relabel e
    rw [← htn]
    exact (T.relabel_symm e.symm).symm
  rw [ht, hb, ← he0]
  exact S.userPayoff_relabel e hξ hξ1 w bn 0 (fun P Q _ _ hh => hgeneric P Q hh)

end FCAppendix.Appendix08.GeneralLow
