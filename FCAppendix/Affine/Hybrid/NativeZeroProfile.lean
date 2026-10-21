import FCAppendix.Affine.Hybrid.NativeZeroEnvelope
import FCAppendix.Affine.Hybrid.CollapsedRowPayoff

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
open scoped BigOperators
variable {m : ℕ}

lemma actualContext_same_rivals (U : ℝ) (z z' : UserProfile m 2)
    (hz:z∈classifiedProfiles m U) (hz':z'∈classifiedProfiles m U)
    (i : Fin m) (hf:(z i).1.2.bid ≤ U) (hf':(z' i).1.2.bid ≤ U)
    (hother:∀k,k≠i → z' k=z k) :
    actualContext U z'=contextAtBid (actualContext U z) i (z' i).1.2.bid:=by
  have hu (j : Fin 2):TaggedLocal.upperAt (classifiedKind U z') (drawsRealization z') j=
      TaggedLocal.upperAt (classifiedKind U z) (drawsRealization z) j:=by
    unfold TaggedLocal.upperAt
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk:k=i
    · subst k
      simp [classifiedKind,hf,hf']
    · simp only [classifiedKind,drawsRealization,hother k hk]
      rfl
  apply Prod.ext
  · change broadcastPart U (observe (drawsRealization z') 0)=
      Function.update (broadcastPart U (observe (drawsRealization z) 0)) i (some (z' i).1.2.bid)
    rw [broadcastPart_observe z' hz' 0,broadcastPart_observe z hz 0]
    funext k
    by_cases hk:k=i
    · subst k
      simp only [Function.update_self,if_pos hf']
    · rw [Function.update_of_ne hk,hother k hk]
  · exact Prod.ext (hu 0) (hu 1)

theorem actual_profile_zero_payoff_le_positive (ξ : ℝ) (hξ:0<ξ) (hξh:ξ ≤ 1/2)
    (c : ℕ) (U : ℝ) (z z' : UserProfile m 2)
    (hz:z∈classifiedProfiles m U) (hz':z'∈classifiedProfiles m U)
    (i : Fin m) (hf:(z i).1.2.bid ≤ U) (hf':(z' i).1.2.bid ≤ U)
    (hother:∀k,k≠i → z' k=z k) (hzbid:(z i).1.2.bid=0)
    (hy:0<(z' i).1.2.bid) (w : ℝ) (hw:0 ≤ w) :
    let hξ1:ξ<1:=by linarith
    seedAveragePayoff ξ hξ hξ1 c (actualContext U z) i w ≤
      seedAveragePayoff ξ hξ hξ1 c (actualContext U z') i w+2*(z' i).1.2.bid:=by
  dsimp only
  have h0:(actualContext U z).1 i=some 0:=by
    change broadcastPart U (observe (drawsRealization z) 0) i=some 0
    rw [broadcastPart_observe z hz 0]
    have hU:0 ≤ U:=by simpa only [hzbid] using hf
    simp only [hzbid,if_pos hU]
  have hh:=context_zero_payoff_le_positive ξ hξ hξh c (actualContext U z) i h0 w hw (z' i).1.2.bid hy
  dsimp only at hh
  rw [←actualContext_same_rivals U z z' hz hz' i hf hf' hother] at hh
  exact hh

end FCAppendix.Affine.Hybrid.NativeContinuation
