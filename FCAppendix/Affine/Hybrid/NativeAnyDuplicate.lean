import FCAppendix.Affine.Hybrid.NativeFocalReindex
import FCAppendix.Affine.Hybrid.NativeDuplicateUnderflow

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
variable {N : ℕ}

theorem native_focal_duplicate_implies_bothUnderflow (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (Gamma : FiniteGame (N+1) 2 c unitInterval) {d U : ℝ} (hd:0 ≤ d) (hdU:d ≤ U)
    (z : UserProfile (N+1) 2) (hz:z∈classifiedProfiles (N+1) U) (i : Fin (N+1))
    (hf:(z i).1.2.bid ≤ d)
    (hactive:∀k∈upperSet d (actualContext U z).1,d<(1-ξ)*entryBid ((actualContext U z).1 k))
    (s : Fin 2→unitInterval)
    (hdup:inclusionCount (drawsRealization z)
      ((contextPolicy ξ hξ hξ1 c).nativeGame Gamma U).policy s i=2) :
    BothUnderflow c (fun j=>(collapsedDeletedRow d U z i j).1):=by
  let e:=focalIndex i
  let zn:=z ∘ e
  let X:=actualContext U z
  let A:=upperSet d X.1
  let omega:=collapsedDeletedRow d U z i
  have he0:e 0=i:=focalIndex_zero i
  have hzn:zn∈classifiedProfiles (N+1) U:=fun k=>hz (e k)
  have hfn:(zn 0).1.2.bid ≤ d:=by simpa only [zn,Function.comp_apply,he0] using hf
  have hctx:actualContext U zn=reindexContext e X:=actualContext_reindex e U z
  have hrow:collapsedProfileRow d U zn=omega:=collapsedProfileRow_focalIndex d U z i
  have hcard:(upperSet d (actualContext U zn).1).card=A.card:=by
    rw [hctx]
    change (upperSet d (X.1 ∘ e)).card=A.card
    rw [upperSet_reindex,Finset.card_map]
  have hr (j : Fin 2):residual c j (actualContext U zn)=residual c j X:=by rw [hctx];rfl
  have hbid:=actualContext_entryBid U z hz i (hf.trans hdU)
  have hi:i∉A:=by
    intro hk
    have hgt:=upperSet_entry_gt X.1 i hk
    rw [hbid] at hgt
    linarith
  have hlow:∀k∉A,entryBid (X.1 k) ≤ d:=fun k hk=>nonupper_entry_le hd _ k hk
  rw [ContextPolicy.native_inclusionCount_eq_focalCopy _ Gamma U z hz s i (hf.trans hdU)] at hdup
  have hboth:i∈select ξ hξ hξ1 c 0 X (s 0) ∧ i∈select ξ hξ hξ1 c 1 X (s 1):=by
    by_cases h0:i∈select ξ hξ hξ1 c 0 X (s 0)
    · by_cases h1:i∈select ξ hξ hξ1 c 1 X (s 1)
      · exact ⟨h0,h1⟩
      · simp [ContextPolicy.selectionPair,contextPolicy,focalCopy,X,h0,h1] at hdup
    · by_cases h1:i∈select ξ hξ hξ1 c 1 X (s 1) <;>
        simp [ContextPolicy.selectionPair,contextPolicy,focalCopy,X,h0,h1] at hdup
  have hu (j : Fin 2):classCount 1 omega+classCount (upperTag j) omega<c:=by
    have hs:i∈select ξ hξ hξ1 c j X (s j):=by fin_cases j <;> tauto
    have hh:=low_included_implies_active_underflow ξ hξ hξ1 c X (actualContext_nonnegative U z hz)
      j (s j) d A hactive hlow i hi hs
    have hn:residual c j (actualContext U zn)-(upperSet d (actualContext U zn).1).card=
        c-classCount 1 (collapsedProfileRow d U zn)-classCount (upperTag j) (collapsedProfileRow d U zn):=
      (collapsed_context_data (c:=c) hdU zn hzn hfn).2.2 j
    rw [hr j,hcard,hrow] at hn
    omega
  constructor
  · rw [sum_firstHigher]
    exact hu 0
  · rw [sum_secondHigher]
    exact hu 1

end FCAppendix.Affine.Hybrid.NativeContinuation
