import FCAppendix.Affine.Hybrid.NativeLowContextPayoff
import FCAppendix.Affine.Hybrid.CollapsedContext
import FCAppendix.Affine.LowBody.NoisyExpectedLoss

set_option maxHeartbeats 1600000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
open scoped BigOperators
variable {N : ℕ}

lemma actualContext_nonnegative (U : ℝ) (z : UserProfile (N+1) 2)
    (hz:z∈classifiedProfiles (N+1) U) : NonnegativeList (actualContext U z).1:=by
  rw [←observedContext_eq_actual z hz 0]
  exact nonnegative_observedContext U 0 _
    ((feasibleObservedList_iff_nonnegative 0 _).mp ⟨z,rfl⟩)

lemma received_row_support (b : ℝ) (omega : Fin N→RowRival) (r0 r1 c : ℕ) :
    (receivedTemplate (rowLowList b omega) r0 r1).support=
      (patternTemplate c (fun j=>(omega j).1)).support:=by
  ext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [receivedTemplate,patternTemplate,rowLowList]
  · by_cases hj:(omega j).1=0 <;>
      simp [receivedTemplate,patternTemplate,rowLowList,patternRow,hj]

lemma rowResidual_tags (c : ℕ) (j : Fin 2) (omega : Fin N→RowRival) :
    rowResidual c j (patternRow (fun k=>(omega k).1))=rowResidual c j omega:=rfl

lemma collapsed_clipped_template {c : ℕ} {d U : ℝ} (hdU:d ≤ U)
    (z : UserProfile (N+1) 2) (hz:z∈classifiedProfiles (N+1) U) (hf:(z 0).1.2.bid ≤ d) :
    let X:=actualContext U z
    let A:=upperSet d X.1
    (receivedTemplate (eraseActiveList A X.1) (residual c 0 X-A.card)
      (residual c 1 X-A.card)).clipped=
      patternTemplate c (fun j=>(collapsedProfileRow d U z j).1):=by
  obtain ⟨hlist,_,_⟩:=collapsed_context_data (c:=c) hdU z hz hf
  have hs:=received_row_support (z 0).1.2.bid (collapsedProfileRow d U z)
    (residual c 0 (actualContext U z)-(upperSet d (actualContext U z).1).card)
    (residual c 1 (actualContext U z)-(upperSet d (actualContext U z).1).card) c
  have hext (T S : PureTemplate (Fin (N+1))) (hs:T.support=S.support)
      (h0:T.residual₀=S.residual₀) (h1:T.residual₁=S.residual₁) : T=S:=by
    cases T;cases S;simp_all
  apply hext
  · simpa only [PureTemplate.clipped,hlist] using hs
  · exact (collapsed_rowResidual (c:=c) hdU z hz hf 0).symm
  · exact (collapsed_rowResidual (c:=c) hdU z hz hf 1).symm

lemma collapsed_low_bid {d U : ℝ} (hdU:d ≤ U) (z : UserProfile (N+1) 2)
    (hz:z∈classifiedProfiles (N+1) U) (hf:(z 0).1.2.bid ≤ d) :
    ResidualPotential.bid (eraseActiveList (upperSet d (actualContext U z).1) (actualContext U z).1)=
      rowBids (z 0).1.2.bid (collapsedProfileRow d U z):=by
  obtain ⟨hlist,_,_⟩:=collapsed_context_data (c:=0) hdU z hz hf
  rw [hlist]
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact max_eq_left (z 0).1.2.bid_nonneg
  · change max (entryBid (if (collapsedProfileRow d U z j).1=0 then
        some (collapsedProfileRow d U z j).2 else none)) 0=
        (if (collapsedProfileRow d U z j).1=0 then (collapsedProfileRow d U z j).2 else 0)
    by_cases hj:(collapsedProfileRow d U z j).1=0
    · simp only [if_pos hj,entryBid]
      have hnonneg:0 ≤ (collapsedProfileRow d U z j).2:=by
        change 0 ≤ (collapseAction d U ((z j.succ).1.2,(z j.succ).2)).2
        unfold collapseAction
        split
        · exact (z j.succ).1.2.bid_nonneg
        · split
          · exact le_rfl
          · unfold upperRow
            split <;> exact le_rfl
      exact max_eq_left hnonneg
    · simp only [if_neg hj,entryBid,max_self]

theorem collapsed_context_low_payoff (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    {d U : ℝ} (hd:0 ≤ d) (hdU:d ≤ U) (z : UserProfile (N+1) 2)
    (hz:z∈classifiedProfiles (N+1) U) (hf:(z 0).1.2.bid ≤ d) (hpos:0<(z 0).1.2.bid)
    (hactive:∀i∈upperSet d (actualContext U z).1,
      d<(1-ξ)*entryBid ((actualContext U z).1 i)) (w : ℝ)
    (hgeneric:∀P Q,(patternTemplate c (fun j=>(collapsedProfileRow d U z j).1)).Feasible P →
      (patternTemplate c (fun j=>(collapsedProfileRow d U z j).1)).Feasible Q →
      CompleteInformation.potential (1-ξ) (rowBids (z 0).1.2.bid (collapsedProfileRow d U z)) P.1 P.2=
        CompleteInformation.potential (1-ξ) (rowBids (z 0).1.2.bid (collapsedProfileRow d U z)) Q.1 Q.2 →
      focalCopy P 0=focalCopy Q 0) :
    (∫s : Fin 2→unitInterval,purePayoff (1-ξ) w (fun k=>entryBid ((actualContext U z).1 k))
      (select ξ hξ hξ1 c 0 (actualContext U z) (s 0),
        select ξ hξ hξ1 c 1 (actualContext U z) (s 1)) 0
      ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)))=
      literalRowPayoff ξ c w ((z 0).1.2.bid,collapsedProfileRow d U z):=by
  have hbid:=actualContext_entryBid U z hz 0 (hf.trans hdU)
  have hi:(0:Fin (N+1))∉upperSet d (actualContext U z).1:=by
    intro h
    have hh:=upperSet_entry_gt _ 0 h
    rw [hbid] at hh
    linarith
  have hlow:∀i∉upperSet d (actualContext U z).1,entryBid ((actualContext U z).1 i) ≤ d:=
    fun i hi=>nonupper_entry_le hd _ i hi
  have hh:=context_low_payoff ξ hξ hξ1 c (actualContext U z) (actualContext_nonnegative U z hz)
    d hd _ hactive hlow 0 hi (by rw [hbid];exact hpos) w
  have hT:=collapsed_clipped_template (c:=c) hdU z hz hf
  have hb:=collapsed_low_bid hdU z hz hf
  dsimp only at hh
  rw [hT,hb] at hh
  exact hh hgeneric

end FCAppendix.Affine.Hybrid.NativeContinuation
