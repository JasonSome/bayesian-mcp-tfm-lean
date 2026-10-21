import FCAppendix.Affine.Hybrid.CollapsedRowPayoff
import FCAppendix.Affine.Hybrid.RowCopyGeneric

set_option maxHeartbeats 1600000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
open scoped BigOperators
variable {m N : ℕ}

def focalIndex (i : Fin (N+1)) : Equiv.Perm (Fin (N+1)):=
  (finSuccEquiv N).trans (finSuccEquiv' i).symm

@[simp] lemma focalIndex_zero (i : Fin (N+1)) : focalIndex i 0=i:=by
  simp [focalIndex]

@[simp] lemma focalIndex_succ (i : Fin (N+1)) (j : Fin N) :
    focalIndex i j.succ=i.succAbove j:=by simp [focalIndex]

def reindexContext (e : Equiv.Perm (Fin m)) (X : ClassifiedContext m) : ClassifiedContext m:=
  (X.1 ∘ e,X.2)

lemma actualContext_reindex (e : Equiv.Perm (Fin m)) (U : ℝ) (z : UserProfile m 2) :
    actualContext U (z ∘ e)=reindexContext e (actualContext U z):=by
  apply Prod.ext
  · funext i
    rfl
  · apply Prod.ext
    · change (∑i : Fin m,if classifiedKind U (z ∘ e) i=2 ∧
        (0:Fin 2)∈(drawsRealization (z ∘ e)).recipients i then 1 else 0)=_
      exact Equiv.sum_comp e (fun i=>if classifiedKind U z i=2 ∧
        (0:Fin 2)∈(drawsRealization z).recipients i then 1 else 0)
    · change (∑i : Fin m,if classifiedKind U (z ∘ e) i=2 ∧
        (1:Fin 2)∈(drawsRealization (z ∘ e)).recipients i then 1 else 0)=_
      exact Equiv.sum_comp e (fun i=>if classifiedKind U z i=2 ∧
        (1:Fin 2)∈(drawsRealization z).recipients i then 1 else 0)

lemma upperSet_reindex (e : Equiv.Perm (Fin m)) (d : ℝ) (L : LocalList m) :
    upperSet d (L ∘ e)=(upperSet d L).map e.symm.toEmbedding:=by
  ext i
  simp [upperSet]

lemma erasedList_reindex (e : Equiv.Perm (Fin m)) (d : ℝ) (L : LocalList m) :
    eraseActiveList (upperSet d (L ∘ e)) (L ∘ e)=eraseActiveList (upperSet d L) L ∘ e:=by
  funext i
  simp [eraseActiveList,upperSet]

lemma clipped_template_reindex (e : Equiv.Perm (Fin m)) (d : ℝ) (c : ℕ)
    (X : ClassifiedContext m) :
    let A:=upperSet d X.1
    let Y:=reindexContext e X
    let B:=upperSet d Y.1
    (receivedTemplate (eraseActiveList B Y.1) (residual c 0 Y-B.card)
      (residual c 1 Y-B.card)).clipped=
      ((receivedTemplate (eraseActiveList A X.1) (residual c 0 X-A.card)
        (residual c 1 X-A.card)).clipped).relabel e.symm:=by
  dsimp only
  have ha:(upperSet d (reindexContext e X).1).card=(upperSet d X.1).card:=by
    rw [show (reindexContext e X).1=X.1 ∘ e from rfl,upperSet_reindex,Finset.card_map]
  have hs:Finset.univ.filter (fun i=>eraseActiveList (upperSet d (reindexContext e X).1)
        (reindexContext e X).1 i≠none)=
      (Finset.univ.filter (fun i=>eraseActiveList (upperSet d X.1) X.1 i≠none)).map e.symm.toEmbedding:=by
    rw [show (reindexContext e X).1=X.1 ∘ e from rfl,erasedList_reindex]
    ext i
    simp
  have hext (T S : PureTemplate (Fin m)) (hs:T.support=S.support)
      (h0:T.residual₀=S.residual₀) (h1:T.residual₁=S.residual₁) : T=S:=by
    cases T;cases S;simp_all
  apply hext
  · exact hs
  · simp only [PureTemplate.relabel,PureTemplate.clipped,receivedTemplate]
    rw [hs,Finset.card_map,ha]
    rfl
  · simp only [PureTemplate.relabel,PureTemplate.clipped,receivedTemplate]
    rw [hs,Finset.card_map,ha]
    rfl

def collapsedDeletedRow (d U : ℝ) (z : UserProfile (N+1) 2) (i : Fin (N+1)) : Fin N→RowRival:=
  fun j=>collapseAction d U ((z (i.succAbove j)).1.2,(z (i.succAbove j)).2)

lemma collapsedProfileRow_focalIndex (d U : ℝ) (z : UserProfile (N+1) 2) (i : Fin (N+1)) :
    collapsedProfileRow d U (z ∘ focalIndex i)=collapsedDeletedRow d U z i:=by
  funext j
  simp [collapsedProfileRow,collapsedDeletedRow]

theorem native_focal_context_low_payoff (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    {d U : ℝ} (hd:0 ≤ d) (hdU:d ≤ U) (z : UserProfile (N+1) 2)
    (hz:z∈classifiedProfiles (N+1) U) (i : Fin (N+1))
    (hf:(z i).1.2.bid ≤ d) (hpos:0<(z i).1.2.bid)
    (hactive:∀k∈upperSet d (actualContext U z).1,
      d<(1-ξ)*entryBid ((actualContext U z).1 k)) (w : ℝ)
    (hgeneric:rowCopyGeneric (1-ξ) (z i).1.2.bid (collapsedDeletedRow d U z i)) :
    (∫s : Fin 2→unitInterval,purePayoff (1-ξ) w (fun k=>entryBid ((actualContext U z).1 k))
      (select ξ hξ hξ1 c 0 (actualContext U z) (s 0),
        select ξ hξ hξ1 c 1 (actualContext U z) (s 1)) i
      ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)))=
      literalRowPayoff ξ c w ((z i).1.2.bid,collapsedDeletedRow d U z i):=by
  let e:=focalIndex i
  let zn:=z ∘ e
  let X:=actualContext U z
  let A:=upperSet d X.1
  let T:=(receivedTemplate (eraseActiveList A X.1) (residual c 0 X-A.card)
    (residual c 1 X-A.card)).clipped
  let b:=ResidualPotential.bid (eraseActiveList A X.1)
  let omega:=collapsedDeletedRow d U z i
  let bn:=rowBids (z i).1.2.bid omega
  have he0:e 0=i:=focalIndex_zero i
  have hzn:zn∈classifiedProfiles (N+1) U:=fun k=>hz (e k)
  have hfn:(zn 0).1.2.bid ≤ d:=by simpa only [zn,Function.comp_apply,he0] using hf
  have hctx:actualContext U zn=reindexContext e X:=actualContext_reindex e U z
  have hrow:collapsedProfileRow d U zn=omega:=collapsedProfileRow_focalIndex d U z i
  have htn:T.relabel e.symm=patternTemplate c (fun j=>(omega j).1):=by
    have ht:=collapsed_clipped_template (c:=c) hdU zn hzn hfn
    rw [hctx] at ht
    dsimp only at ht
    rw [clipped_template_reindex] at ht
    exact ht.trans (by rw [hrow])
  have hbn:b ∘ e=bn:=by
    have hh:=collapsed_low_bid hdU zn hzn hfn
    rw [hctx] at hh
    change ResidualPotential.bid (eraseActiveList (upperSet d (X.1 ∘ e)) (X.1 ∘ e))=_ at hh
    rw [erasedList_reindex] at hh
    change b ∘ e=_ at hh
    simpa only [zn,Function.comp_apply,he0,hrow] using hh
  have hb:b=bn ∘ e.symm:=by
    funext k
    have hh:=congrFun hbn (e.symm k)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hh
  have hgen:∀P Q,T.Feasible P → T.Feasible Q →
      CompleteInformation.potential (1-ξ) b P.1 P.2=
        CompleteInformation.potential (1-ξ) b Q.1 Q.2 → focalCopy P i=focalCopy Q i:=by
    intro P Q _ _ he
    have hp:=potential_relabel (1-ξ) b e.symm P
    have hq:=potential_relabel (1-ξ) b e.symm Q
    change CompleteInformation.potential (1-ξ) (b ∘ e) _ _=_ at hp hq
    rw [hbn] at hp hq
    have hc:=hgeneric (relabelPair e.symm P) (relabelPair e.symm Q) (hp.trans (he.trans hq.symm))
    have h0:e.symm i=0:=by rw [←he0];exact e.symm_apply_apply 0
    have hpC:=focalCopy_relabel e.symm P i
    have hqC:=focalCopy_relabel e.symm Q i
    rw [h0] at hpC hqC
    exact hpC.symm.trans (hc.trans hqC)
  have hbid:=actualContext_entryBid U z hz i (hf.trans hdU)
  have hi:i∉A:=by
    intro hk
    have hh:=upperSet_entry_gt X.1 i hk
    rw [hbid] at hh
    linarith
  have hlow:∀k∉A,entryBid (X.1 k) ≤ d:=fun k hk=>nonupper_entry_le hd _ k hk
  have hout:=context_low_payoff ξ hξ hξ1 c X (actualContext_nonnegative U z hz)
    d hd A hactive hlow i hi (by rw [hbid];exact hpos) w hgen
  rw [hout]
  change T.userPayoff ξ w b i=_
  let S:=patternTemplate c (fun j=>(omega j).1)
  have ht:T=S.relabel e:=by
    change T=(patternTemplate c (fun j=>(omega j).1)).relabel e
    rw [←htn]
    exact (T.relabel_symm e.symm).symm
  rw [ht,hb,←he0]
  exact S.userPayoff_relabel e hξ hξ1 w bn 0 (fun P Q _ _ hh=>hgeneric P Q hh)

end FCAppendix.Affine.Hybrid.NativeContinuation
