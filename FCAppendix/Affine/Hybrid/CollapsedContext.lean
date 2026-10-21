import FCAppendix.Affine.Hybrid.CollapsedProfile

noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
open scoped BigOperators
variable {m N : ℕ}

lemma tag_upper_iff {d U : ℝ} (hdU:d ≤ U) (o : Option ℝ) :
    TaggedLocal.tag U U o=2↔TaggedLocal.tag d U o=2:=by
  cases o with
  | none=>simp [TaggedLocal.tag]
  | some b=>
    by_cases hd:b ≤ d
    · have hU:=hd.trans hdU
      simp [TaggedLocal.tag,hd,hU]
    · by_cases hU:b ≤ U <;> simp [TaggedLocal.tag,hd,hU]

lemma localCount_upper_eq {d U : ℝ} (hdU:d ≤ U) (L : LocalList m) :
    TaggedLocal.localCount U U L 2=TaggedLocal.localCount d U L 2:=by
  unfold TaggedLocal.localCount
  apply Finset.sum_congr rfl
  intro i _
  simp only [tag_upper_iff hdU]

lemma activeSet_broadcast {d U : ℝ} (hdU:d ≤ U) (L : LocalList m) :
    upperSet d (broadcastPart U L)=Finset.univ.filter (fun i=>TaggedLocal.tag d U (L i)=1):=by
  ext i
  cases hi:L i with
  | none=>simp [upperSet,broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi]
  | some b=>
    by_cases hd:b ≤ d
    · have hU:=hd.trans hdU
      simp [upperSet,broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi,hd,hU]
    · by_cases hU:b ≤ U <;> simp [upperSet,broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi,hd,hU]

lemma activeSet_broadcast_card {d U : ℝ} (hdU:d ≤ U) (L : LocalList m) :
    (upperSet d (broadcastPart U L)).card=TaggedLocal.localCount d U L 1:=by
  rw [activeSet_broadcast hdU,Finset.card_eq_sum_ones,Finset.sum_filter]
  rfl

theorem collapsed_context_data {c : ℕ} {d U : ℝ} (hdU:d ≤ U) (z : UserProfile (N+1) 2)
    (hz:z∈classifiedProfiles (N+1) U) (hf:(z 0).1.2.bid ≤ d) :
    let X:=actualContext U z
    let A:=upperSet d X.1
    let omega:=collapsedProfileRow d U z
    eraseActiveList A X.1=rowLowList (z 0).1.2.bid omega ∧
      A.card=classCount 1 omega ∧
      ∀j : Fin 2,residual (m:=N+1) c j X-A.card=c-classCount 1 omega-classCount (upperTag j) omega:=by
  let X:=actualContext U z
  let A:=upperSet d X.1
  let omega:=collapsedProfileRow d U z
  have hlist : eraseActiveList A X.1=rowLowList (z 0).1.2.bid omega:=by
    change eraseActiveList (upperSet d (broadcastPart U (observe (drawsRealization z) 0)))
      (broadcastPart U (observe (drawsRealization z) 0))=_
    rw [erase_active_broadcast_list hdU,collapsed_lowList hdU z hz hf 0]
  have hcard : A.card=classCount 1 omega:=by
    change (upperSet d (broadcastPart U (observe (drawsRealization z) 0))).card=_
    rw [activeSet_broadcast_card hdU]
    exact (collapsed_local_counts hdU z hz hf 0).2.1
  refine ⟨hlist,hcard,?_⟩
  intro j
  have hctx:=observedContext_eq_actual z hz j
  have hupper : contextUpper j X=classCount (upperTag j) omega:=by
    calc
      _=TaggedLocal.localCount U U (observe (drawsRealization z) j) 2:=by
        change contextUpper j (actualContext U z)=_
        rw [←hctx]
        exact contextUpper_observed U j _
      _=TaggedLocal.localCount d U (observe (drawsRealization z) j) 2:=localCount_upper_eq hdU _
      _=_:=(collapsed_local_counts hdU z hz hf j).2.2
  change c-contextUpper j X-A.card=_
  rw [hupper,hcard,Nat.sub_sub,Nat.sub_sub,Nat.add_comm]

theorem collapsed_rowResidual {c : ℕ} {d U : ℝ} (hdU:d ≤ U) (z : UserProfile (N+1) 2)
    (hz:z∈classifiedProfiles (N+1) U) (hf:(z 0).1.2.bid ≤ d) (j : Fin 2) :
    rowResidual c j (collapsedProfileRow d U z)=
      min (Finset.univ.filter (fun i=>eraseActiveList (upperSet d (actualContext U z).1)
        (actualContext U z).1 i≠none)).card
        (residual c j (actualContext U z)-(upperSet d (actualContext U z).1).card):=by
  obtain ⟨hlist,_,hr⟩:=collapsed_context_data (c:=c) hdU z hz hf
  rw [hlist,rowLowList_card,hr j]
  rfl

end FCAppendix.Affine.Hybrid.NativeContinuation
