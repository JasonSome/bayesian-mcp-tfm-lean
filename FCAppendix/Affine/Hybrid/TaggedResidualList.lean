import FCAppendix.Affine.Hybrid.PureActiveResidual

noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes
variable {m : ℕ}

lemma erase_upperSet_eq_broadcastPart (d : ℝ) (L : LocalList m) :
    eraseActiveList (upperSet d L) L=broadcastPart d L:=by
  funext i
  cases hi:L i with
  | none=>simp [eraseActiveList,upperSet,broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi]
  | some b=>
    by_cases hb:b ≤ d
    · simp [eraseActiveList,upperSet,broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi,hb]
    · simp [eraseActiveList,upperSet,broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi,hb]

lemma lowList_eq_broadcastPart (d U : ℝ) (L : LocalList m) :
    TaggedLocal.lowList d U L=broadcastPart d L:=by
  funext i
  cases hi:L i with
  | none=>simp [broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi]
  | some b=>
    by_cases hb:b ≤ d
    · simp [broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi,hb]
    · by_cases hU:b ≤ U <;> simp [broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi,hb,hU]

lemma erase_active_broadcast_list {d U : ℝ} (hdU : d ≤ U) (L : LocalList m) :
    eraseActiveList (upperSet d (broadcastPart U L)) (broadcastPart U L)=TaggedLocal.lowList d U L:=by
  rw [erase_upperSet_eq_broadcastPart,lowList_eq_broadcastPart]
  funext i
  cases hi:L i with
  | none=>simp [broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi]
  | some b=>
    by_cases hb:b ≤ d
    · have hU:=hb.trans hdU
      simp [broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi,hb,hU]
    · by_cases hU:b ≤ U <;> simp [broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,hi,hb,hU]

theorem erased_list_observe (kind : Fin m→Fin 3) (x : Realization m 2) {d U : ℝ}
    (hdU : d ≤ U) (hb : TaggedLocal.BidBoxes kind x d U) (hr : TaggedLocal.ClassRoutes kind x)
    (j : Fin 2) :
    eraseActiveList (upperSet d (broadcastPart U (observe x j))) (broadcastPart U (observe x j))=
      fun i=>if kind i=0 then some (x.action i).bid else none:=by
  rw [erase_active_broadcast_list hdU]
  exact TaggedLocal.lowList_observe kind x hdU hb hr j

end FCAppendix.Affine.Hybrid.NativeContinuation
