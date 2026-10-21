import FCAppendix.Affine.Tail04.HighestBidShift
import FCAppendix.Affine.Tail04.ClosedUpperPriority
import FCAppendix.Affine.Hybrid.Native02.ClosedPosterior

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeClosedCarrier
open MeasureTheory Set Game Bayes Classical
open Hybrid
open ClosedUpperPriority

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma tag_encode (R : ℝ) (a : Option ℝ) :
    TaggedLocal.tag R R (a.map (encodeBid R))=Native02.closedTag R a := by
  cases a with
  | none=>rfl
  | some b=>
    by_cases hb : b<R
    · simp [TaggedLocal.tag,Native02.closedTag,encodeBid,not_le.mpr hb,hb,hb.le]
    · have hRb : R≤b:=le_of_not_gt hb
      have hupper : ¬b+1≤R:=by linarith
      simp [TaggedLocal.tag,Native02.closedTag,encodeBid,hb,hRb,hupper]

lemma lowerList_encode (R : ℝ) (L : LocalList m) :
    Hybrid.broadcastPart R (encodeList R L)=Native02.lowerPart R L := by
  funext i
  change (if TaggedLocal.tag R R ((L i).map (encodeBid R))=0 then
    (L i).map (encodeBid R) else none)=_
  rw [tag_encode]
  cases he : L i with
  | none=>simp [Native02.lowerPart,he,Native02.closedTag]
  | some b=>
    by_cases hb : b<R
    · simp [Native02.lowerPart,he,Native02.closedTag,hb,encodeBid,not_le.mpr hb]
    · simp [Native02.lowerPart,he,Native02.closedTag,hb]

lemma localCount_encode (R : ℝ) (L : LocalList m) (k : Fin 4) :
    TaggedLocal.localCount R R (encodeList R L) k=Native02.localCount R L k := by
  unfold TaggedLocal.localCount Native02.localCount
  simp only [encodeList,tag_encode]

lemma observedContext_encode (R : ℝ) (j : Fin 2) (L : LocalList m) :
    Hybrid.observedContext R j (encodeList R L)=Native02.observedClosedContext R j L := by
  unfold Hybrid.observedContext Native02.observedClosedContext
  rw [localCount_encode,localCount_encode,lowerList_encode]

private lemma highest_absent (L : LocalList m) (i : Fin m) (hi : L i=none) :
    i∉HighestBid.selection L c := by
  intro hmem
  exact (HighestBid.selection_best L c).1.2 i hmem hi

theorem lower_selection_eq (C : Hybrid.ContextPolicy m c Seed) (R : ℝ)
    (j : Fin 2) (L : LocalList m) (seed : Seed) (i : Fin m) (b : ℝ)
    (hi : L i=some b) (hb : b<R) :
    i∈ClosedUpperPriority.selection C R j L seed↔
      i∈Native02.ClosedPolicy.selection C R j L seed := by
  unfold ClosedUpperPriority.selection Hybrid.ContextPolicy.selection Native02.ClosedPolicy.selection
  rw [localCount_encode,observedContext_encode]
  have ht : Native02.closedTag R (L i)=0:=by simp [hi,Native02.closedTag,hb]
  by_cases hcount : Native02.localCount R L 2≤c
  · simp only [if_pos hcount,Finset.mem_union]
    have hnot : i∉Native02.upperSet R L:=by simp [Native02.upperSet,ht]
    have hnot' : i∉Hybrid.upperSet R (encodeList R L):=by
      simp [Hybrid.upperSet,encodeList,tag_encode,ht]
    simp only [hnot,hnot',false_or]
  · simp only [if_neg hcount]
    have hnone : Native02.upperPart R L i=none:=by simp [Native02.upperPart,ht]
    have hnone' : Hybrid.upperPart R (encodeList R L) i=none:=by
      simp [Hybrid.upperPart,encodeList,tag_encode,ht]
    simp only [highest_absent _ i hnone,highest_absent _ i hnone']

theorem lower_focalCount_eq (C : Hybrid.ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) (R : ℝ) (i : Fin m) (act : JointAction 2)
    (hb : act.bid<R) (ω : Sample m 2 Seed) :
    focalCount (ClosedUpperPriority.nativeGame C Γ R) i act ω=
      focalCount (Native02.ClosedPolicy.nativeGame C Γ R) i act ω := by
  apply Fin.ext
  change (accepted (deviated i act ω) (ClosedUpperPriority.nativeGame C Γ R).policy ω.1.2 i).card=
    (accepted (deviated i act ω) (Native02.ClosedPolicy.nativeGame C Γ R).policy ω.1.2 i).card
  congr 1
  ext j
  simp only [accepted,Finset.mem_filter,Finset.mem_univ,true_and]
  change i∈ClosedUpperPriority.selection C R j (observe (deviated i act ω) j) (ω.1.2 j)↔
    i∈Native02.ClosedPolicy.selection C R j (observe (deviated i act ω) j) (ω.1.2 j)
  by_cases hr : j∈(deviated i act ω).recipients i
  · exact lower_selection_eq C R j _ _ i act.bid (by simp [observe,hr,deviated_bid_self]) hb
  · have hn : observe (deviated i act ω) j i=none:=by simp [observe,hr]
    have h1 : i∉ClosedUpperPriority.selection C R j (observe (deviated i act ω) j) (ω.1.2 j):=by
      intro hi
      exact (ClosedUpperPriority.selection_feasible C R j _ _).2 i hi hn
    have h2 : i∉Native02.ClosedPolicy.selection C R j (observe (deviated i act ω) j) (ω.1.2 j):=by
      intro hi
      exact (Native02.ClosedPolicy.selection_feasible C R j _ _).2 i hi hn
    exact iff_of_false h1 h2

theorem lower_outcome_eq (C : Hybrid.ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) (R : ℝ) (i : Fin m) (act : JointAction 2) (hb : act.bid<R) :
    (problem (ClosedUpperPriority.nativeGame C Γ R) i).outcome act=
      (problem (Native02.ClosedPolicy.nativeGame C Γ R) i).outcome act := by
  rw [problem_outcome,problem_outcome]
  exact CountLaw.ofMeasure_congr_ae (sampleLaw Γ) _ _
    (measurable_focalCount (ClosedUpperPriority.nativeGame C Γ R) i act)
    (measurable_focalCount (Native02.ClosedPolicy.nativeGame C Γ R) i act)
    (ae_of_all _ (fun ω=>lower_focalCount_eq C Γ R i act hb ω))

theorem lower_payoff_eq (C : Hybrid.ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) (R : ℝ) (i : Fin m) (act : JointAction 2) (hb : act.bid<R) (v : ℝ) :
    (problem (ClosedUpperPriority.nativeGame C Γ R) i).payoff v act=
      (problem (Native02.ClosedPolicy.nativeGame C Γ R) i).payoff v act := by
  change ((problem (ClosedUpperPriority.nativeGame C Γ R) i).outcome act).utility v act.bid Γ.g Γ.A Γ.G=_
  rw [lower_outcome_eq C Γ R i act hb]
  rfl

lemma upperSet_encode (R : ℝ) (L : LocalList m) :
    Hybrid.upperSet R (encodeList R L) = Native02.upperSet R L := by
  ext i
  simp only [Hybrid.upperSet,Native02.upperSet,Finset.mem_filter,Finset.mem_univ,
    true_and,encodeList,tag_encode]

lemma upperPart_encode (R : ℝ) (L : LocalList m) :
    Hybrid.upperPart R (encodeList R L) = HighestBidShift.shift (Native02.upperPart R L) := by
  funext i
  unfold Hybrid.upperPart
  rw [show encodeList R L i = (L i).map (encodeBid R) from rfl,tag_encode]
  cases he : L i with
  | none => simp [HighestBidShift.shift,Native02.upperPart,he,Native02.closedTag]
  | some b =>
    by_cases hb : b < R
    · simp [HighestBidShift.shift,Native02.upperPart,he,Native02.closedTag,hb]
    · simp [HighestBidShift.shift,Native02.upperPart,he,Native02.closedTag,hb,encodeBid]

lemma upperPart_nonnegative (R : ℝ) (hR : 0 ≤ R) (L : LocalList m) :
    Bayes.NonnegativeList (Native02.upperPart R L) := by
  intro i
  cases he : L i with
  | none => simp [Native02.upperPart,he,Native02.closedTag,Bayes.entryBid]
  | some b =>
    by_cases hb : b < R
    · simp [Native02.upperPart,he,Native02.closedTag,hb,Bayes.entryBid]
    · simpa [Native02.upperPart,he,Native02.closedTag,hb,Bayes.entryBid] using
        hR.trans (le_of_not_gt hb)

theorem selection_eq (C : Hybrid.ContextPolicy m c Seed) (R : ℝ) (hR : 0 ≤ R)
    (j : Fin 2) (L : LocalList m) (seed : Seed) :
    ClosedUpperPriority.selection C R j L seed =
      Native02.ClosedPolicy.selection C R j L seed := by
  unfold ClosedUpperPriority.selection Hybrid.ContextPolicy.selection Native02.ClosedPolicy.selection
  rw [localCount_encode,observedContext_encode,upperSet_encode,upperPart_encode,
    HighestBidShift.selection_shift _ (upperPart_nonnegative R hR L)]

theorem game_eq (C : Hybrid.ContextPolicy m c Seed) (Γ : FiniteGame m 2 c Seed)
    (R : ℝ) (hR : 0 ≤ R) :
    ClosedUpperPriority.nativeGame C Γ R = Native02.ClosedPolicy.nativeGame C Γ R := by
  have hp : ClosedUpperPriority.localPolicy C R = Native02.ClosedPolicy.localPolicy C R := by
    funext j L seed
    apply Subtype.ext
    exact selection_eq C R hR j L seed
  unfold ClosedUpperPriority.nativeGame Native02.ClosedPolicy.nativeGame
  simp only [hp]

end FCAppendix.Affine.Tail04.NativeClosedCarrier
