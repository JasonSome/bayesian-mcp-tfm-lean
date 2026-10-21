import FCAppendix.Affine.Hybrid.NativeAllocationCounts
import FCAppendix.Affine.Hybrid.NativeRows
import FCAppendix.Affine.Hybrid.PopulationGame

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
open scoped BigOperators

lemma singleton_two_complement (S : Finset (Fin 2)) (hS:S.card=1) :
    (1:Fin 2)∈S↔(0:Fin 2)∉S:=by
  obtain ⟨j,rfl⟩:=Finset.card_eq_one.mp hS
  fin_cases j <;> simp

def upperTag (j : Fin 2) : Fin 4:=⟨2+j.val,by omega⟩

lemma upperTag_ne_zero (j : Fin 2) : upperTag j≠0:=by
  intro h
  have hh:=congrArg Fin.val h
  dsimp only [upperTag] at hh
  omega

lemma upperTag_ne_one (j : Fin 2) : upperTag j≠1:=by
  intro h
  have hh:=congrArg Fin.val h
  dsimp only [upperTag] at hh
  omega

lemma upperRow_tag (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    (upperRow τ).1=upperTag j↔j∈firstK τ 1:=by
  have hc:(firstK τ 1).card=1:=card_firstK τ 1 (by omega)
  have hh:=singleton_two_complement (firstK τ 1) hc
  fin_cases j
  · by_cases h0:(0:Fin 2)∈firstK τ 1 <;> simp [upperTag,upperRow,h0,Fin.ext_iff]
  · by_cases h0:(0:Fin 2)∈firstK τ 1
    · have h1:(1:Fin 2)∉firstK τ 1:=by simpa only [hh,not_not] using h0
      simp [upperTag,upperRow,h0,h1]
    · have h1:(1:Fin 2)∈firstK τ 1:=hh.mpr h0
      simp [upperTag,upperRow,h0,h1]

theorem collapsed_local_entry {d U : ℝ} (hdU:d ≤ U) (u : UserDraw 2)
    (hu:PopulationGame.actionShape U u.1.2) (j : Fin 2) :
    let L:Option ℝ:=if j∈firstK u.2 u.1.2.routeCount then some u.1.2.bid else none
    let row:=collapseAction d U (u.1.2,u.2)
    (TaggedLocal.tag d U L=0↔row.1=0) ∧
    (TaggedLocal.tag d U L=1↔row.1=1) ∧
    (TaggedLocal.tag d U L=2↔row.1=upperTag j) ∧
    (if TaggedLocal.tag d U L=0 then L else none)=if row.1=0 then some row.2 else none:=by
  dsimp only
  by_cases hlo:u.1.2.bid ≤ d
  · have hr:u.1.2.routeCount=2:=by
      rcases hu with ⟨_,hr⟩|⟨hb,_⟩
      · exact hr
      · exact False.elim (not_lt_of_ge (hlo.trans hdU) hb)
    simp [hr,firstK_full_two,collapseAction,hlo,TaggedLocal.tag,Ne.symm (upperTag_ne_zero j)]
  · by_cases hhi:u.1.2.bid ≤ U
    · have hr:u.1.2.routeCount=2:=by
        rcases hu with ⟨_,hr⟩|⟨hb,_⟩
        · exact hr
        · exact False.elim (not_lt_of_ge hhi hb)
      simp [hr,firstK_full_two,collapseAction,hlo,hhi,TaggedLocal.tag,Ne.symm (upperTag_ne_one j)]
    · have hr:u.1.2.routeCount=1:=by
        rcases hu with ⟨hb,_⟩|⟨_,hr⟩
        · exact False.elim (hhi hb)
        · exact hr
      have ht:=upperRow_tag u.2 j
      have h20:(upperRow u.2).1≠(0:Fin 4):=by unfold upperRow;split <;> norm_num [Fin.ext_iff]
      have h21:(upperRow u.2).1≠(1:Fin 4):=by unfold upperRow;split <;> norm_num [Fin.ext_iff]
      by_cases hj:j∈firstK u.2 1
      · have hrow:(upperRow u.2).1=upperTag j:=ht.mpr hj
        simp [hr,hj,collapseAction,hlo,hhi,TaggedLocal.tag,hrow,upperTag_ne_zero,upperTag_ne_one]
      · have hrow:(upperRow u.2).1≠upperTag j:=fun h=>hj (ht.mp h)
        simp [hr,hj,collapseAction,hlo,hhi,TaggedLocal.tag,h20,h21,hrow,Fin.ext_iff]

variable {N : ℕ}

def collapsedProfileRow (d U : ℝ) (z : UserProfile (N+1) 2) : Fin N → RowRival:=
  fun k=>collapseAction d U ((z k.succ).1.2,(z k.succ).2)

theorem collapsed_lowList {d U : ℝ} (hdU:d ≤ U) (z : UserProfile (N+1) 2)
    (hz:z∈classifiedProfiles (N+1) U) (hf:(z 0).1.2.bid ≤ d) (j : Fin 2) :
    TaggedLocal.lowList d U (observe (drawsRealization z) j)=
      rowLowList (z 0).1.2.bid (collapsedProfileRow d U z):=by
  funext k
  refine Fin.cases ?_ (fun k=>?_) k
  · have hh:=collapsed_local_entry hdU (z 0) (hz 0) j
    simpa only [TaggedLocal.lowList,observe,drawsRealization,rowLowList,Fin.cons_zero,
      collapseAction,if_pos hf,ite_true] using hh.2.2.2
  · have hh:=collapsed_local_entry hdU (z k.succ) (hz k.succ) j
    simpa only [TaggedLocal.lowList,observe,drawsRealization,rowLowList,Fin.cons_succ,
      collapsedProfileRow] using hh.2.2.2

theorem collapsed_local_counts {d U : ℝ} (hdU:d ≤ U) (z : UserProfile (N+1) 2)
    (hz:z∈classifiedProfiles (N+1) U) (hf:(z 0).1.2.bid ≤ d) (j : Fin 2) :
    TaggedLocal.localCount d U (observe (drawsRealization z) j) 0=1+classCount 0 (collapsedProfileRow d U z) ∧
    TaggedLocal.localCount d U (observe (drawsRealization z) j) 1=classCount 1 (collapsedProfileRow d U z) ∧
    TaggedLocal.localCount d U (observe (drawsRealization z) j) 2=classCount (upperTag j) (collapsedProfileRow d U z):=by
  have hterm (k : Fin (N+1)):=collapsed_local_entry hdU (z k) (hz k) j
  have hfrow:collapseAction d U ((z 0).1.2,(z 0).2)=((0:Fin 4),(z 0).1.2.bid):=if_pos hf
  have h0 : TaggedLocal.tag d U (observe (drawsRealization z) j 0)=0:=by
    exact (hterm 0).1.mpr (by rw [hfrow])
  have h1 : TaggedLocal.tag d U (observe (drawsRealization z) j 0)≠1:=by rw [h0];decide
  have h2 : TaggedLocal.tag d U (observe (drawsRealization z) j 0)≠2:=by rw [h0];decide
  have heq (k : Fin N) (t : Fin 4) (ht:t=0∨t=1∨t=2) :
      (TaggedLocal.tag d U (observe (drawsRealization z) j k.succ)=t)↔
        ((collapsedProfileRow d U z k).1=if t=2 then upperTag j else t):=by
    rcases ht with rfl|rfl|rfl
    · simpa only [collapsedProfileRow,observe,drawsRealization,Fin.reduceEq,if_false] using (hterm k.succ).1
    · simpa only [collapsedProfileRow,observe,drawsRealization,Fin.reduceEq,if_false] using (hterm k.succ).2.1
    · simpa only [collapsedProfileRow,observe,drawsRealization,ite_true] using (hterm k.succ).2.2.1
  constructor
  · unfold TaggedLocal.localCount classCount
    rw [Fin.sum_univ_succ]
    simp only [h0,ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [heq k 0 (Or.inl rfl),Fin.reduceEq,if_false]
  · constructor
    · unfold TaggedLocal.localCount classCount
      rw [Fin.sum_univ_succ]
      simp only [if_neg h1,zero_add]
      apply Finset.sum_congr rfl
      intro k _
      simp only [heq k 1 (Or.inr (Or.inl rfl)),Fin.reduceEq,if_false]
    · unfold TaggedLocal.localCount classCount
      rw [Fin.sum_univ_succ]
      simp only [if_neg h2,zero_add]
      apply Finset.sum_congr rfl
      intro k _
      simp only [heq k 2 (Or.inr (Or.inr rfl)),ite_true]

end FCAppendix.Affine.Hybrid.NativeContinuation
