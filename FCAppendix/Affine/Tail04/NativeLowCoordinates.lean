import FCAppendix.Affine.Tail04.PartialNativeCoordinates
import FCAppendix.Affine.Hybrid.NativeFocalReindex
import FCAppendix.Affine.Hybrid.NativeZeroEnvelope

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLowCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid LowBody NativeContinuation NativeMenuReports PartialNativeCoordinates
open LowResidualCompletion NativeLocalPolicy Observable.Regions
open scoped BigOperators

variable (E : Observable.Regions)

lemma local_counts_total {m : ℕ} (L : LocalList m) :
    E.localCount L 0+E.localCount L 1+E.localCount L 2+E.localCount L 3=m := by
  simp only [Observable.Regions.localCount,←Finset.sum_add_distrib]
  have hterm (i : Fin m) :
      (if E.localTag (L i)=0 then 1 else 0)+
      (if E.localTag (L i)=1 then 1 else 0)+
      (if E.localTag (L i)=2 then 1 else 0)+
      (if E.localTag (L i)=3 then 1 else 0)=(1:ℕ) := by
    generalize E.localTag (L i)=k
    fin_cases k <;> decide
  simp_rw [hterm]
  simp

lemma otherPrivateCount_eq_absent {m : ℕ} (L : LocalList m) :
    E.otherPrivateCount L=E.localCount L 3 := by
  have h := local_counts_total E L
  unfold Observable.Regions.otherPrivateCount
  omega

section Focal
variable {N c : ℕ} {Seed : Type*}

def rivalRow (i : Fin (N+1)) (ω : Background (N+1) 2 Seed) : Fin N→ RowRival :=
  fun r=> E.collapse ((ω.1 (i.succAbove r)).1.2,(ω.1 (i.succAbove r)).2)

lemma measurable_rivalRow [MeasurableSpace Seed] (i : Fin (N+1)) :
    Measurable (rivalRow E (Seed:=Seed) i) := by
  apply measurable_pi_lambda
  intro r
  exact E.measurable_collapse.comp
    ((((measurable_pi_apply (i.succAbove r)).comp measurable_fst).fst.snd).prodMk
      (((measurable_pi_apply (i.succAbove r)).comp measurable_fst).snd))

@[simp] lemma rivalRow_tag (i : Fin (N+1)) (ω : Background (N+1) 2 Seed) (r : Fin N) :
    (rivalRow E i ω r).1=E.coarseTag (ω.1 (i.succAbove r)) := rfl

lemma collapse_low_bid (x : UserDraw 2) (hx : E.coarseTag x=0) :
    (E.collapse (x.1.2,x.2)).2=x.1.2.bid := by
  have hl := (ObservedScenario.coarseTag_low_iff E x).mp hx
  simp [Observable.Regions.collapse,hl]

lemma low_present_counts (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
    (hr : ∀ r : Fin N,MenuAction E (ω.1 (i.succAbove r)).1.2)
    (b : ℝ) (hb : b≤ E.d) (j : Fin 2) :
    E.localCount (presentList ω i b j) 0=1+classCount 0 (rivalRow E i ω) ∧
    E.localCount (presentList ω i b j) 1=classCount 1 (rivalRow E i ω) ∧
    E.localCount (presentList ω i b j) 2=classCount (upperTag j) (rivalRow E i ω) ∧
    E.localCount (presentList ω i b j) 3=classCount (upperTag (otherProposer j)) (rivalRow E i ω) := by
  have htag : E.localTag (some b)=0 := by simp [Observable.Regions.localTag,hb]
  have h0 := present_count E i ω b j 0
  have h1 := present_count E i ω b j 1
  have h2 := present_count E i ω b j 2
  have h3 := present_count E i ω b j 3
  simp only [htag,ite_true,ite_false,Fin.reduceEq,zero_add] at h0 h1 h2 h3
  refine ⟨h0.trans ?_,h1.trans ?_,h2.trans ?_,h3.trans ?_⟩
  · congr 1
    apply Finset.sum_congr rfl
    intro r _
    simp only [observed_low_tag E _ (hr r) j,rivalRow_tag]
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro r _
    simp only [observed_active_tag E _ (hr r) j,rivalRow_tag]
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro r _
    simp only [observed_private_tag E _ (hr r) j,rivalRow_tag]
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro r _
    simp only [observed_absent_tag E _ (hr r) j,rivalRow_tag]
    split_ifs <;> rfl

def rowContext (b : ℝ) (ω : Fin N→ RowRival) : ClassifiedContext (N+1) :=
  (rowLowList b ω,(classCount 1 ω+classCount 2 ω,classCount 1 ω+classCount 3 ω))

def rowContextAt (i : Fin (N+1)) (b : ℝ) (ω : Fin N→ RowRival) : ClassifiedContext (N+1) :=
  reindexContext (focalIndex i).symm (rowContext b ω)

lemma rowContextAt_focal (i : Fin (N+1)) (b : ℝ) (ω : Fin N→ RowRival) :
    (rowContextAt i b ω).1 i=some b := by
  have he : (focalIndex i).symm i=0 := by
    rw [←focalIndex_zero i]
    exact Equiv.symm_apply_apply _ _
  simp [rowContextAt,reindexContext,rowContext,he,rowLowList]

lemma rowContextAt_rival (i : Fin (N+1)) (b : ℝ) (ω : Fin N→ RowRival) (r : Fin N) :
    (rowContextAt i b ω).1 (i.succAbove r)=
      if (ω r).1=0 then some (ω r).2 else none := by
  have he : (focalIndex i).symm (i.succAbove r)=r.succ := by
    rw [←focalIndex_succ i r]
    exact Equiv.symm_apply_apply _ _
  simp [rowContextAt,reindexContext,rowContext,he,rowLowList]

lemma low_present_list (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
    (hr : ∀ r : Fin N,MenuAction E (ω.1 (i.succAbove r)).1.2)
    (b : ℝ) (hb : b≤ E.d) (j : Fin 2) :
    E.roleList 0 (presentList ω i b j)=(rowContextAt i b (rivalRow E i ω)).1 := by
  funext l
  by_cases hl : l=i
  · subst l
    rw [rowContextAt_focal]
    simp [Observable.Regions.roleList,presentList_self,Observable.Regions.localTag,hb]
  · obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
    rw [rowContextAt_rival]
    unfold Observable.Regions.roleList
    rw [present_other_observed]
    simp only [observed_low_tag E _ (hr r) j]
    by_cases htag : E.coarseTag (ω.1 (i.succAbove r))=0
    · have hl := (ObservedScenario.coarseTag_low_iff E _).mp htag
      have hprivate : (ω.1 (i.succAbove r)).1.2.bid∉E.privateBids :=
        fun hp=>(not_lt.mpr hl) (E.private_above_low hp)
      have hk := menu_common_route E _ (hr r) hprivate
      rw [if_pos htag]
      simp only [rivalRow_tag,htag,ite_true]
      rw [show (rivalRow E i ω r).2=(ω.1 (i.succAbove r)).1.2.bid from collapse_low_bid E _ htag]
      simp [NativePrivatePosterior.observedEntry,hk,firstK_full_two]
    · simp only [rivalRow_tag,htag,ite_false]

theorem low_context_exact (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
    (hr : ∀ r : Fin N,MenuAction E (ω.1 (i.succAbove r)).1.2)
    (b : ℝ) (hb : b≤ E.d) (j : Fin 2) :
    lowContext E j (presentList ω i b j)=rowContextAt i b (rivalRow E i ω) := by
  obtain ⟨h0,h1,h2,h3⟩ := low_present_counts E i ω hr b hb j
  have hother := otherPrivateCount_eq_absent E (presentList ω i b j)
  apply Prod.ext
  · exact low_present_list E i ω hr b hb j
  · fin_cases j <;>
      simp only [lowContext,Observable.Regions.context,
        h1,h2,hother,h3,rowContextAt,reindexContext,rowContext,upperTag,otherProposer] <;> rfl

theorem rowContextAt_change_bid (i : Fin (N+1)) (b y : ℝ) (r : Fin N→ RowRival) :
    rowContextAt i y r=contextAtBid (rowContextAt i b r) i y := by
  apply Prod.ext
  · funext l
    by_cases hl:l=i
    · subst l
      simp [contextAtBid,rowContextAt_focal]
    · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hl
      rw [rowContextAt_rival]
      simp only [contextAtBid,Function.update_of_ne (Fin.succAbove_ne i j),rowContextAt_rival]
  · rfl

theorem low_context_change_bid (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
    (hr : ∀ r : Fin N,MenuAction E (ω.1 (i.succAbove r)).1.2)
    (b y : ℝ) (hb : b≤ E.d) (hy : y≤ E.d) (j : Fin 2) :
    lowContext E j (presentList ω i y j)=
      contextAtBid (lowContext E j (presentList ω i b j)) i y := by
  rw [low_context_exact E i ω hr y hy j,low_context_exact E i ω hr b hb j]
  exact rowContextAt_change_bid i b y _

end Focal
end FCAppendix.Affine.Tail04.NativeLowCoordinates
