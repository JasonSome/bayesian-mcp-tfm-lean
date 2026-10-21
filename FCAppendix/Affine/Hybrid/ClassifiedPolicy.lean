import FCAppendix.Affine.Hybrid.ClassifiedReceipts
import FCAppendix.Existence.HighestBidPolicy
import FCAppendix.Affine.Hybrid.FiniteSelector

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Bayes Game Set Filter
open scoped BigOperators

def contextUpper {m : ℕ} (j : Fin 2) (X : ClassifiedContext m) : ℕ :=
  if j=0 then X.2.1 else X.2.2

lemma measurable_contextUpper {m : ℕ} (j : Fin 2) :
    Measurable (contextUpper (m:=m) j) := by
  unfold contextUpper
  split_ifs <;> fun_prop

lemma contextUpper_observed {m : ℕ} (U : ℝ) (j : Fin 2) (L : LocalList m) :
    contextUpper j (observedContext U j L)=TaggedLocal.localCount U U L 2 := by
  fin_cases j <;> simp [contextUpper,observedContext]

def upperPart {m : ℕ} (U : ℝ) (L : LocalList m) : LocalList m :=
  fun i=>if TaggedLocal.tag U U (L i)=2 then L i else none

def upperSet {m : ℕ} (U : ℝ) (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i=>TaggedLocal.tag U U (L i)=2)

lemma measurable_upperPart {m : ℕ} (U : ℝ) : Measurable (upperPart (m:=m) U) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    (measurableSet_eq_fun ((TaggedLocal.measurable_tag U U).comp (measurable_pi_apply i))
      measurable_const) (measurable_pi_apply i) measurable_const

lemma measurable_upperSet {m : ℕ} (U : ℝ) : Measurable (upperSet (m:=m) U) := by
  classical
  apply measurable_to_countable'
  intro S
  have he : (upperSet U) ⁻¹' {S}=
      ⋂i : Fin m, {L : LocalList m | (i∈S ↔ TaggedLocal.tag U U (L i)=2)} := by
    ext L
    simp only [mem_preimage,mem_singleton_iff,mem_iInter,mem_setOf_eq,upperSet]
    exact ⟨fun h i=>by rw [←h]; simp,
      fun h=>Finset.ext (fun i=>by simpa only [Finset.mem_filter,Finset.mem_univ,true_and]
        using (h i).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i∈S
  · simp only [hi,true_iff]
    exact measurableSet_eq_fun ((TaggedLocal.measurable_tag U U).comp (measurable_pi_apply i))
      measurable_const
  · simp only [hi,false_iff]
    exact (measurableSet_eq_fun ((TaggedLocal.measurable_tag U U).comp (measurable_pi_apply i))
      measurable_const).compl

lemma upperSet_card {m : ℕ} (U : ℝ) (L : LocalList m) :
    (upperSet U L).card=TaggedLocal.localCount U U L 2 := by
  simp only [upperSet,TaggedLocal.localCount,Finset.card_eq_sum_ones,Finset.sum_filter]

lemma upperSet_present {m : ℕ} (U : ℝ) (L : LocalList m) (i : Fin m)
    (hi : i∈upperSet U L) : L i≠none := by
  have ht := (Finset.mem_filter.mp hi).2
  intro hn
  simp [hn,TaggedLocal.tag] at ht

lemma upperPart_present_iff {m : ℕ} (U : ℝ) (L : LocalList m) (i : Fin m) :
    upperPart U L i≠none ↔ i∈upperSet U L := by
  classical
  by_cases hi : i∈upperSet U L
  · have ht := (Finset.mem_filter.mp hi).2
    simp [upperPart,ht,hi,upperSet_present U L i hi]
  · have ht : TaggedLocal.tag U U (L i)≠2 := by simpa [upperSet] using hi
    simp [upperPart,ht,hi]

lemma broadcastPart_present {m : ℕ} (U : ℝ) (L : LocalList m) (i : Fin m)
    (hi : broadcastPart U L i≠none) : L i≠none ∧ i∉upperSet U L := by
  unfold broadcastPart TaggedLocal.lowList at hi
  by_cases ht : TaggedLocal.tag U U (L i)=0
  · simp only [if_pos ht] at hi
    refine ⟨hi,?_⟩
    simp [upperSet,ht]
  · simp only [if_neg ht] at hi
    exact False.elim (hi rfl)

structure ContextPolicy (m c : ℕ) (Seed : Type*) [MeasurableSpace Seed] where
  select : Fin 2 → ClassifiedContext m → Seed → Finset (Fin m)
  measurable : ∀j,Measurable (Function.uncurry (select j))
  feasible : ∀j X s,LocallyFeasible X.1 (c-contextUpper j X) (select j X s)

namespace ContextPolicy
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (C : ContextPolicy m c Seed)

def selection (U : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed) : Finset (Fin m) :=
  if TaggedLocal.localCount U U L 2≤c then
    upperSet U L ∪ C.select j (observedContext U j L) s
  else HighestBid.selection (upperPart U L) c

lemma lower_card (U : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed) :
    (C.select j (observedContext U j L) s).card≤c-TaggedLocal.localCount U U L 2 := by
  simpa only [contextUpper_observed] using (C.feasible j (observedContext U j L) s).1

lemma lower_present (U : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed)
    (i : Fin m) (hi : i∈C.select j (observedContext U j L) s) :
    L i≠none ∧ i∉upperSet U L :=
  broadcastPart_present U L i ((C.feasible j (observedContext U j L) s).2 i hi)

lemma selection_feasible (U : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed) :
    LocallyFeasible L c (C.selection U j L s) := by
  classical
  unfold selection
  split_ifs with hcap
  · constructor
    · apply (Finset.card_union_le _ _).trans
      rw [upperSet_card]
      have hlow := C.lower_card U j L s
      omega
    · intro i hi
      rcases Finset.mem_union.mp hi with hh | hl
      · exact upperSet_present U L i hh
      · exact (C.lower_present U j L s i hl).1
  · obtain ⟨hc,hs⟩ := (HighestBid.selection_best (upperPart U L) c).1
    exact ⟨hc,fun i hi=>upperSet_present U L i
      ((upperPart_present_iff U L i).mp (hs i hi))⟩

lemma measurable_selection (U : ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (C.selection U j)) := by
  have hc : Measurable (fun x : LocalList m × Seed=>
      C.select j (observedContext U j x.1) x.2) :=
    (C.measurable j).comp (((measurable_observedContext U j).comp measurable_fst).prodMk measurable_snd)
  have hu : Measurable (fun x : LocalList m × Seed=>
      upperSet U x.1 ∪ C.select j (observedContext U j x.1) x.2) :=
    (measurable_of_countable (fun ST : Finset (Fin m) × Finset (Fin m)=>ST.1∪ST.2)).comp
      (((measurable_upperSet U).comp measurable_fst).prodMk hc)
  exact Measurable.ite
    (measurableSet_le ((TaggedLocal.measurable_localCount U U 2).comp measurable_fst) measurable_const)
    hu ((HighestBid.measurable_selection m c).comp ((measurable_upperPart U).comp measurable_fst))

def localPolicy (U : ℝ) (j : Fin 2) : LocalPolicy m c Seed :=
  fun L s=>⟨C.selection U j L s,C.selection_feasible U j L s⟩

lemma factors (U : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed)
    (i : Fin m) (hi : broadcastPart U L i≠none) :
    i∈C.selection U j L s ↔ i∈C.select j (observedContext U j L) s := by
  classical
  have hn := (broadcastPart_present U L i hi).2
  unfold selection
  split_ifs with hcap
  · simp only [Finset.mem_union,hn,false_or]
  · have hz : C.select j (observedContext U j L) s=∅ := by
      apply Finset.card_eq_zero.mp
      have hc := C.lower_card U j L s
      omega
    rw [hz]
    simp only [Finset.notMem_empty,iff_false]
    intro hsel
    have hp := (HighestBid.selection_best (upperPart U L) c).1.2 i hsel
    exact hn ((upperPart_present_iff U L i).mp hp)

def nativeGame (Γ : FiniteGame m 2 c Seed) (U : ℝ) : FiniteGame m 2 c Seed :=
  { Γ with policy:=C.localPolicy U,policy_measurable:=C.measurable_selection U }

lemma nativeGame_factors (Γ : FiniteGame m 2 c Seed) (U : ℝ) :
    ContextFactors (C.nativeGame Γ U) U C.select := C.factors U

end ContextPolicy

lemma optimal_of_order_slack {ι : Type*} [DecidableEq ι] (c : ℕ) (r : ι→ℝ) (S : Finset ι)
    (hcap : S.card≤c) (hpos : ∀i∈S,0≤r i)
    (horder : ∀i∈S,∀j∉S,r j≤r i)
    (hslack : S.card<c → ∀j∉S,r j≤0) : Finite.Optimal c r S := by
  refine ⟨hcap,?_⟩
  intro T hT
  by_cases heq : S.card=c
  · by_cases hne : S.Nonempty
    · let a := S.inf' hne r
      have ha : 0≤a := Finset.le_inf' hne r (fun i hi=>hpos i hi)
      apply threshold_optimal r S T a ha (by omega)
      · intro i hi
        exact Finset.inf'_le r hi
      · intro j hj
        exact Finset.le_inf' hne r (fun i hi=>horder i hi j hj)
    · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have htz : T=∅ := Finset.card_eq_zero.mp (by simpa [hz] using hT.trans_eq heq.symm)
      simp [hz,htz]
  · have hlt : S.card<c := by omega
    have hdrop : (∑i∈T\S,r i)≤0 :=
      Finset.sum_nonpos (fun i hi=>hslack hlt i (Finset.mem_sdiff.mp hi).2)
    have hadd : 0≤∑i∈S\T,r i :=
      Finset.sum_nonneg (fun i hi=>hpos i (Finset.mem_sdiff.mp hi).1)
    have hs := Finset.sum_inter_add_sum_sdiff S T r
    have ht := Finset.sum_inter_add_sum_sdiff T S r
    rw [Finset.inter_comm T S] at ht
    linarith

lemma priority_union_optimal {ι : Type*} [DecidableEq ι] (c : ℕ) (r : ι→ℝ)
    (H S : Finset ι) (hH : H.card≤c) (hdisj : Disjoint H S)
    (hpos : ∀i,0≤r i) (hpriority : ∀i∈H,∀j∉H,r j≤r i)
    (hS : Finite.Optimal (c-H.card) (fun i=>if i∈H then 0 else r i) S) :
    Finite.Optimal c r (H∪S) := by
  classical
  have hcard : (H∪S).card=H.card+S.card := Finset.card_union_of_disjoint hdisj
  apply optimal_of_order_slack c r (H∪S) (by rw [hcard]; have := hS.1;omega)
    (fun i _=>hpos i)
  · intro i hi j hj
    have hjH : j∉H := fun h=>hj (Finset.mem_union_left S h)
    have hjS : j∉S := fun h=>hj (Finset.mem_union_right H h)
    rcases Finset.mem_union.mp hi with hiH | hiS
    · exact hpriority i hiH j hjH
    · have hiH : i∉H := fun h=>(Finset.disjoint_left.mp hdisj) h hiS
      simpa only [if_neg hiH,if_neg hjH] using
        Finite.optimal_swap (c-H.card) _ S hS i j hiS hjS
  · intro hslack j hj
    have hjH : j∉H := fun h=>hj (Finset.mem_union_left S h)
    have hjS : j∉S := fun h=>hj (Finset.mem_union_right H h)
    by_contra h
    have hp : 0<(if j∈H then 0 else r j) := by simpa [hjH] using lt_of_not_ge h
    have hc := Finite.optimal_fills (c-H.card) _ S hS j hjS hp
    rw [hcard,hc] at hslack
    omega

lemma priority_full_optimal {ι : Type*} [DecidableEq ι] (c : ℕ) (r : ι→ℝ)
    (H S : Finset ι) (hsub : S⊆H) (hcard : S.card=c) (hpos : ∀i,0≤r i)
    (hpriority : ∀i∈H,∀j∉H,r j≤r i)
    (hS : Finite.Optimal c (fun i=>if i∈H then r i else 0) S) :
    Finite.Optimal c r S := by
  classical
  apply optimal_of_order_slack c r S hcard.le (fun i _=>hpos i)
  · intro i hi j hj
    by_cases hjH : j∈H
    · simpa only [if_pos (hsub hi),if_pos hjH] using
        Finite.optimal_swap c _ S hS i j hi hj
    · exact hpriority i (hsub hi) j hjH
  · intro h
    omega

end FCAppendix.Affine.Hybrid
