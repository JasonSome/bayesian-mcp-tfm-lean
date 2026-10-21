import FCAppendix.Affine.LowBody.FirstCopyBoundary
import FCAppendix.Affine.LowBody.FirstCopyPair
import FCAppendix.Affine.LowBody.ResidualOutcomes

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
variable {N : ℕ}

def lowAboveSet (u : ℝ) : Set RowRival := {x|x.1=0 ∧ u<x.2}

def lowAboveCount (u : ℝ) (omega : Fin N→RowRival) : ℕ :=
  PiBinomial.count (lowAboveSet u) Finset.univ omega

def pairKinds (omega : Fin N→RowRival) : Fin (N+1)→Fin 4 :=
  Fin.cons 0 (fun i=>(omega i).1)

def pairRowBids (x y : ℝ) (omega : Fin N→RowRival) : Fin (N+2)→ℝ :=
  Fin.cons x (Fin.cons y (fun i=>if (omega i).1=0 then (omega i).2 else 0))

theorem measurableSet_lowAboveSet (u : ℝ) : MeasurableSet (lowAboveSet u) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_snd)

theorem measurable_pairKinds : Measurable (pairKinds (N:=N)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases measurable_const (fun j=>?_) i
  exact (measurable_pi_apply j).fst

theorem measurable_pairRowBids (x y : ℝ) : Measurable (pairRowBids (N:=N) x y) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases measurable_const (fun j=>?_) i
  refine Fin.cases measurable_const (fun k=>?_) j
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply k).fst measurable_const)
    (measurable_pi_apply k).snd measurable_const

lemma classCount_cons_row (k : Fin 4) (t : RowRival) (omega : Fin N→RowRival) :
    classCount k (Fin.cons t omega)=(if t.1=k then 1 else 0)+classCount k omega := by
  unfold classCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]

lemma classCount_pattern_tags (k : Fin 4) (omega : Fin N→RowRival) :
    classCount k (patternRow (fun i=>(omega i).1))=classCount k omega := rfl

lemma classCount_pairKinds (k : Fin 4) (omega : Fin N→RowRival) :
    classCount k (patternRow (pairKinds omega))=(if (0:Fin 4)=k then 1 else 0)+classCount k omega := by
  have he : patternRow (pairKinds omega)=Fin.cons ((0:Fin 4),(0:ℝ)) (patternRow (fun i=>(omega i).1)) := by
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  rw [he]
  rw [classCount_cons_row,classCount_pattern_tags]

theorem higherAtCount_eq (u : ℝ) (omega : Fin N→RowRival) :
    PiBinomial.count (higherAtSet u) Finset.univ omega=
      classCount 1 omega+classCount 2 omega+lowAboveCount u omega := by
  unfold lowAboveCount
  rw [PiBinomial.count_eq_sum,PiBinomial.count_eq_sum]
  unfold classCount
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize he : omega i=t
  rcases t with ⟨k,b⟩
  simp only [higherAtSet,lowAboveSet,mem_setOf_eq]
  fin_cases k <;> norm_num [Fin.ext_iff]

theorem lowAboveCount_le_low (u : ℝ) (omega : Fin N→RowRival) :
    lowAboveCount u omega≤classCount 0 omega := by
  unfold lowAboveCount classCount
  rw [PiBinomial.count_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hk:(omega i).1=0
  · simp only [lowAboveSet,mem_setOf_eq,hk,true_and,if_true]
    split_ifs <;> omega
  · simp [lowAboveSet,hk]

theorem firstCopy_other_higher_full (c : ℕ) (u : ℝ) (omega : Fin N→RowRival)
    (hc : 0<c) (hboundary : omega∈firstCopyBoundary c u) :
    c≤classCount 1 omega+classCount 3 omega := by
  have hcount:=hboundary.1
  change PiBinomial.count (higherAtSet u) Finset.univ omega=c-1 at hcount
  rw [higherAtCount_eq] at hcount
  have hnot:=hboundary.2
  change ¬BothUnderflow c (fun i=>(omega i).1) at hnot
  unfold BothUnderflow at hnot
  rw [sum_firstHigher,sum_secondHigher,classCount_pattern_tags,classCount_pattern_tags,
    classCount_pattern_tags] at hnot
  omega

theorem firstCopy_residuals (c : ℕ) (u : ℝ) (omega : Fin N→RowRival)
    (hc : 0<c) (hboundary : omega∈firstCopyBoundary c u) :
    (patternTemplate c (pairKinds omega)).residual₀=lowAboveCount u omega+1 ∧
      (patternTemplate c (pairKinds omega)).residual₁=0 := by
  have hcount:=hboundary.1
  change PiBinomial.count (higherAtSet u) Finset.univ omega=c-1 at hcount
  rw [higherAtCount_eq] at hcount
  have hother:=firstCopy_other_higher_full c u omega hc hboundary
  have hlow:=lowAboveCount_le_low u omega
  simp only [patternTemplate,rowResidual,classCount_pairKinds]
  norm_num [Fin.ext_iff]
  change min (1+(1+classCount 0 omega)) (c-classCount 1 omega-classCount 2 omega)=lowAboveCount u omega+1 ∧
    c-classCount 1 omega-classCount 3 omega=0
  omega

theorem pairRowBids_support (c : ℕ) (omega : Fin N→RowRival) :
    (0:Fin (N+2))∈(patternTemplate c (pairKinds omega)).support ∧
      (0:Fin (N+1)).succ∈(patternTemplate c (pairKinds omega)).support := by
  simp [patternTemplate,rowLowList,patternRow,pairKinds]

theorem pairRowBids_outside (c : ℕ) (omega : Fin N→RowRival) (x y : ℝ)
    (k : Fin (N+2)) (hk : k∉(patternTemplate c (pairKinds omega)).support) :
    pairRowBids x y omega k=0 := by
  revert hk
  refine Fin.cases ?_ (fun j=>?_) k
  · intro hk
    exact False.elim (hk (pairRowBids_support c omega).1)
  · refine Fin.cases ?_ (fun l=>?_) j
    · intro hk
      exact False.elim (hk (pairRowBids_support c omega).2)
    · intro hk
      by_cases ht:(omega l).1=0
      · exfalso
        apply hk
        simp [patternTemplate,rowLowList,patternRow,pairKinds,ht]
      · simp [pairRowBids,ht]

theorem pairRestAbove_pairRowBids_card (u : ℝ) (hu : 0≤u) (omega : Fin N→RowRival) (x y : ℝ) :
    (pairRestAbove u (0:Fin (N+2)) (0:Fin (N+1)).succ (pairRowBids x y omega)).card=
      lowAboveCount u omega := by
  unfold pairRestAbove lowAboveCount
  rw [Finset.card_filter,PiBinomial.count_eq_sum,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [ne_eq,not_true_eq_false,false_and,if_false,zero_add,
    Fin.succ_ne_zero,pairRowBids,Fin.cons_succ,Fin.cons_zero]
  simp only [not_false_eq_true,and_false,true_and,if_false,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  have h1:i.succ.succ≠(0:Fin (N+1)).succ:=fun he=>Fin.succ_ne_zero i (Fin.succ_inj.mp he)
  have h1lit:i.succ.succ≠(1:Fin (N+2)):=by simpa using h1
  by_cases ht:(omega i).1=0
  · simp [h1lit,ht,lowAboveSet]
  · simp [ht,lowAboveSet,not_lt_of_ge hu]

theorem pairOthersAbove_eq_pairRest (u : ℝ) (omega : Fin N→RowRival) (x y : ℝ) (hy : y≤u) :
    Finset.univ.filter (fun k : Fin (N+2)=>k≠0 ∧ u<pairRowBids x y omega k)=
      pairRestAbove u (0:Fin (N+2)) (0:Fin (N+1)).succ (pairRowBids x y omega) := by
  ext k
  simp only [pairRestAbove,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hk,hb⟩
    refine ⟨hk,?_,hb⟩
    intro he
    subst k
    simp only [pairRowBids,Fin.cons_succ,Fin.cons_zero] at hb
    linarith
  · exact fun h=>⟨h.1,h.2.2⟩

theorem firstCopy_template_counts (c : ℕ) (u : ℝ) (omega : Fin N→RowRival)
    (hc : 0<c) (hu : 0≤u) (hboundary : omega∈firstCopyBoundary c u)
    (x y : ℝ) (hy : y≤u) :
    let T:=patternTemplate c (pairKinds omega)
    T.residual₁=0 ∧
      (pairRestAbove u (0:Fin (N+2)) (0:Fin (N+1)).succ (pairRowBids x y omega)).card=T.residual₀-1 ∧
      (Finset.univ.filter (fun k : Fin (N+2)=>k≠0 ∧ u<pairRowBids x y omega k)).card<T.residual₀ := by
  obtain ⟨hleft,hright⟩:=firstCopy_residuals c u omega hc hboundary
  refine ⟨hright,?_,?_⟩
  · rw [pairRestAbove_pairRowBids_card u hu,hleft]
    omega
  · rw [pairOthersAbove_eq_pairRest u omega x y hy,pairRestAbove_pairRowBids_card u hu,hleft]
    omega

end FCAppendix.Affine.LowBody
