import FCAppendix.Affine.UniformFinite.Late.NativeExceptionalProfile
import FCAppendix.Affine.UniformFinite.SourceRelabel

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.ExceptionalRelabel
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 SourceContinuity ClippedResidual WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem count_test (a : Fin M) (P : Allocation M) (f : Fin 3→ℝ) :
    f (pairCount a P)=f 0+(f 1-f 0)*Literal.firstCopy a P+
      (f 2-f 1)*Literal.duplicateCopy a P := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [pairCount,Literal.firstCopy,Literal.duplicateCopy,WeightedSampling.indicator,h0,h1]

omit [NeZero M] in
theorem count_expect (P : FiniteLaw (Allocation M)) (a : Fin M) (f : Fin 3→ℝ) :
    P.expect (fun S=> f (pairCount a S))=f 0+(f 1-f 0)*P.expect (Literal.firstCopy a)+
      (f 2-f 1)*P.expect (Literal.duplicateCopy a) := by
  simp_rw [count_test]
  rw [FiniteLaw.expect_add,FiniteLaw.expect_add,FiniteLaw.expect_const,
    FiniteLaw.expect_const_mul,FiniteLaw.expect_const_mul]

def countValue (f : Fin 3→ℝ) (p : ℝ) : ℝ :=
  f 0+(f 1-f 0)*(2*p-p^2)+(f 2-f 1)*p^2

omit [NeZero M] in
theorem equal_count (i : Row) (row : Source.CountRow M) (b : Fin M→ℝ)
    (a : Fin M) (f : Fin 3→ℝ) :
    (equalLaw i row b).expect (fun P=> f (pairCount a P))=
      countValue f (EqualCapacity.positiveMarginal (xi i) (Source.small row) (Source.lowerBids row b) a) := by
  let p := EqualCapacity.positiveMarginal (xi i) (Source.small row) (Source.lowerBids row b) a
  have hm := (EqualCapacity.canonicalLottery_implements (xi_range i).1 (xi_range i).2
    (Source.small row) (Source.lowerBids row b)).2 a
  have hi : (equalLottery i row b).expect (indicator a)=p :=
    (FiniteLaw.prob_eq_expect _ _).symm.trans hm
  have h0 : (equalLaw i row b).expect (fun P=> indicator a P.1)=p := by
    rw [equalLaw,FiniteLaw.expect_prod]
    simp only [FiniteLaw.expect_const,hi]
  have h1 : (equalLaw i row b).expect (fun P=> indicator a P.2)=p := by
    rw [equalLaw,FiniteLaw.expect_prod]
    simp only [hi,FiniteLaw.expect_const]
  have hd : (equalLaw i row b).expect (Literal.duplicateCopy a)=p^2 := by
    change (equalLaw i row b).expect (fun P=>
      WeightedSampling.indicator a P.1*WeightedSampling.indicator a P.2)=_
    rw [equalLaw,FiniteLaw.expect_prod_mul,hi]
    ring
  have hs : (equalLaw i row b).expect (Literal.firstCopy a)=2*p-p^2 := by
    change (equalLaw i row b).expect (fun P=>
      WeightedSampling.indicator a P.1+WeightedSampling.indicator a P.2-
        WeightedSampling.indicator a P.1*WeightedSampling.indicator a P.2)=_
    rw [FiniteLaw.expect_sub,FiniteLaw.expect_add,h0,h1]
    change p+p-(equalLaw i row b).expect (Literal.duplicateCopy a)=_
    rw [hd]
    ring
  rw [count_expect,hs,hd]
  rfl

omit [NeZero M] in
theorem count_orient (row : Source.CountRow M) (a : Fin M) (P : Allocation M) :
    pairCount a (orient row P)=pairCount a P := by
  by_cases h : Source.residual row 0< Source.residual row 1 <;>
    simp [orient,h,pairCount,Finset.inter_comm,Finset.union_comm]

omit [NeZero M] in
theorem ordinary (e : Equiv.Perm (Fin M)) (row : Source.CountRow M)
    (b : Fin M→ℝ) (a : Fin M) :
    Exceptional.ordinary (SourceRelabel.row e row) (b∘e.symm) (e a)=
      Exceptional.ordinary row b a∘e.symm := by
  rw [Exceptional.ordinary,SourceRelabel.lowerBids]
  funext j
  by_cases hj : e.symm j=a
  · have he : j=e a := by simpa using congrArg e hj
    simp [Exceptional.ordinary,he]
  · have he : j≠e a := fun h=> hj (by simp [h])
    simp [Exceptional.ordinary,Function.update_of_ne hj,Function.update_of_ne he]

omit [NeZero M] in
theorem weight (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (b : Fin M→ℝ) (a : Fin M) :
    Exceptional.weight i G (SourceRelabel.row e row) (b∘e.symm) (e a)=
      GuardedPathRelabel.relabelWeights e (Exceptional.weight i G row b a) := by
  rw [Exceptional.weight,ordinary,SourceRelabel.weights]
  rfl

omit [NeZero M] in
theorem alpha (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (b : Fin M→ℝ) (a : Fin M) :
    Exceptional.alpha i G (SourceRelabel.row e row) (b∘e.symm) (e a)=Exceptional.alpha i G row b a := by
  simp only [Exceptional.alpha,ordinary,SourceRelabel.seedCount,SourceRelabel.rawAlpha,
    Function.comp_apply,Equiv.symm_apply_apply]

omit [NeZero M] in
theorem good (e : Equiv.Perm (Fin M)) (i : Row) (row : Source.CountRow M)
    (b : Fin M→ℝ) (a : Fin M) (hb : NativeExceptionalRow.Good i row a b) :
    NativeExceptionalRow.Good i (SourceRelabel.row e row) (e a) (b∘e.symm) := by
  refine ⟨(SourceRelabel.lower_mem e row a).mpr hb.1,?_,?_⟩
  · intro j hj
    apply hb.2.1 (e.symm j)
    exact (SourceRelabel.lower_mem e row (e.symm j)).mp
      (by simpa only [Equiv.apply_symm_apply] using hj)
  · intro j hj hja
    apply hb.2.2 (e.symm j)
    · exact (SourceRelabel.lower_mem e row (e.symm j)).mp
        (by simpa only [Equiv.apply_symm_apply] using hj)
    · intro he
      apply hja
      simpa using congrArg e he

def pathCount (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (a : Fin M) (f : Fin 3→ℝ)
    (p : Path (Fin M) (Source.imbalance row)) : ℝ :=
  countValue f (exposure (xi i)
    (Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G) (Source.lowerBids row b)
      (finalSet (Source.imbalance row) ∅ p) (Source.small row)) (b a))

theorem canonical_count (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (a : Fin M) (hb : NativeExceptionalRow.Good i row a b)
    (hα : 0< Exceptional.alpha i G row b a) (f : Fin 3→ℝ) :
    (Exceptional.canonicalLaw i G row b a).expect (fun P=> f (pairCount a P))=
      (pathLaw (Exceptional.weight i G row b a) (Source.imbalance row) ∅).expect
        (pathCount i G row b a f) := by
  rw [Exceptional.canonicalLaw,FiniteLaw.expect_map,WeightedSampling.expect_pairLaw]
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (pathLaw (Exceptional.weight i G row b a) (Source.imbalance row) ∅).mass p=0
  · simp only [hp,zero_mul]
  · have hpos : 0<(pathLaw (Exceptional.weight i G row b a) (Source.imbalance row) ∅).mass p :=
      lt_of_le_of_ne (FiniteLaw.nonneg _ p) (Ne.symm hp)
    obtain ⟨hcard,haE,hz,hclear,hsel⟩ :=
      Exceptional.guarded_path i G row b a hb.1 hb.2.2 hα p hpos
    let E := finalSet (Source.imbalance row) ∅ p
    let z := Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G)
      (Source.lowerBids row b) E (Source.small row)
    have hz0 : 0< z := (Source.rootBounds i G).1.trans_le hz.1
    have hg := Exceptional.guarded_new_state i G row b a hb.1 hb.2.2 hα
    have hdata := Exceptional.alpha_pos_data i G row b a hα
    have he := Exceptional.conditionalCompletion_eq_literal (xi_range i).1 (xi_range i).2 hz0
      (t_pos i).le (hdata.2.1.trans hz.1) (Source.small row) (Source.lowerBids row b) E
      (Exceptional.lowerBids_nonnegative row b hb.2.1) hg.1.1 hclear
    congr 1
    change (Exceptional.conditionalCompletion (xi i) (Source.small row)
      (Source.lowerBids row b) E).expect (fun P=>f (pairCount a (orient row P)))=
        pathCount i G row b a f p
    simp only [count_orient]
    rw [he,count_expect,
      Literal.conditional_first_copy (xi_range i).1 hz0 _ E (Source.small row) hclear a,
      Literal.conditional_duplicate_copy (xi_range i).1 hz0 _ E (Source.small row) hclear a,
      if_neg haE,if_neg haE,Source.lowerBids_of_mem row b hb.1]
    rfl

theorem canonical_count_relabel (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (hb : NativeExceptionalRow.Good i row a b) (hα : 0< Exceptional.alpha i G row b a)
    (f : Fin 3→ℝ) :
    (Exceptional.canonicalLaw i G (SourceRelabel.row e row) (b∘e.symm) (e a)).expect
      (fun P=> f (pairCount (e a) P))=
      (Exceptional.canonicalLaw i G row b a).expect (fun P=> f (pairCount a P)) := by
  have hα' : 0< Exceptional.alpha i G (SourceRelabel.row e row) (b∘e.symm) (e a) := by
    rwa [alpha]
  have hW : (Source.imbalance row:ℝ)< totalWeight (Exceptional.weight i G row b a) := by
    have hg := Exceptional.guarded_new_state i G row b a hb.1 hb.2.2 hα
    have hd := Exceptional.alpha_pos_data i G row b a hα
    linarith [hg.1.2.2.2.1,hd.2.2.1]
  rw [canonical_count i G _ _ _ (good e i row b a hb) hα' f,
    canonical_count i G row b a hb hα f]
  unfold pathCount
  rw [weight]
  let F : ℕ→ℝ:=fun n=>
    (pathLaw (GuardedPathRelabel.relabelWeights e (Exceptional.weight i G row b a)) n ∅).expect
      (fun p=>countValue f (exposure (xi i)
        (Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G)
          (Source.lowerBids (SourceRelabel.row e row) (b∘e.symm))
          (finalSet n ∅ p) (Source.small (SourceRelabel.row e row))) ((b∘e.symm) (e a))))
  change F (Source.imbalance (SourceRelabel.row e row))=_
  rw [congrArg F (SourceRelabel.imbalance e row)]
  dsimp only [F]
  simp only [SourceRelabel.small,SourceRelabel.lowerBids,
    Function.comp_apply,Equiv.symm_apply_apply]
  rw [GuardedPathRelabel.guarded_empty_path_expect e _ _ hW]
  apply FiniteLaw.expect_congr
  intro p
  have hE : finalSet (Source.imbalance row) ∅ (GuardedPathRelabel.relabelPath e (Source.imbalance row) p)=
      (finalSet (Source.imbalance row) ∅ p).map e.toEmbedding := by
    simpa using GuardedPathRelabel.finalSet_relabel e (Source.imbalance row) ∅ p
  simp only [hE,Literal.root_relabel]

omit [NeZero M] in
theorem pure_count_relabel (e : Equiv.Perm (Fin M)) (i : Row)
    (row : Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (hgeneric : ∀P Q : Allocation M,
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row b) P.1 P.2=
        LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row b) Q.1 Q.2→
      LowBody.focalCopy P a=LowBody.focalCopy Q a) (f : Fin 3→ℝ) :
    (pureLaw i (SourceRelabel.row e row) (b∘e.symm)).expect (fun P=> f (pairCount (e a) P))=
      (pureLaw i row b).expect (fun P=> f (pairCount a P)) := by
  have he := (Source.lowerTemplate row).selection_focalCopy_relabel e (kappa i)
    (Source.lowerBids row b) a (fun P Q _ _ h=> hgeneric P Q h)
  simp only [pureLaw,FiniteLaw.expect_dirac,SourceRelabel.template,SourceRelabel.lowerBids,
    NativeProfile.pairCount_focalCopy,he]

theorem continuation_count_relabel (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (hb : NativeExceptionalRow.Good i row a b)
    (hgeneric : ∀P Q : Allocation M,
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row b) P.1 P.2=
        LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row b) Q.1 Q.2→
      LowBody.focalCopy P a=LowBody.focalCopy Q a) (f : Fin 3→ℝ) :
    (Exceptional.continuationLaw i G (SourceRelabel.row e row) (b∘e.symm) (e a)).expect
      (fun P=> f (pairCount (e a) P))=
      (Exceptional.continuationLaw i G row b a).expect (fun P=> f (pairCount a P)) := by
  by_cases he : Source.residual row 0=Source.residual row 1
  · simp only [Exceptional.continuationLaw,SourceRelabel.residual,if_pos he,equal_count,
      SourceRelabel.small,SourceRelabel.lowerBids,
      EqualCapacity.positiveMarginal_equiv e.symm (xi_range i).1 (xi_range i).2,
      Equiv.symm_apply_apply]
  · simp only [Exceptional.continuationLaw,SourceRelabel.residual,if_neg he,FiniteLaw.expect_mixture,alpha]
    rw [pure_count_relabel e i row b a hgeneric f]
    by_cases hα : Exceptional.alpha i G row b a=0
    · simp only [hα,zero_mul]
    · have hp : 0< Exceptional.alpha i G row b a :=
        lt_of_le_of_ne (Exceptional.alpha_bounds i G row b a).1 (Ne.symm hα)
      rw [canonical_count_relabel e i G row b a hb hp f]

end FCAppendix.Affine.UniformFinite.Late.ExceptionalRelabel
