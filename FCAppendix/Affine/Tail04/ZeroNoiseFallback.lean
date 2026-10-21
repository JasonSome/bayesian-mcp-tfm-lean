import FCAppendix.Affine.Tail04.ZeroNoiseAffine
import FCAppendix.Affine.Tail04.SortedAllNoise

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNoiseFallback
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open AllNoiseFiniteSelector AtypicalUnequal AllCountAtypical AtypicalActiveRanks
open AtypicalActiveNoisy PrivateRowSorting SortedAllNoise
open scoped BigOperators

abbrev Pair (N : ℕ) := Finset (Fin N)×Finset (Fin N)

def coefficient {N : ℕ} (ξ : ℝ) (P : Pair N) : Fin N→ℝ := LowBody.copyCoefficient (1-ξ) P

def rankBad (N : ℕ) : Set (Fin N→ℝ) :=
  (⋃ i : Fin N,{b | b i≤0}) ∪
    ⋃ i : Fin N,⋃ j : Fin N,if i=j then ∅ else {b | b i=b j}

def potentialBad (N : ℕ) (ξ : ℝ) : Set (Fin N→ℝ) :=
  ⋃ σ : Equiv.Perm (Fin N),⋃ P : Pair N,⋃ Q : Pair N,
    if coefficient ξ P=coefficient ξ Q then ∅ else
      {b | score (fun _=>0) (coefficient ξ) (b ∘ σ) P=
        score (fun _=>0) (coefficient ξ) (b ∘ σ) Q}

def bad (N : ℕ) (ξ : ℝ) : Set (Fin N→ℝ) := rankBad N∪potentialBad N ξ

lemma isClosed_rankBad (N : ℕ) : IsClosed (rankBad N) := by
  apply IsClosed.union
  · exact isClosed_iUnion_of_finite (fun i=> isClosed_le (continuous_apply i) continuous_const)
  · apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    split_ifs
    · exact isClosed_empty
    · exact isClosed_eq (continuous_apply i) (continuous_apply j)

lemma isClosed_potentialBad (N : ℕ) (ξ : ℝ) : IsClosed (potentialBad N ξ) := by
  apply isClosed_iUnion_of_finite
  intro σ
  apply isClosed_iUnion_of_finite
  intro P
  apply isClosed_iUnion_of_finite
  intro Q
  split_ifs
  · exact isClosed_empty
  · exact isClosed_eq
      ((continuous_score (fun _=>0) (coefficient ξ) P).comp (continuous_reindex_fixed σ))
      ((continuous_score (fun _=>0) (coefficient ξ) Q).comp (continuous_reindex_fixed σ))

lemma isClosed_bad (N : ℕ) (ξ : ℝ) : IsClosed (bad N ξ) :=
  (isClosed_rankBad N).union (isClosed_potentialBad N ξ)

lemma regular_of_not_bad {N : ℕ} (ξ : ℝ) (b : Fin N→ℝ) (hb : b∉bad N ξ) :
    (∀ i,0< b i) ∧ (∀ i j,i≠j→ b i≠b j) ∧
      ∀ σ : Equiv.Perm (Fin N),∀ P Q : Pair N,
        score (fun _=>0) (coefficient ξ) (b ∘ σ) P=
          score (fun _=>0) (coefficient ξ) (b ∘ σ) Q→
            coefficient ξ P=coefficient ξ Q := by
  have hr : b∉rankBad N:=fun h=> hb (Or.inl h)
  have hp : b∉potentialBad N ξ:=fun h=> hb (Or.inr h)
  refine ⟨?_,?_,?_⟩
  · intro i
    apply lt_of_not_ge
    intro hi
    exact hr (Or.inl (Set.mem_iUnion.mpr ⟨i,hi⟩))
  · intro i j hij he
    apply hr
    right
    apply Set.mem_iUnion.mpr ⟨i,?_⟩
    apply Set.mem_iUnion.mpr ⟨j,?_⟩
    simpa only [if_neg hij,Set.mem_setOf_eq] using he
  · intro σ P Q he
    by_contra hne
    apply hp
    apply Set.mem_iUnion.mpr ⟨σ,?_⟩
    apply Set.mem_iUnion.mpr ⟨P,?_⟩
    apply Set.mem_iUnion.mpr ⟨Q,?_⟩
    simpa only [if_neg hne,Set.mem_setOf_eq] using he

lemma score_reindex {N : ℕ} (ξ : ℝ) (σ : Equiv.Perm (Fin N))
    (b : Fin N→ℝ) (P : Pair N) :
    score (fun _=>0) (coefficient ξ) (b ∘ σ) P=
      score (fun _=>0) (fun P i=> coefficient ξ P (σ.symm i)) b P := by
  simp only [score,zero_add,Function.comp_apply]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp σ (fun i=> coefficient ξ P (σ.symm i)*b i))

theorem ae_cons_not_bad {N : ℕ} {L U : ℝ} (ξ : ℝ) (hL : 0< L)
    (μ : Measure (Icc L U)) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (b : ℝ) (hb : 0< b) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N=> μ),
      Fin.cons b (fun i=>(r i:ℝ))∉bad (N+1) ξ := by
  have hp : ∀ᵐ r ∂Measure.pi (fun _ : Fin N=> μ),∀ σ : Equiv.Perm (Fin (N+1)),
      ∀ P Q : Pair (N+1),
        score (fun _=>0) (coefficient ξ) ((Fin.cons b (fun i=>(r i:ℝ))) ∘ σ) P=
          score (fun _=>0) (coefficient ξ) ((Fin.cons b (fun i=>(r i:ℝ))) ∘ σ) Q→
            coefficient ξ P=coefficient ξ Q := by
    apply ae_all_iff.mpr
    intro σ
    filter_upwards [ZeroNoiseAffine.ae_cons_score_ties_identical μ
      (fun P i=> coefficient ξ P (σ.symm i)) b hb.ne'] with r hr
    intro P Q he
    simp_rw [score_reindex] at he
    have hh:=hr P Q he
    funext i
    simpa only [Equiv.symm_apply_apply] using congrFun hh (σ i)
  filter_upwards [hp,ZeroNoiseAffine.ae_cons_distinct μ b hb.ne'] with r hr hdist
  have hpos (i : Fin (N+1)) : 0 < (Fin.cons b (fun k => (r k:ℝ)) : Fin (N+1) → ℝ) i :=
    Fin.cases hb (fun j=> hL.trans_le (r j).2.1) i
  intro hbad
  rcases hbad with hrank|hpot
  · rcases hrank with hn|htie
    · obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hn
      exact (not_le.mpr (hpos i)) hi
    · obtain ⟨i,hi⟩:=Set.mem_iUnion.mp htie
      obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hi
      by_cases hij : i=j
      · simp only [if_pos hij,Set.mem_empty_iff_false] at hj
      · exact hdist i j hij (by simpa only [if_neg hij,Set.mem_setOf_eq] using hj)
  · obtain ⟨σ,hσ⟩:=Set.mem_iUnion.mp hpot
    obtain ⟨P,hP⟩:=Set.mem_iUnion.mp hσ
    obtain ⟨Q,hQ⟩:=Set.mem_iUnion.mp hP
    by_cases hPQ : coefficient ξ P=coefficient ξ Q
    · simp only [if_pos hPQ,Set.mem_empty_iff_false] at hQ
    · exact hPQ (hr σ P Q (by simpa only [if_neg hPQ,Set.mem_setOf_eq] using hQ))

lemma topSelection_eventually_eq {N : ℕ} (A : Finset (Fin N)) (c : ℕ)
    (b : Fin N→ℝ) (hpos : ∀ i,0< b i) (hno : ∀ i j,i≠j→ b i≠b j) :
    ∀ᶠ a in 𝓝 b,topSelection A c a=topSelection A c b := by
  have hp : ∀ᶠ a : Fin N→ℝ in 𝓝 b,∀ i,0< a i :=
    Filter.eventually_all.mpr (fun i=>(isOpen_lt continuous_const (continuous_apply i)).mem_nhds (hpos i))
  filter_upwards [comparisons_eventually_eq b hno,hp] with a hc ha
  have hna (i j : Fin N) (hij : i≠j) : a i≠a j := by
    rcases lt_or_gt_of_ne (hno i j hij) with h|h
    · exact ne_of_lt ((hc i j).mpr h)
    · exact ne_of_gt ((hc j i).mpr h)
  ext i
  by_cases hi : i∈A
  · rw [topSelection_iff_strict_rank A c a (fun j _=>(ha j).le) i hi (ha i)
      (fun j _ hji=> hna j i hji),
      topSelection_iff_strict_rank A c b (fun j _=>(hpos j).le) i hi (hpos i)
      (fun j _ hji=> hno j i hji)]
    have he : A.filter (fun j=> a i< a j)=A.filter (fun j=> b i< b j) := by
      ext j
      simp only [Finset.mem_filter,hc i j]
    rw [he]
  · exact iff_of_false (fun h=> hi ((topSelection_feasible A c a).2 h))
      (fun h=> hi ((topSelection_feasible A c b).2 h))

lemma fittingPair_eventually_eq (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N→ℝ)
    (hscore : ∀ P Q : Pair N,
      score (fun _=>0) (coefficient ξ) b P=score (fun _=>0) (coefficient ξ) b Q→
        coefficient ξ P=coefficient ξ Q) :
    ∀ᶠ a in 𝓝 b,fittingPair N H0 H1 c ξ a=fittingPair N H0 H1 c ξ b := by
  by_cases hcap : c-H0≤ N ∧ c-H1≤ N
  · let A:=LowBody.CompleteInformation.Choice (ι:=Fin N) (c-H0)×
      LowBody.CompleteInformation.Choice (ι:=Fin N) (c-H1)
    letI : Nonempty (LowBody.CompleteInformation.Choice (ι:=Fin N) (c-H0)) :=
      LowBody.CompleteInformation.choice_nonempty (c-H0) (by simpa using hcap.1)
    letI : Nonempty (LowBody.CompleteInformation.Choice (ι:=Fin N) (c-H1)) :=
      LowBody.CompleteInformation.choice_nonempty (c-H1) (by simpa using hcap.2)
    let f : (Fin N→ℝ)→ A→ℝ:=fun a P=> LowBody.CompleteInformation.potential (1-ξ) a P.1.1 P.2.1
    have he (a : Fin N→ℝ) (P : A) : f a P=score (fun _=>0) (coefficient ξ) a (P.1.1,P.2.1) := by
      simpa only [f,score,zero_add,coefficient] using
        LowBody.potential_eq_copyCoefficient (1-ξ) a (P.1.1,P.2.1)
    have hs:=select_eventually_eq f (fun P=> by
      simp_rw [he]
      exact continuous_score _ _ _) b (by
        intro P Q hPQ a
        have hc:=hscore (P.1.1,P.2.1) (Q.1.1,Q.2.1) (by simpa only [he] using hPQ)
        simp only [he,score,hc])
    filter_upwards [hs] with a ha
    have hh:=congrArg (fun P : A=>(P.1.1,P.2.1)) ha
    simpa only [fittingPair,dif_pos hcap,LowBody.CompleteInformation.selector,f] using hh
  · exact Eventually.of_forall fun a=> by simp only [fittingPair,dif_neg hcap]

lemma activeRule_eventually_eq (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N→ℝ)
    (hpos : ∀ i,0< b i) (hno : ∀ i j,i≠j→ b i≠b j)
    (hscore : ∀ P Q : Pair N,
      score (fun _=>0) (coefficient ξ) b P=score (fun _=>0) (coefficient ξ) b Q→
        coefficient ξ P=coefficient ξ Q) :
    ∀ᶠ a in 𝓝 b,∀ side k i,
      activeRule N H0 H1 c ξ side a k i↔activeRule N H0 H1 c ξ side b k i := by
  have hp : ∀ᶠ a in 𝓝 b,ownerPool N c a=ownerPool N c b := by
    by_cases hn : N≤2*c
    · exact Eventually.of_forall fun a=> by simp only [ownerPool,if_pos hn]
    · simpa only [ownerPool,if_neg hn] using topSelection_eventually_eq Finset.univ (2*c) b hpos hno
  filter_upwards [fittingPair_eventually_eq N H0 H1 c ξ b hscore,hp,
    comparisons_eventually_eq b hno] with a hfit hpool hcmp
  have ho (side : Bool) : owners N H0 c a side=owners N H0 c b side := by simp only [owners,hpool]
  have hf (side : Bool) : fittingActive N H0 H1 c ξ a side=fittingActive N H0 H1 c ξ b side := by
    simp only [fittingActive,hfit]
  have hr (O : Finset (Fin N)) (i : Fin N) :
      O.filter (fun j=> a i< a j)=O.filter (fun j=> b i< b j) := by
    ext j
    simp only [Finset.mem_filter,hcmp i j]
  intro side k i
  simp only [activeRule,hf side,ho side,hr]

theorem sortedFallback_eventually_eq (N H0 H1 c : ℕ) (ξ : ℝ)
    (ν0 : FiniteLaw (EqualPrivateSignal.Marks H0))
    (ν1 : FiniteLaw (EqualPrivateSignal.Marks H1)) (b : Fin N→ℝ)
    (hb : b∉bad N ξ) :
    ∀ᶠ a in 𝓝 b,∀ i,
      sortedFallback N H0 H1 c ξ ν0 ν1 a i=sortedFallback N H0 H1 c ξ ν0 ν1 b i := by
  obtain ⟨hpos,hno,hscore⟩:=regular_of_not_bad ξ b hb
  let σ:=permutation b
  have hr:=activeRule_eventually_eq N H0 H1 c ξ (b ∘ σ)
    (fun i=> hpos (σ i)) (fun i j hij=> hno (σ i) (σ j) (fun he=> hij (σ.injective he))) (hscore σ)
  have hc:=(continuous_reindex_fixed σ).continuousAt.tendsto.eventually hr
  filter_upwards [hc,permutation_eventually_eq b hno] with a ha hp
  intro i
  unfold sortedFallback
  have hi : focalRank a i=focalRank b i := by simp only [focalRank,hp]
  rw [hi]
  apply countLaw_congr_rules
  intro side k
  simpa only [sorted,hp,σ] using ha side k (focalRank b i)

end FCAppendix.Affine.Tail04.ZeroNoiseFallback
