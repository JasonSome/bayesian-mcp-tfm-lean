import FCAppendix.Affine.Tail04.AtypicalFittingFiniteLoss
import FCAppendix.Affine.Tail04.UnequalOriginalCountPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.SortedFallbackFiniteLoss
open MeasureTheory Set Classical
open LowBody EqualPrivateSignal AtypicalUnequal AllCountAtypical AtypicalActiveRanks
open SortedAllNoise AtypicalFittingFiniteLoss
open scoped BigOperators

variable {N : ℕ}

lemma comparisons_update_of_no_cross (b : Fin N → ℝ) (i : Fin N) (y : ℝ)
    (hy : b i≤ y) (hn : ∀ j,j≠i → b j∉Icc (b i) y) :
    ∀ j k,(Function.update b i y j< Function.update b i y k ↔ b j< b k) := by
  have hlow (j : Fin N) (hji : j≠i) : b j< y ↔ b j< b i := by
    rcases lt_or_ge (b j) (b i) with hj | hj
    · exact iff_of_true (hj.trans_le hy) hj
    · have hh : y< b j := lt_of_not_ge (fun hh => hn j hji ⟨hj,hh⟩)
      exact iff_of_false (not_lt.mpr hh.le) (not_lt.mpr hj)
  have hhigh (j : Fin N) (hji : j≠i) : y< b j ↔ b i< b j := by
    rcases lt_or_ge (b j) (b i) with hj | hj
    · exact iff_of_false (not_lt.mpr (hj.le.trans hy)) (not_lt.mpr hj.le)
    · have hh : y< b j := lt_of_not_ge (fun hh => hn j hji ⟨hj,hh⟩)
      exact iff_of_true hh (hy.trans_lt hh)
  intro j k
  by_cases hj : j=i <;> by_cases hk : k=i
  · subst j
    subst k
    simp
  · subst j
    simpa only [Function.update_self,Function.update_of_ne hk] using hhigh k hk
  · subst k
    simpa only [Function.update_self,Function.update_of_ne hj] using hlow j hj
  · simp only [Function.update_of_ne hj,Function.update_of_ne hk]

lemma distinct_of_same_comparisons (a b : Fin N → ℝ)
    (hc : ∀ j k,a j< a k ↔ b j< b k) (hb : ∀ j k,j≠k → b j≠b k) :
    ∀ j k,j≠k → a j≠a k := by
  intro j k hjk he
  rcases lt_or_gt_of_ne (hb j k hjk) with h | h
  · have hh := (hc j k).mpr h
    exact (ne_of_lt hh) he
  · have hh := (hc k j).mpr h
    exact (ne_of_lt hh) he.symm

lemma topSelection_eq_of_comparisons (A : Finset (Fin N)) (c : ℕ)
    (a b : Fin N → ℝ) (ha : ∀ j,0< a j) (hb : ∀ j,0< b j)
    (hno : ∀ j k,j≠k → b j≠b k) (hc : ∀ j k,a j< a k ↔ b j< b k) :
    topSelection A c a=topSelection A c b := by
  have hano := distinct_of_same_comparisons a b hc hno
  ext i
  by_cases hi : i∈A
  · rw [topSelection_iff_strict_rank A c a (fun j _ => (ha j).le) i hi (ha i)
      (fun j _ hji => hano j i hji),
      topSelection_iff_strict_rank A c b (fun j _ => (hb j).le) i hi (hb i)
      (fun j _ hji => hno j i hji)]
    have he : A.filter (fun j => a i< a j)=A.filter (fun j => b i< b j) := by
      ext j
      simp only [Finset.mem_filter,hc i j]
    rw [he]
  · exact iff_of_false (fun h => hi ((topSelection_feasible A c a).2 h))
      (fun h => hi ((topSelection_feasible A c b).2 h))

lemma ownerPool_eq_of_comparisons (N c : ℕ) (a b : Fin N → ℝ)
    (ha : ∀ j,0< a j) (hb : ∀ j,0< b j)
    (hno : ∀ j k,j≠k → b j≠b k) (hc : ∀ j k,a j< a k ↔ b j< b k) :
    ownerPool N c a=ownerPool N c b := by
  unfold ownerPool
  split_ifs
  · rfl
  · exact topSelection_eq_of_comparisons Finset.univ (2*c) a b ha hb hno hc

theorem sortedFallback_eq_of_no_cross (N H0 H1 c : ℕ) (ξ : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (hb : ∀ j,0< b j) (hno : ∀ j k,j≠k → b j≠b k)
    (i : Fin N) (y : ℝ) (hy : b i≤ y)
    (hn : ∀ j,j≠i → b j∉Icc (b i) y)
    (hbranch : EitherSlack N H0 H1 c ∨ 2*c< N+H0+H1) :
    sortedFallback N H0 H1 c ξ ν0 ν1 (Function.update b i y) i=
      sortedFallback N H0 H1 c ξ ν0 ν1 b i := by
  let a := Function.update b i y
  have hc := comparisons_update_of_no_cross b i y hy hn
  have hperm : PrivateRowSorting.permutation a=PrivateRowSorting.permutation b :=
    permutation_eq_of_comparisons a b hc
  have hrank : focalRank a i=focalRank b i := by simp only [focalRank,hperm]
  have hapos (j : Fin N) : 0< a j := by
    by_cases hj : j=i
    · subst j
      simpa only [a,Function.update_self] using (hb i).trans_le hy
    · simpa only [a,Function.update_of_ne hj] using hb j
  have hsc (j k : Fin N) : sorted a j< sorted a k ↔ sorted b j< sorted b k := by
    simpa only [sorted,Function.comp_apply,hperm] using
      hc (PrivateRowSorting.permutation b j) (PrivateRowSorting.permutation b k)
  have hsno (j k : Fin N) (hjk : j≠k) : sorted b j≠sorted b k :=
    hno _ _ ((PrivateRowSorting.permutation b).injective.ne hjk)
  have hp := ownerPool_eq_of_comparisons N c (sorted a) (sorted b)
    (fun j => hapos _) (fun j => hb _) hsno hsc
  have ho (side : Bool) : owners N H0 c (sorted a) side=owners N H0 c (sorted b) side := by
    simp only [owners,hp]
  have hfilter (A : Finset (Fin N)) (j : Fin N) :
      A.filter (fun k => sorted a j< sorted a k)=A.filter (fun k => sorted b j< sorted b k) := by
    ext k
    simp only [Finset.mem_filter,hsc j k]
  unfold sortedFallback
  rw [hrank]
  apply AtypicalActiveNoisy.countLaw_congr_rules
  intro side k
  change activeRule N H0 H1 c ξ side (sorted a) k (focalRank b i) ↔
    activeRule N H0 H1 c ξ side (sorted b) k (focalRank b i)
  rcases hbranch with hs | hs
  · simp only [activeRule,if_pos hs,hfilter]
  · by_cases hsl : EitherSlack N H0 H1 c
    · simp only [activeRule,if_pos hsl,hfilter]
    · have hfit : ¬N+H0+H1≤2*c := not_le.mpr hs
      simp only [activeRule,if_neg hsl,if_neg hfit,ho side,hfilter]

lemma affineCountUtility_bounds (C : CountLaw 2) {eta v b B : ℝ}
    (he0 : 0≤ eta) (he1 : eta≤1) (hv : 0≤ v) (hb : 0≤ b) (hbB : b≤ B) :
    -2*B≤ affineCountUtility C v b eta he0 he1 ∧
      affineCountUtility C v b eta he0 he1≤ v := by
  have hpoint (r : Fin 3) :
      -2*B≤ userPayoff v b 0 (Schedule.affine 2 eta he0 he1).charge (Schedule.once 2).charge r.val ∧
      userPayoff v b 0 (Schedule.affine 2 eta he0 he1).charge (Schedule.once 2).charge r.val≤ v := by
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr with rfl | rfl | rfl <;>
      norm_num [userPayoff,Schedule.affine,Schedule.once,successIndicator] <;>
      (try constructor) <;> nlinarith
  constructor
  · have h := C.expect_mono (fun r => (hpoint r).1)
    simpa only [FiniteLaw.expect_const,affineCountUtility,CountLaw.utility] using h
  · have h := C.expect_mono (fun r => (hpoint r).2)
    simpa only [FiniteLaw.expect_const,affineCountUtility,CountLaw.utility] using h

lemma affineCountUtility_price_loss (C : CountLaw 2) {eta v b y : ℝ}
    (he0 : 0≤ eta) (he1 : eta≤1) (hy : b≤ y) :
    affineCountUtility C v b eta he0 he1-affineCountUtility C v y eta he0 he1≤2*(y-b) := by
  have hpoint (r : Fin 3) :
      userPayoff v b 0 (Schedule.affine 2 eta he0 he1).charge (Schedule.once 2).charge r.val-
      userPayoff v y 0 (Schedule.affine 2 eta he0 he1).charge (Schedule.once 2).charge r.val≤2*(y-b) := by
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr with rfl | rfl | rfl <;>
      norm_num [userPayoff,Schedule.affine,Schedule.once,successIndicator] <;>
      nlinarith
  have h := C.expect_mono hpoint
  simpa only [FiniteLaw.expect_const,FiniteLaw.expect_sub,affineCountUtility,CountLaw.utility] using h

lemma purePair_affine (P : Finset (Fin N)×Finset (Fin N)) (i : Fin N)
    {ξ : ℝ} (hξ0 : 0≤ ξ) (hξ1 : ξ≤1/2) (v : ℝ) (b : Fin N → ℝ) :
    affineCountUtility (twoCoinCountLaw (if i∈P.1 then 1 else 0) (if i∈P.2 then 1 else 0)
      (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
      (by split_ifs <;> norm_num) (by split_ifs <;> norm_num))
      v (b i) (1-2*ξ) (by linarith) (by linarith)=purePayoff (1-ξ) v b P i := by
  unfold affineCountUtility CountLaw.utility
  rw [twoCoinCountLaw_expect]
  by_cases h0 : i∈P.1 <;> by_cases h1 : i∈P.2 <;>
    norm_num [Fin.ext_iff,h0,h1,purePayoff,focalCopy,userPayoff,Schedule.affine,Schedule.once,successIndicator]
  all_goals ring

lemma fitting_count_utility (N H0 H1 c : ℕ) {ξ : ℝ}
    (hξ0 : 0≤ ξ) (hξ1 : ξ≤1/2)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (i : Fin N) (v : ℝ)
    (hsl : ¬EitherSlack N H0 H1 c) (hfit : N+H0+H1≤2*c) :
    affineCountUtility (AtypicalActiveNoisy.countLaw N H0 H1 c ξ ν0 ν1 b i)
      v (b i) (1-2*ξ) (by linarith) (by linarith)=
      purePayoff (1-ξ) v b (fittingPair N H0 H1 c ξ b) i := by
  have h0 : AtypicalActiveNoisy.acceptance N H0 H1 c ξ false ν0 b i=
      if i∈(fittingPair N H0 H1 c ξ b).1 then 1 else 0 := by
    simp only [AtypicalActiveNoisy.acceptance,activeRule,if_neg hsl,if_pos hfit,
      fittingActive,Bool.false_eq_true,ite_false,FiniteLaw.prob_eq_expect,FiniteLaw.expect_const]
  have h1 : AtypicalActiveNoisy.acceptance N H0 H1 c ξ true ν1 b i=
      if i∈(fittingPair N H0 H1 c ξ b).2 then 1 else 0 := by
    simp only [AtypicalActiveNoisy.acceptance,activeRule,if_neg hsl,if_pos hfit,
      fittingActive,ite_true,FiniteLaw.prob_eq_expect,FiniteLaw.expect_const]
  unfold AtypicalActiveNoisy.countLaw
  simp only [h0,h1]
  exact purePair_affine _ i hξ0 hξ1 v b

lemma sorted_fitting_count_utility (N H0 H1 c : ℕ) {ξ : ℝ}
    (hξ0 : 0≤ ξ) (hξ1 : ξ≤1/2)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (i : Fin N) (v : ℝ)
    (hsl : ¬EitherSlack N H0 H1 c) (hfit : N+H0+H1≤2*c) :
    affineCountUtility (sortedFallback N H0 H1 c ξ ν0 ν1 b i)
      v (b i) (1-2*ξ) (by linarith) (by linarith)=
      purePayoff (1-ξ) v b (decodedFitting N H0 H1 c ξ b) i := by
  let k := focalRank b i
  have hb : sorted b k=b i := by simp [k,sorted,focalRank]
  have hc : focalCopy (decodedFitting N H0 H1 c ξ b) i=
      focalCopy (fittingPair N H0 H1 c ξ (sorted b)) k := by
    simpa only [decodedFitting,k,focalRank,Equiv.apply_symm_apply] using
      focalCopy_relabel (PrivateRowSorting.permutation b)
        (fittingPair N H0 H1 c ξ (sorted b)) k
  have h := fitting_count_utility N H0 H1 c hξ0 hξ1 ν0 ν1 (sorted b) k v hsl hfit
  simpa only [sortedFallback,purePayoff,hc,hb] using h

theorem sortedFallback_finite_loss (N H0 H1 c : ℕ) {ξ B v : ℝ}
    (hξ0 : 0≤ ξ) (hξ1 : ξ≤1/2) (hsep : (1-ξ)*B<1)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (hb : ∀ j,b j∈Icc (1:ℝ) B)
    (hno : ∀ j k,j≠k → b j≠b k)
    (i : Fin N) (hiv : b i≤ v) (y : ℝ) (hy : b i< y) (hyB : y≤ B) :
    affineCountUtility (sortedFallback N H0 H1 c ξ ν0 ν1 b i)
      v (b i) (1-2*ξ) (by linarith) (by linarith)-
    affineCountUtility (sortedFallback N H0 H1 c ξ ν0 ν1 (Function.update b i y) i)
      v y (1-2*ξ) (by linarith) (by linarith)≤
      (v+2*B)*crossingCount b i y+2*(y-b i) := by
  have hv : 0≤ v := (by norm_num : (0:ℝ)≤1).trans ((hb i).1.trans hiv)
  have hbi : 0≤ b i := (by norm_num : (0:ℝ)≤1).trans (hb i).1
  have hB : 0≤ B := hbi.trans (hb i).2
  have hy0 : 0≤ y := hbi.trans hy.le
  have he0 : 0≤1-2*ξ := by linarith
  have he1 : 1-2*ξ≤1 := by linarith
  by_cases hcross : ∃ j,j≠i ∧ b j∈Icc (b i) y
  · have h0 := (affineCountUtility_bounds
      (sortedFallback N H0 H1 c ξ ν0 ν1 b i) he0 he1 hv hbi (hb i).2).2
    have h1 := (affineCountUtility_bounds
      (sortedFallback N H0 H1 c ξ ν0 ν1 (Function.update b i y) i)
      he0 he1 hv hy0 hyB).1
    have hc := mul_le_mul_of_nonneg_left (one_le_crossingCount b i y hcross)
      (show 0≤ v+2*B by positivity)
    nlinarith only [h0,h1,hc,hy]
  · have hn : ∀ j,j≠i → b j∉Icc (b i) y := by
      intro j hji hj
      exact hcross ⟨j,hji,hj⟩
    have hz : crossingCount b i y=0 := by
      unfold crossingCount
      apply Finset.sum_eq_zero
      intro j _
      exact if_neg (fun h => hn j h.1 h.2)
    rw [hz,mul_zero,zero_add]
    by_cases hsl : EitherSlack N H0 H1 c
    · rw [sortedFallback_eq_of_no_cross N H0 H1 c ξ ν0 ν1 b
        (fun j => (by norm_num : (0:ℝ)<1).trans_le (hb j).1) hno i y hy.le hn (Or.inl hsl)]
      exact affineCountUtility_price_loss _ he0 he1 hy.le
    · by_cases hfit : N+H0+H1≤2*c
      · have hnsl := nonslack_both N H0 H1 c hsl
        have hres := fitting_residual_counts N H0 H1 c hnsl.1 hnsl.2 hfit
        rw [sorted_fitting_count_utility N H0 H1 c hξ0 hξ1 ν0 ν1 b i v hsl hfit]
        have hup := sorted_fitting_count_utility N H0 H1 c hξ0 hξ1 ν0 ν1
          (Function.update b i y) i v hsl hfit
        simp only [Function.update_self] at hup
        rw [hup]
        have h := sorted_fitting_finite_loss N H0 H1 c hξ1 hsep
          hres.2.2.1 hres.2.2.2.1 b hb i hiv y hy hyB
        rw [hz,mul_zero,zero_add] at h
        have hp : 2*(1-ξ)*(y-b i)≤2*(y-b i) := by
          nlinarith [mul_nonneg hξ0 (sub_nonneg.mpr hy.le)]
        exact h.trans hp
      · rw [sortedFallback_eq_of_no_cross N H0 H1 c ξ ν0 ν1 b
          (fun j => (by norm_num : (0:ℝ)<1).trans_le (hb j).1) hno i y hy.le hn
          (Or.inr (lt_of_not_ge hfit))]
        exact affineCountUtility_price_loss _ he0 he1 hy.le

end FCAppendix.Affine.Tail04.SortedFallbackFiniteLoss
