import FCAppendix.Affine.Hybrid.NativeActivePriority

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes
open EqualCapacity
open Existence.PayOnceBounded (listBids positiveSupport mem_positiveSupport)
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma positiveMarginal_zero_of_nonpos (ξ : ℝ) (r : ℕ) (b : ι→ℝ) (i : ι) (hi : b i ≤ 0) :
    positiveMarginal ξ r b i=0:=by
  apply onSupport_outside
  rw [mem_positiveSupport]
  exact not_lt.mpr hi

lemma positiveMarginal_unique_linear {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ)
    (b q : ι→ℝ) (hb : ∀i,0 ≤ b i) (hq0 : ∀i,0 ≤ q i) (hq1 : ∀i,q i ≤ 1)
    (hqsum : (∑i,q i) ≤ (r:ℝ)) (hqzero : ∀i,b i=0→q i=0)
    (hopt : ∀v : ι→ℝ,(∀i,0 ≤ v i)→(∀i,v i ≤ 1)→(∑i,v i) ≤ (r:ℝ)→
      (∑i,v i*(b i*(1-ξ*q i))) ≤ ∑i,q i*(b i*(1-ξ*q i))) :
    q=positiveMarginal ξ r b:=by
  let p:=positiveMarginal ξ r b
  have hp:=positiveMarginal_spec ξ r hξ hξ1 b
  have hpsum : (∑i,p i) ≤ (r:ℝ):=hp.2.2.le.trans (Nat.cast_le.mpr (min_le_left _ _))
  have h1:=positiveMarginal_linear_optimal hξ hξ1 r b q hq0 hq1 hqsum
  have h2:=hopt p hp.1 hp.2.1 hpsum
  have he : (∑i,ξ*b i*(q i-p i)^2)=
      ((∑i,q i*(b i*(1-ξ*p i)))-(∑i,p i*(b i*(1-ξ*p i))))+
      ((∑i,p i*(b i*(1-ξ*q i)))-(∑i,q i*(b i*(1-ξ*q i)))):=by
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs : (∑i,ξ*b i*(q i-p i)^2) ≤ 0:=by rw [he];linarith
  funext i
  by_cases hbi:0<b i
  · have hi:=Finset.single_le_sum (s:=Finset.univ)
      (f:=fun k=>ξ*b k*(q k-p k)^2)
      (fun k _=>mul_nonneg (mul_nonneg hξ.le (hb k)) (sq_nonneg _)) (Finset.mem_univ i)
    have hc : 0<ξ*b i:=mul_pos hξ hbi
    have hs0 : (q i-p i)^2 ≤ 0:=
      le_of_mul_le_mul_left (by simpa only [mul_zero] using hi.trans hs) hc
    have hz : q i-p i=0:=by nlinarith [sq_nonneg (q i-p i)]
    exact sub_eq_zero.mp hz
  · have hz : b i=0:=le_antisymm (le_of_not_gt hbi) (hb i)
    rw [hqzero i hz,positiveMarginal_zero_of_nonpos ξ r b i hz.le]

def eraseActiveBids (A : Finset ι) (b : ι→ℝ) : ι→ℝ:=fun i=>if i∈A then 0 else b i

theorem positiveMarginal_erase_active {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (r : ℕ)
    (b : ι→ℝ) (hb : ∀i,0 ≤ b i) (A : Finset ι) (hfit : A.card ≤ r)
    (hactive : ∀i∈A,positiveMarginal ξ r b i=1) :
    ∀i∉A,positiveMarginal ξ r b i=positiveMarginal ξ (r-A.card) (eraseActiveBids A b) i:=by
  let p:=positiveMarginal ξ r b
  let q : ι→ℝ:=fun i=>if i∈A then 0 else p i
  let low:=eraseActiveBids A b
  have hpactive (i : ι) (hi:i∈A) : p i=1:=hactive i hi
  have hp:=positiveMarginal_spec ξ r hξ hξ1 b
  have hpSum : (∑i,p i) ≤ (r:ℝ):=hp.2.2.le.trans (Nat.cast_le.mpr (min_le_left _ _))
  have hq0 (i : ι) : 0 ≤ q i:=by dsimp only [q];split <;> [exact le_rfl;exact hp.1 i]
  have hq1 (i : ι) : q i ≤ 1:=by dsimp only [q];split <;> [exact zero_le_one;exact hp.2.1 i]
  have hsum : (∑i,p i)=(A.card:ℝ)+∑i,q i:=by
    calc
      _=∑i,((if i∈A then (1:ℝ) else 0)+q i):=by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi:i∈A
        · simp only [q,if_pos hi,hpactive i hi,add_zero]
        · simp only [q,if_neg hi,zero_add]
      _=_:=by rw [Finset.sum_add_distrib];simp
  have hqsum : (∑i,q i) ≤ ((r-A.card:ℕ):ℝ):=by
    rw [Nat.cast_sub hfit]
    linarith
  have hlow (i : ι) : 0 ≤ low i:=by dsimp only [low,eraseActiveBids];split <;> [exact le_rfl;exact hb i]
  have hqzero (i : ι) (hi:low i=0) : q i=0:=by
    by_cases ha:i∈A
    · simp only [q,if_pos ha]
    · have hh:b i=0:=by simpa only [low,eraseActiveBids,if_neg ha] using hi
      simp only [q,if_neg ha]
      exact positiveMarginal_zero_of_nonpos ξ r b i hh.le
  have hopt : ∀v : ι→ℝ,(∀i,0 ≤ v i)→(∀i,v i ≤ 1)→(∑i,v i) ≤ ((r-A.card:ℕ):ℝ)→
      (∑i,v i*(low i*(1-ξ*q i))) ≤ ∑i,q i*(low i*(1-ξ*q i)):=by
    intro v hv0 hv1 hvsum
    let full : ι→ℝ:=fun i=>if i∈A then 1 else v i
    have hf0 (i : ι) : 0 ≤ full i:=by dsimp only [full];split <;> [exact zero_le_one;exact hv0 i]
    have hf1 (i : ι) : full i ≤ 1:=by dsimp only [full];split <;> [exact le_rfl;exact hv1 i]
    have hfsum : (∑i,full i) ≤ (r:ℝ):=by
      have hh : (∑i,full i) ≤ (A.card:ℝ)+∑i,v i:=by
        calc
          _ ≤ ∑i,((if i∈A then (1:ℝ) else 0)+v i):=by
            apply Finset.sum_le_sum
            intro i _
            by_cases hi:i∈A
            · simp only [full,if_pos hi];linarith [hv0 i]
            · simp only [full,if_neg hi,zero_add,le_refl]
          _=_:=by rw [Finset.sum_add_distrib];simp
      rw [Nat.cast_sub hfit] at hvsum
      linarith
    have hh:=positiveMarginal_linear_optimal hξ hξ1 r b full hf0 hf1 hfsum
    have he (v' : ι→ℝ) :
        (∑i,(if i∈A then 1 else v' i)*(b i*(1-ξ*p i)))=
          (∑i∈A,b i*(1-ξ))+(∑i,v' i*(low i*(1-ξ*q i))):=by
      have hA : (∑i∈A,b i*(1-ξ))=∑i,if i∈A then b i*(1-ξ) else 0:=by simp
      rw [hA,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi:i∈A
      · simp only [hi,if_true,hpactive i hi,low,eraseActiveBids,q,mul_zero,sub_zero,mul_one,one_mul,add_zero]
      · simp only [hi,if_false,low,eraseActiveBids,q,zero_add]
    have hpeq : p=fun i=>if i∈A then 1 else q i:=by
      funext i
      by_cases hi:i∈A
      · simp only [if_pos hi,hpactive i hi]
      · simp only [if_neg hi,q]
    change (∑i,full i*(b i*(1-ξ*p i))) ≤ ∑i,p i*(b i*(1-ξ*p i)) at hh
    rw [show full=(fun i=>if i∈A then 1 else v i) from rfl,he] at hh
    calc
      _ ≤ (∑i,p i*(b i*(1-ξ*p i)))-(∑i∈A,b i*(1-ξ)):=by linarith
      _=∑i,q i*(low i*(1-ξ*q i)):=by
        have hpe : (∑i,p i*(b i*(1-ξ*p i)))=
            ∑i,(if i∈A then 1 else q i)*(b i*(1-ξ*p i)):=by
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg (fun t : ℝ=>t*(b i*(1-ξ*p i))) (congrFun hpeq i)
        rw [hpe,he]
        ring
  have heq:=positiveMarginal_unique_linear hξ hξ1 (r-A.card) low q hlow hq0 hq1 hqsum hqzero hopt
  intro i hi
  have hh:=congrFun heq i
  simpa only [q,if_neg hi] using hh

variable {m : ℕ}

theorem equal_acceptance_low_residual (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (he:residual c 0 X=residual c 1 X) (d : ℝ) (hd : 0 ≤ d) (A : Finset (Fin m))
    (hA : ∀i∈A,d<(1-ξ)*entryBid (X.1 i)) (hlow : ∀i∉A,entryBid (X.1 i) ≤ d)
    (hfit : A.card ≤ residual c 0 X) (j : Fin 2) (i : Fin m) (hi:i∉A) :
    acceptance ξ hξ hξ1 c j X i=
      positiveMarginal ξ (residual c 0 X-A.card) (eraseActiveBids A (listBids X.1)) i:=by
  have hactive : ∀k∈A,positiveMarginal ξ (residual c 0 X) (listBids X.1) k=1:=by
    intro k hk
    rw [←acceptance_equal ξ hξ hξ1 c 0 X he k]
    have hh (s : unitInterval) : k∈select ξ hξ hξ1 c 0 X s:=
      active_included_when_fit ξ hξ hξ1 c X hX 0 s d hd A hA hlow hfit hk
    simp only [acceptance,if_pos (hh _),integral_const,probReal_univ,smul_eq_mul,mul_one]
  rw [acceptance_equal ξ hξ hξ1 c j X he]
  apply positiveMarginal_erase_active hξ hξ1 _ _ _ A hfit hactive i hi
  intro k
  have heB : listBids X.1 k=entryBid (X.1 k):=by cases hv:X.1 k <;> simp [listBids,entryBid,hv]
  rw [heB]
  exact hX k

end FCAppendix.Affine.Hybrid.NativeContinuation
