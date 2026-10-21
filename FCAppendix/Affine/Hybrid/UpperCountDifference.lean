import FCAppendix.Affine.Hybrid.CategoricalCounts
import FCAppendix.Probability.FairBinomialBound

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open Affine.LowBody

def upperStep (k : Fin 4) : ℤ:=if k=2 then 1 else if k=3 then -1 else 0

def fairRoute : FiniteLaw Bool:=
  IndependentCounts.bernoulli (1/2) (by norm_num) (by norm_num)

lemma fairRoute_expect (f : Bool→ℝ) :
    fairRoute.expect f=(1/2)*f false+(1/2)*f true := by
  unfold fairRoute
  rw [IndependentCounts.expect_bernoulli]
  ring

def upperDifference {N : ℕ} (row : Fin N→Fin 4) : ℤ:=∑i,upperStep (row i)

theorem upperDifference_cons {N : ℕ} (k : Fin 4) (row : Fin N→Fin 4) :
    upperDifference (Fin.cons k row)=upperStep k+upperDifference row := by
  simp only [upperDifference,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

def coinDifference {K : ℕ} (coins : Fin K→Bool) : ℤ:=
  2*(hitCount (fun b=>b=true) coins:ℤ)-(K:ℤ)

theorem coinDifference_cons {K : ℕ} (b : Bool) (coins : Fin K→Bool) :
    coinDifference (Fin.cons b coins)=(if b then (1:ℤ) else -1)+coinDifference coins := by
  rw [coinDifference,hitCount_cons]
  simp only [Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
    unfold coinDifference <;> omega

lemma categorical_upperStep_expect (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (G : Measure ℝ) [IsProbabilityMeasure G] (f : ℤ→ℝ) :
    (categoryLaw s a h hs ha hh hsum G).expect (fun k=>f (upperStep k))=
      (1-h)*f 0+h/2*f 1+h/2*f (-1) := by
  rw [categoryLaw_expect]
  norm_num [upperStep,Fin.ext_iff]
  nlinarith [congrArg (fun x : ℝ=>x*f 0) hsum]

lemma fair_coin_walk_succ (K : ℕ) (f : ℤ→ℝ) :
    (CommonList.iid fairRoute (K+1)).expect
      (fun coins=>f (coinDifference coins))=
      (1/2)*(CommonList.iid fairRoute K).expect
        (fun coins=>f (-1+coinDifference coins))+
      (1/2)*(CommonList.iid fairRoute K).expect
        (fun coins=>f (1+coinDifference coins)) := by
  rw [CommonList.expect_iid_succ,fairRoute_expect]
  simp only [coinDifference_cons,Bool.false_eq_true,↓reduceIte]

def fairWalkExpectation (K : ℕ) (f : ℤ→ℝ) : ℝ:=
  (CommonList.iid fairRoute K).expect (fun coins=>f (coinDifference coins))

lemma fairWalkExpectation_succ (K : ℕ) (f : ℤ→ℝ) :
    fairWalkExpectation (K+1) f=
      (1/2)*fairWalkExpectation K (fun z=>f (-1+z))+
      (1/2)*fairWalkExpectation K (fun z=>f (1+z)):=fair_coin_walk_succ K f

theorem upperDifference_binomial_mixture (s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N : ℕ) (f : ℤ→ℝ) :
    (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).expect
      (fun row=>f (upperDifference row))=
      (IndependentCounts.binomial N h hh hh1).expect (fun K=>fairWalkExpectation K.val f) := by
  induction N generalizing f with
  | zero=>
    rw [CommonList.expect_iid_zero]
    simp [IndependentCounts.binomial,IndependentCounts.independentCount,upperDifference,
      fairWalkExpectation,coinDifference,hitCount]
  | succ N ih=>
    rw [CommonList.expect_iid_succ,IndependentCounts.expect_binomial_succ]
    simp only [upperDifference_cons]
    have hstep:=categorical_upperStep_expect s a h hs ha hh hsum G
      (fun z=>(CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).expect
        (fun row=>f (z+upperDifference row)))
    rw [hstep]
    simp only [zero_add]
    rw [ih f,ih (fun z=>f (1+z)),ih (fun z=>f (-1+z))]
    have he (K : Fin (N+1)) :
        fairWalkExpectation (IndependentCounts.addCount N true K).val f=
          (1/2)*fairWalkExpectation K.val (fun z=>f (-1+z))+
          (1/2)*fairWalkExpectation K.val (fun z=>f (1+z)) := by
      rw [IndependentCounts.val_add_true,Nat.add_comm 1]
      exact fairWalkExpectation_succ K.val f
    simp only [IndependentCounts.val_add_false]
    rw [(IndependentCounts.binomial N h hh hh1).expect_congr he]
    rw [FiniteLaw.expect_add,FiniteLaw.expect_const_mul,FiniteLaw.expect_const_mul]
    ring

theorem fair_coin_difference_probability_le (K : ℕ) (q : ℤ) :
    (CommonList.iid fairRoute K).prob
      (fun coins=>coinDifference coins=q) ≤ Real.sqrt (2/((K:ℝ)+1)) := by
  let F:=fairRoute
  by_cases hsol : ∃k : ℕ,2*(k:ℤ)-(K:ℤ)=q
  · obtain ⟨k,hk⟩:=hsol
    have he (coins : Fin K→Bool) : coinDifference coins=q↔hitCount (fun b=>b=true) coins=k := by
      unfold coinDifference
      omega
    have hh:=expect_hitCount_binomial F (fun b=>b=true) K (fun r=>if r=k then (1:ℝ) else 0)
    have hp : F.prob (fun b=>b=true)=1/2 := by
      rw [FiniteLaw.prob_eq_expect]
      change fairRoute.expect _=1/2
      rw [fairRoute_expect]
      norm_num
    simp only [hp] at hh
    have hb : (IndependentCounts.binomial K (1/2) (by norm_num) (by norm_num)).prob
        (fun r=>r.val=k)=PiBinomial.pmf K (1/2) k := by
      by_cases hkK : k<K+1
      · rw [FiniteLaw.prob_eq_expect]
        have he' (r : Fin (K+1)) : r.val=k↔r=(⟨k,hkK⟩ : Fin (K+1)):=by
          exact ⟨fun hr=>Fin.ext hr,fun hr=>congrArg Fin.val hr⟩
        simp only [he',FiniteLaw.expect_singleton,PiBinomial.binomial_mass]
      · have hz : ∀r : Fin (K+1),¬r.val=k:=fun r hr=>by omega
        simp only [FiniteLaw.prob_eq_expect,hz,if_false,FiniteLaw.expect_zero,
          PiBinomial.pmf,Nat.choose_eq_zero_of_lt (show K<k by omega),Nat.cast_zero,zero_mul]
    have hprob : (CommonList.iid F K).prob (fun coins=>coinDifference coins=q)=PiBinomial.pmf K (1/2) k := by
      rw [FiniteLaw.prob_eq_expect]
      simp only [he]
      rw [hh,←FiniteLaw.prob_eq_expect,hb]
    exact hprob.le.trans (PiBinomial.pmf_half_le_sqrt K k)
  · have hz : ∀coins : Fin K→Bool,¬coinDifference coins=q:=by
      intro coins hc
      exact hsol ⟨hitCount (fun b=>b=true) coins,hc⟩
    simp only [FiniteLaw.prob_eq_expect,hz,if_false,FiniteLaw.expect_zero]
    exact Real.sqrt_nonneg _

end FCAppendix.Affine.Hybrid
