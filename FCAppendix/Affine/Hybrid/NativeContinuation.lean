import FCAppendix.Affine.Hybrid.NativeEqual
import FCAppendix.Affine.Hybrid.ClassifiedOptimality
import FCAppendix.Affine.TaggedPureResidual

set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes
open Existence.PayOnceBounded (listBids)
open scoped BigOperators

attribute [local irreducible] NativeEqual.sample

variable {m c : ℕ}

def residual (c : ℕ) (j : Fin 2) (X : ClassifiedContext m) : ℕ:=c-contextUpper j X

lemma measurable_residual (c : ℕ) (j : Fin 2) : Measurable (residual (m:=m) c j):=
  measurable_const.sub (measurable_contextUpper j)

def purePair (ξ : ℝ) (c : ℕ) (X : ClassifiedContext m) : ResidualPotential.Pair m:=
  ResidualPotential.selection (1-ξ) X.1 (residual c 0 X) (residual c 1 X)

def select (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) : Finset (Fin m):=
  if residual c 0 X=residual c 1 X then NativeEqual.sample m ξ hξ hξ1 (residual c 0 X) X.1 s
  else if j=0 then (purePair ξ c X).1 else (purePair ξ c X).2

lemma measurable_select (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (j : Fin 2) :
    Measurable (Function.uncurry (select (m:=m) ξ hξ hξ1 c j)) := by
  have heq : MeasurableSet {q : ClassifiedContext m×unitInterval | residual c 0 q.1=residual c 1 q.1}:=
    measurableSet_eq_fun ((measurable_residual c 0).comp measurable_fst)
      ((measurable_residual c 1).comp measurable_fst)
  have he : Measurable (fun q : ClassifiedContext m×unitInterval=>
      NativeEqual.sample m ξ hξ hξ1 (residual c 0 q.1) q.1.1 q.2):=
    (NativeEqual.measurable_sample_capacity m ξ hξ hξ1).comp
      (((measurable_residual c 0).comp measurable_fst).prodMk (measurable_fst.fst.prodMk measurable_snd))
  have hp : Measurable (purePair (m:=m) ξ c):=
    ResidualPotential.measurable_selection measurable_const measurable_fst
      (measurable_residual c 0) (measurable_residual c 1)
  change Measurable (fun q : ClassifiedContext m×unitInterval=>
    if residual c 0 q.1=residual c 1 q.1 then
      NativeEqual.sample m ξ hξ hξ1 (residual c 0 q.1) q.1.1 q.2
    else if j=0 then (purePair ξ c q.1).1 else (purePair ξ c q.1).2)
  apply Measurable.ite heq he
  by_cases hj:j=0
  · simpa only [hj,if_true,Function.comp_def] using (hp.fst.comp measurable_fst)
  · simpa only [hj,if_false,Function.comp_def] using (hp.snd.comp measurable_fst)

lemma select_feasible (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) :
    LocallyFeasible X.1 (residual c j X) (select ξ hξ hξ1 c j X s) := by
  have hp:=ResidualPotential.selection_feasible (1-ξ) (by linarith : 0 ≤ 1-ξ)
    X.1 (residual c 0 X) (residual c 1 X)
  by_cases he:residual c 0 X=residual c 1 X
  · have hs:=NativeEqual.sample_feasible m ξ hξ hξ1 (residual c 0 X) X.1 s
    fin_cases j
    · change LocallyFeasible X.1 (residual c 0 X) (select ξ hξ hξ1 c 0 X s)
      rw [select,if_pos he]
      exact hs
    · change LocallyFeasible X.1 (residual c 1 X) (select ξ hξ hξ1 c 1 X s)
      rw [select,if_pos he,←he]
      exact hs
  · fin_cases j
    · change LocallyFeasible X.1 (residual c 0 X) (select ξ hξ hξ1 c 0 X s)
      rw [select,if_neg he,if_pos rfl]
      exact hp.1
    · change LocallyFeasible X.1 (residual c 1 X) (select ξ hξ hξ1 c 1 X s)
      rw [select,if_neg he,if_neg (by decide : (1:Fin 2)≠0)]
      exact hp.2

def contextPolicy (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) : ContextPolicy m c unitInterval where
  select:=select ξ hξ hξ1 c
  measurable:=measurable_select ξ hξ hξ1 c
  feasible:=select_feasible ξ hξ hξ1 c

def acceptance (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) : ℝ:=
  ∫s : unitInterval,(if i∈select ξ hξ hξ1 c j X s then (1:ℝ) else 0) ∂(volume : Measure unitInterval)

def receipt (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) : ℝ:=
  entryBid (X.1 i)*(1-ξ*acceptance ξ hξ hξ1 c (otherProposer j) X i)

lemma acceptance_equal (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (he:residual c 0 X=residual c 1 X) (i : Fin m) :
    acceptance ξ hξ hξ1 c j X i=EqualCapacity.positiveMarginal ξ (residual c 0 X) (listBids X.1) i:=by
  simp only [acceptance,select,if_pos he]
  exact NativeEqual.sample_acceptance m ξ hξ hξ1 (residual c 0 X) X.1 i

lemma acceptance_pure (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (he:residual c 0 X≠residual c 1 X) (i : Fin m) :
    acceptance ξ hξ hξ1 c j X i=
      if i∈(if j=0 then (purePair ξ c X).1 else (purePair ξ c X).2) then (1:ℝ) else 0:=by
  simp only [acceptance,select,if_neg he,integral_const,probReal_univ,smul_eq_mul,one_mul]

lemma pure_numerical_optimal {ξ : ℝ} (hξ1 : ξ<1) (L : LocalList m) (hL : NonnegativeList L)
    (r₀ r₁ : ℕ) :
    let P:=ResidualPotential.selection (1-ξ) L r₀ r₁
    Finite.Optimal r₀ (fun i=>entryBid (L i)*(1-ξ*(if i∈P.2 then (1:ℝ) else 0))) P.1 ∧
    Finite.Optimal r₁ (fun i=>entryBid (L i)*(1-ξ*(if i∈P.1 then (1:ℝ) else 0))) P.2:=by
  let P:=ResidualPotential.selection (1-ξ) L r₀ r₁
  have hf:=ResidualPotential.selection_feasible (1-ξ) (by linarith : 0 ≤ 1-ξ) L r₀ r₁
  have hm:=ResidualPotential.selection_nash (1-ξ) (by linarith : 0 ≤ 1-ξ) L r₀ r₁
  have hrevenue (S T : Finset (Fin m)) :
      LowBody.CompleteInformation.revenue (1-ξ) (ResidualPotential.bid L) S T=
        ∑i∈S,entryBid (L i)*(1-ξ*(if i∈T then (1:ℝ) else 0)):=by
    unfold LowBody.CompleteInformation.revenue
    apply Finset.sum_congr rfl
    intro i _
    rw [show ResidualPotential.bid L i=entryBid (L i) from max_eq_left (hL i)]
    by_cases hi:i∈T
    · simp only [if_pos hi];ring
    · simp only [if_neg hi,mul_zero,sub_zero,mul_one]
  have hfilter (S T : Finset (Fin m)) :
      (∑i∈S.filter (fun i=>L i≠none),entryBid (L i)*(1-ξ*(if i∈T then (1:ℝ) else 0)))=
        ∑i∈S,entryBid (L i)*(1-ξ*(if i∈T then (1:ℝ) else 0)):=by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:L i=none
    · simp only [hi,ne_eq,not_true_eq_false,if_false,entryBid,zero_mul]
    · simp only [hi,ne_eq,not_false_eq_true,if_true]
  constructor
  · refine ⟨hf.1.1,?_⟩
    intro S hS
    have hh:=hm.1 (S.filter (fun i=>L i≠none))
      ⟨(Finset.card_filter_le _ _).trans hS,fun i hi=>(Finset.mem_filter.mp hi).2⟩
    rw [hrevenue,hrevenue,hfilter] at hh
    exact hh
  · refine ⟨hf.2.1,?_⟩
    intro S hS
    have hh:=hm.2 (S.filter (fun i=>L i≠none))
      ⟨(Finset.card_filter_le _ _).trans hS,fun i hi=>(Finset.mem_filter.mp hi).2⟩
    rw [hrevenue,hrevenue,hfilter] at hh
    exact hh

theorem select_numerical_optimal (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1) (j : Fin 2) (s : unitInterval) :
    Finite.Optimal (residual c j X) (receipt ξ hξ hξ1 c j X) (select ξ hξ hξ1 c j X s):=by
  by_cases he:residual c 0 X=residual c 1 X
  · have hr : residual c j X=residual c 0 X:=by
      fin_cases j
      · rfl
      · exact he.symm
    have hh:=NativeEqual.sample_optimal m ξ hξ hξ1 (residual c 0 X) X.1 s
    have hre : receipt ξ hξ hξ1 c j X=
        fun i=>listBids X.1 i*(1-ξ*EqualCapacity.positiveMarginal ξ (residual c 0 X) (listBids X.1) i):=by
      funext i
      rw [receipt,acceptance_equal ξ hξ hξ1 c (otherProposer j) X he]
      have heB : entryBid (X.1 i)=listBids X.1 i:=by cases hi:X.1 i <;> simp [entryBid,listBids,hi]
      rw [heB]
    simpa only [hr,hre,select,if_pos he] using hh
  · have hh:=pure_numerical_optimal hξ1 X.1 hX (residual c 0 X) (residual c 1 X)
    have hre : receipt ξ hξ hξ1 c j X=fun i=>entryBid (X.1 i)*
        (1-ξ*(if i∈(if j=0 then (purePair ξ c X).2 else (purePair ξ c X).1) then (1:ℝ) else 0)):=by
      funext i
      rw [receipt,acceptance_pure ξ hξ hξ1 c (otherProposer j) X he]
      fin_cases j <;> simp [otherProposer]
    rw [hre]
    by_cases hj:j=0
    · subst j
      change Finite.Optimal (residual c 0 X)
        (fun i=>entryBid (X.1 i)*(1-ξ*(if i∈(purePair ξ c X).2 then (1:ℝ) else 0)))
        (select ξ hξ hξ1 c 0 X s)
      rw [select,if_neg he,if_pos rfl]
      exact hh.1
    · have hj1 : j=1:=by omega
      subst j
      change Finite.Optimal (residual c 1 X)
        (fun i=>entryBid (X.1 i)*(1-ξ*(if i∈(purePair ξ c X).1 then (1:ℝ) else 0)))
        (select ξ hξ hξ1 c 1 X s)
      rw [select,if_neg he,if_neg (by decide : (1:Fin 2)≠0)]
      exact hh.2

theorem contextPolicy_lower_optimal (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (Gamma : FiniteGame m 2 c unitInterval) (hseed:Gamma.seedLaw=volume)
    (j : Fin 2) (X : ClassifiedContext m) (hX : NonnegativeList X.1) (s : unitInterval) :
    Finite.Optimal (c-contextUpper j X)
      (lowerContextReceipt Gamma (contextPolicy ξ hξ hξ1 c) ξ j X)
      ((contextPolicy ξ hξ hξ1 c).select j X s):=by
  have hr : lowerContextReceipt Gamma (contextPolicy ξ hξ hξ1 c) ξ j X=receipt ξ hξ hξ1 c j X:=by
    funext i
    simp only [lowerContextReceipt,contextAcceptance,hseed,contextPolicy,receipt,acceptance]
    rfl
  rw [hr]
  exact select_numerical_optimal ξ hξ hξ1 c X hX j s

lemma nonnegative_observedContext (U : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) : NonnegativeList (observedContext U j L).1:=by
  intro i
  change 0 ≤ entryBid (broadcastPart U L i)
  unfold broadcastPart TaggedLocal.lowList
  split
  · exact hL i
  · simp only [entryBid,le_refl]

theorem contextPolicy_observed_lower_optimal (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (Gamma : FiniteGame m 2 c unitInterval) (hseed:Gamma.seedLaw=volume) (U : ℝ)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) (s : unitInterval) :
    let C:=contextPolicy (m:=m) ξ hξ hξ1 c
    Finite.Optimal (c-TaggedLocal.localCount U U L 2)
      (lowerContextReceipt (C.nativeGame Gamma U) C ξ j (observedContext U j L))
      (C.select j (observedContext U j L) s):=by
  have hh:=contextPolicy_lower_optimal ξ hξ hξ1 c
    ((contextPolicy (m:=m) ξ hξ hξ1 c).nativeGame Gamma U) hseed j (observedContext U j L)
    (nonnegative_observedContext U j L ((feasibleObservedList_iff_nonnegative j L).mp hL)) s
  simpa only [contextUpper_observed] using hh

end FCAppendix.Affine.Hybrid.NativeContinuation
