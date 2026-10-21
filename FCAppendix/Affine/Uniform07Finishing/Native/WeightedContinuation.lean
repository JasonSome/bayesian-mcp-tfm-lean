import FCAppendix.Affine.Uniform07Finishing.Native.WeightedThreshold
import FCAppendix.Affine.Uniform07Finishing.Native.StrictOptimality
import FCAppendix.Affine.Hybrid.NativeContinuation

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open StrictNative
open Existence.PayOnceBounded (listBids measurable_listBids positiveSupport measurable_positiveSupport)
open scoped BigOperators
set_option maxHeartbeats 600000

variable {m : ℕ} [Nonempty (Fin m)]

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def presentSet (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i=>L i≠none)

omit [Nonempty (Fin m)] in
lemma measurable_presentSet : Measurable (presentSet (m:=m)) := by
  apply measurable_to_countable'
  intro S
  have he : presentSet ⁻¹' {S}=⋂i : Fin m,{L : LocalList m | (i∈S ↔ L i≠none)} := by
    ext L
    simp only [mem_preimage,mem_singleton_iff,mem_iInter,mem_setOf_eq]
    exact ⟨fun h i=>by rw [←h];simp [presentSet],
      fun h=>Finset.ext (fun i=>by simpa only [presentSet,Finset.mem_filter,
        Finset.mem_univ,true_and] using (h i).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro i
  by_cases hi:i∈S
  · simpa only [hi,true_iff,Set.compl_setOf] using
      (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).compl
  · simpa only [hi,false_iff,not_not] using
      (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)

def budget (c : ℕ) (j : Fin 2) (X : ClassifiedContext m) : ℕ :=
  min (c-contextUpper j X) (presentSet X.1).card

omit [Nonempty (Fin m)] in
lemma measurable_budget (c : ℕ) (j : Fin 2) : Measurable (budget (m:=m) c j) :=
  (measurable_const.sub (measurable_contextUpper j)).min
    ((measurable_of_countable Finset.card).comp (measurable_presentSet.comp measurable_fst))

def commonBudget (c : ℕ) (X : ClassifiedContext m) : ℕ :=
  min (budget c 0 X) (budget c 1 X)

def larger (c : ℕ) (X : ClassifiedContext m) : Fin 2 :=
  if budget c 0 X< budget c 1 X then 1 else 0

omit [Nonempty (Fin m)] in
lemma measurable_larger (c : ℕ) : Measurable (larger (m:=m) c) :=
  Measurable.ite (measurableSet_lt (measurable_budget c 0) (measurable_budget c 1))
    measurable_const measurable_const

omit [Nonempty (Fin m)] in
lemma larger_budget (c : ℕ) (X : ClassifiedContext m) :
    budget c (larger c X) X=max (budget c 0 X) (budget c 1 X) := by
  by_cases h:budget c 0 X< budget c 1 X
  · simp [larger,h,max_eq_right h.le]
  · simp [larger,h,max_eq_left (le_of_not_gt h)]

omit [Nonempty (Fin m)] in
lemma other_larger_budget (c : ℕ) (X : ClassifiedContext m) :
    budget c (otherProposer (larger c X)) X=commonBudget c X := by
  by_cases h:budget c 0 X< budget c 1 X
  · simp [larger,h,otherProposer,commonBudget,min_eq_left h.le]
  · simp [larger,h,otherProposer,commonBudget,min_eq_right (le_of_not_gt h)]

lemma eq_other_of_ne (j l : Fin 2) (h:j≠l) : j=otherProposer l := by
  fin_cases j <;> fin_cases l <;> simp_all [otherProposer]

lemma measurable_threshold_capacity (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) :
    Measurable (fun q : ℕ×(Fin m→ℝ)=>threshold ξ q.1 q.2) :=
  measurable_from_prod_countable_right (fun d=>measurable_threshold ξ hξ hξ1 d)

lemma measurableSet_validExclusive {X : Type*} [MeasurableSpace X]
    (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (L : X→ LocalList m) (hL:Measurable L)
    (d₀ d₁ : X→ℕ) (hd₀:Measurable d₀) (hd₁:Measurable d₁)
    (E : X→ Finset (Fin m)) (hE:Measurable E) :
    MeasurableSet {x | ValidExclusive ξ (L x) (d₀ x) (d₁ x) (E x)} := by
  have hB : Measurable (fun x=>listBids (remainder (L x) (E x))) :=
    measurable_listBids.comp (measurable_remainder.comp (hL.prodMk hE))
  have hz : Measurable (fun x=>threshold ξ (min (d₀ x) (d₁ x))
      (listBids (remainder (L x) (E x)))) := by
    change Measurable ((fun q : ℕ×(Fin m→ℝ) => threshold ξ q.1 q.2) ∘
      fun x : X => (min (d₀ x) (d₁ x),listBids (remainder (L x) (E x))))
    exact (measurable_threshold_capacity (m:=m) ξ hξ hξ1).comp ((hd₀.min hd₁).prodMk hB)
  have hmem (i : Fin m) : MeasurableSet {x | i∈E x} :=
    hE (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i∈S})
  have hcard := (measurable_of_countable (fun S : Finset (Fin m) => S.card)).comp hE
  have hpositive := (measurable_of_countable (fun S : Finset (Fin m) => S.card)).comp
    (measurable_positiveSupport.comp hB)
  have hpres : MeasurableSet {x | ∀i∈E x,L x i≠none} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    have hi : MeasurableSet {x : X | L x i ≠ none} :=
      (measurableSet_eq_fun ((measurable_pi_apply i).comp hL)
        (measurable_const (a:=(none:Option ℝ)))).compl
    simpa only [imp_iff_not_or,setOf_or,Set.compl_setOf] using (hmem i).compl.union hi
  have hreceipt : MeasurableSet {x | ∀i∈E x,
      (1-ξ)*entryBid (L x i)≤ threshold ξ (min (d₀ x) (d₁ x))
        (listBids (remainder (L x) (E x))) ∧
      threshold ξ (min (d₀ x) (d₁ x))
        (listBids (remainder (L x) (E x)))≤ entryBid (L x i)} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    have hb:=measurable_entryBid.comp ((measurable_pi_apply i).comp hL)
    have hh := (measurableSet_le ((measurable_const (a:=1-ξ)).mul hb) hz).inter
      (measurableSet_le hz hb)
    change MeasurableSet {x : X | (1-ξ)*entryBid (L x i)≤
      threshold ξ (min (d₀ x) (d₁ x)) (listBids (remainder (L x) (E x))) ∧
      threshold ξ (min (d₀ x) (d₁ x)) (listBids (remainder (L x) (E x)))≤entryBid (L x i)} at hh
    simpa only [imp_iff_not_or,setOf_or,Set.compl_setOf,setOf_and] using (hmem i).compl.union hh
  exact (measurableSet_eq_fun hcard ((hd₀.max hd₁).sub (hd₀.min hd₁))).inter
    (hpres.inter ((measurableSet_le (hd₀.min hd₁) hpositive).inter hreceipt))

variable (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
  (plan : ClassifiedContext m→ Option (Finset (Fin m))) (hplan:Measurable plan)

def candidate (X : ClassifiedContext m) : Finset (Fin m) := (plan X).getD ∅

omit [Nonempty (Fin m)] in
include hplan in
lemma measurable_candidate : Measurable (candidate plan) :=
  (measurable_of_countable (fun e : Option (Finset (Fin m))=>e.getD ∅)).comp hplan

def usable (X : ClassifiedContext m) : Prop :=
  plan X≠none ∧ ValidExclusive ξ X.1 (budget c 0 X) (budget c 1 X) (candidate plan X)

include hξ hξ1 hplan in
lemma measurableSet_usable : MeasurableSet {X | usable ξ c plan X} :=
  (measurableSet_eq_fun hplan measurable_const).compl.inter
    (measurableSet_validExclusive ξ hξ hξ1 _ measurable_fst _ _
      (measurable_budget c 0) (measurable_budget c 1) _ (measurable_candidate plan hplan))

def purePair (X : ClassifiedContext m) : ResidualPotential.Pair m :=
  ResidualPotential.selection (1-ξ) X.1 (budget c 0 X) (budget c 1 X)

def balanced (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) : Finset (Fin m) :=
  let S:=Hybrid.NativeEqual.sample m ξ hξ hξ1 (commonBudget c X)
    (remainder X.1 (candidate plan X)) s
  if j=larger c X then candidate plan X∪S else S

def select (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) : Finset (Fin m) :=
  if budget c 0 X=budget c 1 X then
    Hybrid.NativeEqual.sample m ξ hξ hξ1 (budget c 0 X) X.1 s
  else if usable ξ c plan X then balanced ξ hξ hξ1 c plan j X s
  else if j=0 then (purePair ξ c X).1 else (purePair ξ c X).2

omit [Nonempty (Fin m)] in
include hplan in
lemma measurable_balanced (j : Fin 2) :
    Measurable (Function.uncurry (balanced ξ hξ hξ1 c plan j)) := by
  have hd : Measurable (commonBudget (m:=m) c) := (measurable_budget c 0).min (measurable_budget c 1)
  have hB : Measurable (fun X : ClassifiedContext m=>remainder X.1 (candidate plan X)) :=
    measurable_remainder.comp (measurable_fst.prodMk (measurable_candidate plan hplan))
  have hs := (Hybrid.NativeEqual.measurable_sample_capacity m ξ hξ hξ1).comp
    ((hd.comp measurable_fst).prodMk ((hB.comp measurable_fst).prodMk measurable_snd))
  have hu := (measurable_of_countable (fun ES : Finset (Fin m)×Finset (Fin m)=>ES.1∪ES.2)).comp
    (((measurable_candidate plan hplan).comp measurable_fst).prodMk hs)
  exact Measurable.ite
    (measurableSet_eq_fun measurable_const ((measurable_larger c).comp measurable_fst)) hu hs

include hplan in
lemma measurable_select (j : Fin 2) :
    Measurable (Function.uncurry (select ξ hξ hξ1 c plan j)) := by
  have he := (Hybrid.NativeEqual.measurable_sample_capacity m ξ hξ hξ1).comp
    (((measurable_budget c 0).comp measurable_fst).prodMk (measurable_fst.fst.prodMk measurable_snd))
  have hp : Measurable (purePair (m:=m) ξ c) :=
    ResidualPotential.measurable_selection measurable_const measurable_fst
      (measurable_budget c 0) (measurable_budget c 1)
  apply Measurable.ite
    (measurableSet_eq_fun ((measurable_budget c 0).comp measurable_fst)
      ((measurable_budget c 1).comp measurable_fst)) he
  apply Measurable.ite ((measurableSet_usable ξ hξ hξ1 c plan hplan).preimage measurable_fst)
    (measurable_balanced ξ hξ hξ1 c plan hplan j)
  by_cases hj:j=0
  · simpa only [hj,if_true,Function.comp_def] using hp.fst.comp measurable_fst
  · simpa only [hj,if_false,Function.comp_def] using hp.snd.comp measurable_fst

lemma balanced_feasible (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval)
    (hU:usable ξ c plan X) : LocallyFeasible X.1 (budget c j X)
      (balanced ξ hξ hξ1 c plan j X s) := by
  let E:=candidate plan X
  let d:=commonBudget c X
  let S:=Hybrid.NativeEqual.sample m ξ hξ hξ1 d (remainder X.1 E) s
  have hs:=Hybrid.NativeEqual.sample_feasible m ξ hξ hξ1 d (remainder X.1 E) s
  have hc:S.card=d := sample_card ξ hξ hξ1 d (remainder X.1 E) s hU.2.2.2.1
  by_cases hj:j=larger c X
  · subst j
    rw [balanced,if_pos rfl,larger_budget]
    refine ⟨?_,?_⟩
    · apply (Finset.card_union_le _ _).trans
      rw [hU.2.1,hc]
      dsimp only [d,commonBudget]
      omega
    · intro i hi
      rcases Finset.mem_union.mp hi with hie | his
      · exact hU.2.2.1 i hie
      · exact ((remainder_present X.1 E i).mp (hs.2 i his)).2
  · have hj':j=otherProposer (larger c X):=eq_other_of_ne j _ hj
    rw [balanced,if_neg hj,hj',other_larger_budget]
    exact ⟨hs.1,fun i hi=>((remainder_present X.1 E i).mp (hs.2 i hi)).2⟩

lemma select_capped_feasible (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) :
    LocallyFeasible X.1 (budget c j X) (select ξ hξ hξ1 c plan j X s) := by
  by_cases he:budget c 0 X=budget c 1 X
  · have hr:budget c j X=budget c 0 X := by
      fin_cases j
      · rfl
      · exact he.symm
    rw [select,if_pos he,hr]
    exact Hybrid.NativeEqual.sample_feasible m ξ hξ hξ1 _ X.1 s
  · rw [select,if_neg he]
    by_cases hu:usable ξ c plan X
    · rw [if_pos hu]
      exact balanced_feasible ξ hξ hξ1 c plan j X s hu
    · rw [if_neg hu]
      have hp:=ResidualPotential.selection_feasible (1-ξ) (by linarith : 0≤ 1-ξ)
        X.1 (budget c 0 X) (budget c 1 X)
      fin_cases j
      · simpa [purePair] using hp.1
      · simpa [purePair] using hp.2

lemma select_feasible (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) :
    LocallyFeasible X.1 (c-contextUpper j X) (select ξ hξ hξ1 c plan j X s) :=
  ⟨(select_capped_feasible ξ hξ hξ1 c plan j X s).1.trans (min_le_left _ _),
    (select_capped_feasible ξ hξ hξ1 c plan j X s).2⟩

def contextPolicy : ContextPolicy m c unitInterval where
  select:=select ξ hξ hξ1 c plan
  measurable:=measurable_select ξ hξ hξ1 c plan hplan
  feasible:=select_feasible ξ hξ hξ1 c plan

def acceptance (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  ∫s : unitInterval,if i∈select ξ hξ hξ1 c plan j X s then (1:ℝ) else 0

def receipt (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  entryBid (X.1 i)*(1-ξ*acceptance ξ hξ hξ1 c plan (otherProposer j) X i)

lemma acceptance_equal (j : Fin 2) (X : ClassifiedContext m)
    (he:budget c 0 X=budget c 1 X) (i : Fin m) :
    acceptance ξ hξ hξ1 c plan j X i=
      EqualCapacity.positiveMarginal ξ (budget c 0 X) (listBids X.1) i := by
  simp only [acceptance,select,if_pos he]
  exact Hybrid.NativeEqual.sample_acceptance m ξ hξ hξ1 _ X.1 i

lemma acceptance_weighted (j : Fin 2) (X : ClassifiedContext m)
    (he:budget c 0 X≠budget c 1 X) (hu:usable ξ c plan X) (i : Fin m) :
    acceptance ξ hξ hξ1 c plan j X i=
      if j=larger c X ∧ i∈candidate plan X then 1 else
        EqualCapacity.positiveMarginal ξ (commonBudget c X)
          (listBids (remainder X.1 (candidate plan X))) i := by
  simp only [acceptance,select,if_neg he,if_pos hu,balanced]
  by_cases hj:j=larger c X <;> by_cases hi:i∈candidate plan X
  · simp [hj,hi]
  · simpa [hj,hi] using Hybrid.NativeEqual.sample_acceptance m ξ hξ hξ1
      (commonBudget c X) (remainder X.1 (candidate plan X)) i
  · simpa [hj,hi] using Hybrid.NativeEqual.sample_acceptance m ξ hξ hξ1
      (commonBudget c X) (remainder X.1 (candidate plan X)) i
  · simpa [hj,hi] using Hybrid.NativeEqual.sample_acceptance m ξ hξ hξ1
      (commonBudget c X) (remainder X.1 (candidate plan X)) i

lemma acceptance_pure (j : Fin 2) (X : ClassifiedContext m)
    (he:budget c 0 X≠budget c 1 X) (hu:¬usable ξ c plan X) (i : Fin m) :
    acceptance ξ hξ hξ1 c plan j X i=
      if i∈(if j=0 then (purePair ξ c X).1 else (purePair ξ c X).2) then 1 else 0 := by
  simp only [acceptance,select,if_neg he,if_neg hu,integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem select_capped_optimal (j : Fin 2) (X : ClassifiedContext m)
    (hX:NonnegativeList X.1) (s : unitInterval) :
    Finite.Optimal (budget c j X) (receipt ξ hξ hξ1 c plan j X)
      (select ξ hξ hξ1 c plan j X s) := by
  by_cases he:budget c 0 X=budget c 1 X
  · have hr:budget c j X=budget c 0 X := by
      fin_cases j
      · rfl
      · exact he.symm
    have hh:=Hybrid.NativeEqual.sample_optimal m ξ hξ hξ1 (budget c 0 X) X.1 s
    have hrec:receipt ξ hξ hξ1 c plan j X=fun i=>listBids X.1 i*
        (1-ξ*EqualCapacity.positiveMarginal ξ (budget c 0 X) (listBids X.1) i) := by
      funext i
      rw [receipt,acceptance_equal ξ hξ hξ1 c plan (otherProposer j) X he]
      rw [listBids_eq_entry]
    simpa only [select,if_pos he,hr,hrec] using hh
  · by_cases hu:usable ξ c plan X
    · by_cases hj:j=larger c X
      · subst j
        have hn:otherProposer (larger c X)≠larger c X:=otherProposer_ne _
        have hrec:receipt ξ hξ hξ1 c plan (larger c X) X=fun i=>entryBid (X.1 i)*
            (1-ξ*EqualCapacity.positiveMarginal ξ (commonBudget c X)
              (listBids (remainder X.1 (candidate plan X))) i) := by
          funext i
          rw [receipt,acceptance_weighted ξ hξ hξ1 c plan _ X he hu]
          simp only [hn,false_and,if_false]
        rw [hrec,select,if_neg he,if_pos hu,balanced,if_pos rfl,larger_budget]
        exact exclusive_large_optimal ξ hξ hξ1 X.1 hX _ _ _ hu.2 s
      · have hj':j=otherProposer (larger c X):=eq_other_of_ne j _ hj
        have ho:otherProposer j=larger c X := by rw [hj',otherProposer_other]
        have hrec:receipt ξ hξ hξ1 c plan j X=fun i=>entryBid (X.1 i)*
            (1-ξ*(if i∈candidate plan X then 1 else
              EqualCapacity.positiveMarginal ξ (commonBudget c X)
                (listBids (remainder X.1 (candidate plan X))) i)) := by
          funext i
          rw [receipt,acceptance_weighted ξ hξ hξ1 c plan _ X he hu,ho]
          simp only [true_and]
        rw [hrec,select,if_neg he,if_pos hu,balanced,if_neg hj,hj',other_larger_budget]
        exact exclusive_small_optimal ξ hξ hξ1 X.1 hX _ _ _ hu.2 s
    · have hp:=Hybrid.NativeContinuation.pure_numerical_optimal hξ1 X.1 hX
        (budget c 0 X) (budget c 1 X)
      have hrec:receipt ξ hξ hξ1 c plan j X=fun i=>entryBid (X.1 i)*
          (1-ξ*(if i∈(if j=0 then (purePair ξ c X).2 else (purePair ξ c X).1) then 1 else 0)) := by
        funext i
        rw [receipt,acceptance_pure ξ hξ hξ1 c plan _ X he hu]
        fin_cases j <;> simp [otherProposer]
      rw [hrec,select,if_neg he,if_neg hu]
      fin_cases j
      · simpa [purePair] using hp.1
      · simpa [purePair] using hp.2

omit [Nonempty (Fin m)] in

lemma optimal_uncap_present (L : LocalList m) (r : Fin m→ℝ) (C : ℕ)
    (S : Finset (Fin m)) (hzero:∀i,L i=none→ r i=0)
    (hopt:Finite.Optimal (min C (presentSet L).card) r S) : Finite.Optimal C r S := by
  refine ⟨hopt.1.trans (min_le_left _ _),?_⟩
  intro T hT
  have hcap:(T.filter (fun i=>L i≠none)).card≤ min C (presentSet L).card := by
    apply le_min ((Finset.card_filter_le _ _).trans hT)
    apply Finset.card_le_card
    intro i hi
    simp only [presentSet,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (Finset.mem_filter.mp hi).2
  have hh:=hopt.2 _ hcap
  have he:(∑i∈T.filter (fun i=>L i≠none),r i)=∑i∈T,r i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:L i=none
    · simp [hi,hzero i hi]
    · simp [hi]
  rwa [he] at hh

 theorem select_optimal (j : Fin 2) (X : ClassifiedContext m)
    (hX:NonnegativeList X.1) (s : unitInterval) :
    Finite.Optimal (c-contextUpper j X) (receipt ξ hξ hξ1 c plan j X)
      (select ξ hξ hξ1 c plan j X s) := by
  apply optimal_uncap_present X.1 _ _ _
  · intro i hi
    simp only [receipt,hi,entryBid,zero_mul]
  · exact select_capped_optimal ξ hξ hξ1 c plan j X hX s

theorem native_proposer_optimal (Γ : FiniteGame m 2 c unitInterval)
    {R η : ℝ} (hR:0< R) (hη0:0≤η) (hη1:η<1)
    (hξeq:ξ=(1-η)/2) (hA:Γ.A=Schedule.affine 2 η hη0 hη1.le)
    (hseed:Γ.seedLaw=volume)
    (hfull:∀ᵐd∂userProfileLaw Γ,d∈classifiedProfiles m R) :
    let C:=contextPolicy ξ hξ hξ1 c plan hplan
    let G:=C.nativeGame Γ R
    let B:=classifiedPosterior G (R:=R) hfull
    ∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal c (beliefReceipts G.A (posteriorCountBelief G B j L) L)
        (G.policy j L s).val := by
  let C:=contextPolicy ξ hξ hξ1 c plan hplan
  apply ContextPolicy.nativeGame_proposer_optimal C Γ hR le_rfl hη0 hη1.le hA hfull
  intro j L hL s
  have hX:NonnegativeList (observedContext R j L).1 := by
    intro i
    change 0≤ entryBid (broadcastPart R L i)
    unfold broadcastPart StrictTags.lowList
    split_ifs
    · exact ((feasibleObservedList_iff_nonnegative j L).mp hL) i
    · exact le_rfl
  have hh:=select_optimal ξ hξ hξ1 c plan j (observedContext R j L) hX s
  have hrec:lowerContextReceipt (C.nativeGame Γ R) C ((1-η)/2) j (observedContext R j L)=
      receipt ξ hξ hξ1 c plan j (observedContext R j L) := by
    funext i
    simp only [lowerContextReceipt,contextAcceptance,ContextPolicy.nativeGame,hseed,
      C,contextPolicy,receipt,acceptance,hξeq]
  rw [hrec]
  simpa only [contextUpper_observed,C,contextPolicy] using hh

end FCAppendix.Affine.Uniform07Finishing.Weighted
