import FCAppendix.Affine.Hybrid.Native02.ClosedClassifier
import FCAppendix.Affine.Hybrid.NativeContinuation
import FCAppendix.Affine.Hybrid.UpperNativeRoutes

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical
open scoped BigOperators

def ClosedContextFactors {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (C : Fin 2 → ClassifiedContext m → Seed → Finset (Fin m)) : Prop :=
  ∀ j L s i, lowerPart R L i ≠ none →
    (i ∈ (Γ.policy j L s).val ↔ i ∈ C j (observedClosedContext R j L) s)

theorem closedUpperPosterior_lower_mean {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈ closedProfiles m R)
    (C : Fin 2 → ClassifiedContext m → Seed → Finset (Fin m))
    (hC : ∀ j,Measurable (Function.uncurry (C j))) (hfactor : ClosedContextFactors Γ R C)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : b<R) :
    posteriorOtherMean Γ (closedUpperPosterior Γ R hfull) j L i=
      contextAcceptance Γ C (otherProposer j) (observedClosedContext R j L) i := by
  classical
  rw [posteriorOtherMean_eq_profile_integral]
  have hstat : ∀ᵐd ∂(closedUpperPosterior Γ R hfull).posterior j L,
      (∫s : Fin 2 → Seed,((otherInclusionCount Γ j i (d,s)).val:ℝ)
          ∂Measure.pi (fun _ : Fin 2=>Γ.seedLaw))=
        contextAcceptance Γ C (otherProposer j) (observedClosedContext R j L) i := by
    filter_upwards [closedUpperPosterior_support Γ R hfull j L hL] with d hd
    have hctx : observedClosedContext R (otherProposer j) (observe (drawsRealization d) (otherProposer j))=
        observedClosedContext R j L := by
      rw [observedClosedContext_eq_actual d hd.2,←observedClosedContext_eq_actual d hd.2 j,hd.1]
    have hlow : lowerPart R (observe (drawsRealization d) (otherProposer j)) i≠none := by
      rw [lowerPart_common d hd.2 (otherProposer j) j,hd.1,lowerPart_some L i hi hb]
      exact Option.some_ne_none b
    have heq (s : Fin 2 → Seed) : ((otherInclusionCount Γ j i (d,s)).val : ℝ)=
        if i∈ C (otherProposer j) (observedClosedContext R j L) (s (otherProposer j)) then 1 else 0 := by
      rw [otherInclusionCount_two]
      have hf := hfactor (otherProposer j) (observe (drawsRealization d) (otherProposer j))
        (s (otherProposer j)) i hlow
      rw [hctx] at hf
      simp only [allocation,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      simp only [hf]
    rw [integral_congr_ae (Eventually.of_forall heq)]
    let f : Seed→ℝ := fun s=>if i∈ C (otherProposer j) (observedClosedContext R j L) s then 1 else 0
    have hm : Measurable f := Measurable.ite
      (((hC (otherProposer j)).comp (measurable_const.prodMk measurable_id))
        (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i∈ S}))
      measurable_const measurable_const
    have hp := measurePreserving_eval (fun _ : Fin 2=>Γ.seedLaw) (otherProposer j)
    change (∫s : Fin 2→ Seed,f (s (otherProposer j)) ∂Measure.pi (fun _=>Γ.seedLaw))=
      ∫s,f s ∂Γ.seedLaw
    calc
      _ = ∫s,f s ∂(Measure.pi (fun _ : Fin 2=>Γ.seedLaw)).map (fun s=>s (otherProposer j)) :=
        (integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable).symm
      _ = _ := by rw [hp.map_eq]
  calc
    _ = ∫_d,contextAcceptance Γ C (otherProposer j) (observedClosedContext R j L) i
        ∂(closedUpperPosterior Γ R hfull).posterior j L := integral_congr_ae hstat
    _ = _ := by simp

lemma closed_upper_other_absent {m : ℕ} {R b : ℝ} (d : UserProfile m 2)
    (hd : d∈ closedProfiles m R) (j : Fin 2) (i : Fin m)
    (hi : observe (drawsRealization d) j i=some b) (hb : R≤ b) :
    observe (drawsRealization d) (otherProposer j) i=none := by
  classical
  have hj : j∈(drawsRealization d).recipients i := by
    by_contra hn
    simp only [observe,if_neg hn] at hi
    cases hi
  have hbid : (d i).1.2.bid=b := by
    change ((drawsRealization d).action i).bid=b
    apply Option.some.inj
    simpa only [observe,if_pos hj] using hi
  have hr : (d i).1.2.routeCount=1 := by
    rcases hd i with hlow | hupp
    · rw [hbid] at hlow
      exact False.elim (not_lt.mpr hb hlow.1)
    · exact hupp.2
  have hc : ((drawsRealization d).recipients i).card=1 := by
    rw [(drawsRealization d).chosen_size]
    exact hr
  obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hc
  have hlj : l=j := by
    rw [hl] at hj
    exact (Finset.mem_singleton.mp hj).symm
  rw [hlj] at hl
  simp only [observe,hl,Finset.mem_singleton,otherProposer_ne,if_false]

theorem closedUpperPosterior_upper_mean {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈ closedProfiles m R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : R≤ b) :
    posteriorOtherMean Γ (closedUpperPosterior Γ R hfull) j L i=0 := by
  classical
  rw [posteriorOtherMean_eq_profile_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [closedUpperPosterior_support Γ R hfull j L hL] with d hd
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro s
  have hobs : observe (drawsRealization d) j i=some b := by rw [hd.1,hi]
  have hnone := closed_upper_other_absent d hd.2 j i hobs hb
  have hnot : i∉allocation (drawsRealization d) Γ.policy s (otherProposer j) := by
    intro hin
    exact ((Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j))
      (s (otherProposer j))).property.2 i hin) hnone
  change ((otherInclusionCount Γ j i (d,s)).val:ℝ)=0
  rw [otherInclusionCount_two,if_neg hnot]
  norm_num

theorem closedUpperPosterior_lower_receipt {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈ closedProfiles m R)
    (η : ℝ) (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (C : Fin 2 → ClassifiedContext m → Seed → Finset (Fin m))
    (hC : ∀ j,Measurable (Function.uncurry (C j))) (hfactor : ClosedContextFactors Γ R C)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : b<R) :
    Finite.conditionalReceipt Γ.A
        (posteriorCountBelief Γ (closedUpperPosterior Γ R hfull) j L i) b=
      b*(1-(1-η)/2*contextAcceptance Γ C (otherProposer j) (observedClosedContext R j L) i) := by
  rw [posterior_affine_receipt Γ _ η hη0 hη1 hA,
    closedUpperPosterior_lower_mean Γ R hfull C hC hfactor j L hL i b hi hb]

theorem closedUpperPosterior_upper_receipt {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈ closedProfiles m R)
    (η : ℝ) (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : R≤ b) :
    Finite.conditionalReceipt Γ.A
      (posteriorCountBelief Γ (closedUpperPosterior Γ R hfull) j L i) b=b := by
  rw [posterior_affine_receipt Γ _ η hη0 hη1 hA,
    closedUpperPosterior_upper_mean Γ R hfull j L hL i b hi hb]
  ring

namespace ClosedPolicy
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (C : ContextPolicy m c Seed)

def selection (R : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed) : Finset (Fin m) :=
  if localCount R L 2≤ c then
    upperSet R L ∪ C.select j (observedClosedContext R j L) s
  else HighestBid.selection (upperPart R L) c

lemma lower_card (R : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed) :
    (C.select j (observedClosedContext R j L) s).card≤ c-localCount R L 2 := by
  simpa only [contextUpper_observedClosed] using (C.feasible j (observedClosedContext R j L) s).1

lemma lower_present (R : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed)
    (i : Fin m) (hi : i∈ C.select j (observedClosedContext R j L) s) :
    L i≠none ∧ i∉upperSet R L :=
  lowerPart_present R L i ((C.feasible j (observedClosedContext R j L) s).2 i hi)

lemma selection_feasible (R : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed) :
    LocallyFeasible L c (selection C R j L s) := by
  classical
  unfold selection
  split_ifs with hcap
  · constructor
    · apply (Finset.card_union_le _ _).trans
      rw [upperSet_card]
      have hlow := lower_card C R j L s
      omega
    · intro i hi
      rcases Finset.mem_union.mp hi with hh | hl
      · exact upperSet_present R L i hh
      · exact (lower_present C R j L s i hl).1
  · obtain ⟨hc,hs⟩ := (HighestBid.selection_best (upperPart R L) c).1
    exact ⟨hc,fun i hi=>upperSet_present R L i
      ((upperPart_present_iff R L i).mp (hs i hi))⟩

lemma measurable_selection (R : ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (selection C R j)) := by
  have hc : Measurable (fun x : LocalList m × Seed=>
      C.select j (observedClosedContext R j x.1) x.2) :=
    (C.measurable j).comp (((measurable_observedClosedContext R j).comp measurable_fst).prodMk measurable_snd)
  have hu : Measurable (fun x : LocalList m × Seed=>
      upperSet R x.1 ∪ C.select j (observedClosedContext R j x.1) x.2) :=
    (measurable_of_countable (fun ST : Finset (Fin m) × Finset (Fin m)=>ST.1∪ST.2)).comp
      (((measurable_upperSet R).comp measurable_fst).prodMk hc)
  exact Measurable.ite
    (measurableSet_le ((measurable_localCount R 2).comp measurable_fst) measurable_const)
    hu ((HighestBid.measurable_selection m c).comp ((measurable_upperPart R).comp measurable_fst))

def localPolicy (R : ℝ) (j : Fin 2) : LocalPolicy m c Seed :=
  fun L s=>⟨selection C R j L s,selection_feasible C R j L s⟩

lemma factors (R : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed)
    (i : Fin m) (hi : lowerPart R L i≠none) :
    i∈ selection C R j L s ↔ i∈ C.select j (observedClosedContext R j L) s := by
  classical
  have hn := (lowerPart_present R L i hi).2
  unfold selection
  split_ifs with hcap
  · simp only [Finset.mem_union,hn,false_or]
  · have hz : C.select j (observedClosedContext R j L) s=∅ := by
      apply Finset.card_eq_zero.mp
      have hc := lower_card C R j L s
      omega
    rw [hz]
    simp only [Finset.notMem_empty,iff_false]
    intro hsel
    have hp := (HighestBid.selection_best (upperPart R L) c).1.2 i hsel
    exact hn ((upperPart_present_iff R L i).mp hp)

def nativeGame (Γ : FiniteGame m 2 c Seed) (R : ℝ) : FiniteGame m 2 c Seed :=
  { Γ with policy:=localPolicy C R,policy_measurable:=measurable_selection C R }

lemma nativeGame_factors (Γ : FiniteGame m 2 c Seed) (R : ℝ) :
    ClosedContextFactors (nativeGame C Γ R) R C.select := factors C R

variable (Γ : FiniteGame m 2 c Seed) {R η : ℝ}
    (hR : 0<R) (hη0 : 0≤η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hfull : ∀ᵐd ∂userProfileLaw (nativeGame C Γ R),d∈ closedProfiles m R)
local notation "Gamma"=>nativeGame C Γ R
local notation "Belief"=>closedUpperPosterior Gamma R hfull
include hR hη0 hη1 hA

omit hR in

lemma native_receipt_vector (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) :
    beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L i=
      if i∈ upperSet R L then entryBid (L i) else
        lowerContextReceipt Gamma C ((1-η)/2) j (observedClosedContext R j L) i := by
  classical
  have ha : (Gamma).A=Schedule.affine 2 η hη0 hη1 := hA
  cases he : L i with
  | none=>
    have hn : i∉upperSet R L := fun h=>upperSet_present R L i h he
    simp [beliefReceipts,he,hn,lowerContextReceipt,observedClosedContext,lowerPart,
      closedTag,entryBid]
  | some b=>
    by_cases hb : b<R
    · have hn : i∉upperSet R L := by simpa only [upperSet_iff_bid L i he] using not_le.mpr hb
      have hl := closedUpperPosterior_lower_receipt Gamma R hfull η hη0 hη1 ha
        C.select C.measurable (nativeGame_factors C Γ R) j L hL i b he hb
      simp only [beliefReceipts,he,if_neg hn]
      rw [hl]
      simp only [lowerContextReceipt,observedClosedContext,lowerPart_some L i he hb,entryBid]
    · have hb' : R≤ b := le_of_not_gt hb
      have hh : i∈ upperSet R L := (upperSet_iff_bid L i he).mpr hb'
      simp only [beliefReceipts,he,if_pos hh,entryBid]
      exact closedUpperPosterior_upper_receipt Gamma R hfull η hη0 hη1 ha
        j L hL i b he hb'

omit hR in
lemma native_lower_vector (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) :
    lowerContextReceipt Gamma C ((1-η)/2) j (observedClosedContext R j L)=
      fun i=>if i∈ upperSet R L then 0 else
        beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L i := by
  classical
  funext i
  by_cases hi : i∈ upperSet R L
  · have ht := (Finset.mem_filter.mp hi).2
    simp only [if_pos hi,lowerContextReceipt,observedClosedContext,lowerPart]
    have hn : closedTag R (L i)≠0 := by rw [ht]; decide
    simp only [if_neg hn,entryBid,zero_mul]
  · rw [if_neg hi,native_receipt_vector C Γ hη0 hη1 hA hfull j L hL i,if_neg hi]

lemma native_upper_priority (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ i∈ upperSet R L,∀ l∉upperSet R L,
      beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L l≤
        beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L i := by
  intro i hi l hl
  have hb := (beliefReceipts_nonneg_le Gamma Belief j L
    ((feasibleObservedList_iff_nonnegative j L).mp hL) l).2
  rw [native_receipt_vector C Γ hη0 hη1 hA hfull j L hL i,if_pos hi]
  exact hb.trans ((nonupper_entry_le hR.le L l hl).trans (upperSet_entry_ge L i hi))

theorem nativeGame_proposer_optimal
    (hlower : ∀ j L,FeasibleObservedList j L → ∀ s,
      Finite.Optimal (c-localCount R L 2)
        (lowerContextReceipt Gamma C ((1-η)/2) j (observedClosedContext R j L))
        (C.select j (observedClosedContext R j L) s)) :
    ∀ j L,FeasibleObservedList j L → ∀ s,
      Finite.Optimal c (beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L)
        ((Gamma).policy j L s).val := by
  classical
  intro j L hL s
  let r := beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L
  let H := upperSet R L
  let S := C.select j (observedClosedContext R j L) s
  have hr0 (i : Fin m) : 0≤ r i :=
    (beliefReceipts_nonneg_le Gamma Belief j L
      ((feasibleObservedList_iff_nonnegative j L).mp hL) i).1
  have hpriority : ∀ i∈ H,∀ l∉H,r l≤ r i :=
    native_upper_priority C Γ hR hη0 hη1 hA hfull j L hL
  change Finite.Optimal c r (selection C R j L s)
  unfold selection
  split_ifs with hcap
  · have hH : H.card≤ c := by simpa only [H,upperSet_card] using hcap
    have hd : Disjoint H S := Finset.disjoint_left.mpr
      (fun i hi hs=>(lower_present C R j L s i hs).2 hi)
    apply priority_union_optimal c r H S hH hd hr0 hpriority
    have hopt := hlower j L hL s
    rw [native_lower_vector C Γ hη0 hη1 hA hfull j L hL] at hopt
    simpa only [H,S,r,upperSet_card] using hopt
  · let T := HighestBid.selection (upperPart R L) c
    have hsub : T⊆H := by
      intro i hi
      exact (upperPart_present_iff R L i).mp
        ((HighestBid.selection_best (upperPart R L) c).1.2 i hi)
    have htop := HighestBid.selection_optimal (upperPart R L) c
    change Finite.Optimal c (fun i=>entryBid (upperPart R L i)) T at htop
    have heq : (fun i=>entryBid (upperPart R L i))=(fun i=>if i∈ H then r i else 0) := by
      funext i
      by_cases hi : i∈ H
      · have ht := (Finset.mem_filter.mp hi).2
        rw [if_pos hi]
        change entryBid (upperPart R L i)=_
        simp only [upperPart,if_pos ht]
        dsimp only [r]
        rw [native_receipt_vector C Γ hη0 hη1 hA hfull j L hL i,if_pos hi]
      · have ht : closedTag R (L i)≠2 := by simpa only [H,upperSet,Finset.mem_filter,
          Finset.mem_univ,true_and] using hi
        simp only [upperPart,if_neg ht,if_neg hi,entryBid]
    rw [heq] at htop
    have hcard : T.card=c := by
      apply le_antisymm htop.1
      by_contra h
      have ht : T.card<H.card := by
        have hH : c<H.card := by simpa only [H,upperSet_card] using lt_of_not_ge hcap
        omega
      obtain ⟨i,hiH,hiT⟩ := Finset.exists_mem_notMem_of_card_lt_card ht
      have hri : 0<(if i∈ H then r i else 0) := by
        rw [if_pos hiH]
        dsimp only [r]
        rw [native_receipt_vector C Γ hη0 hη1 hA hfull j L hL i,if_pos hiH]
        exact hR.trans_le (upperSet_entry_ge L i hiH)
      have hh := Finite.optimal_fills c _ T htop i hiT hri
      omega
    exact priority_full_optimal c r H T hsub hcard hr0 hpriority htop

end ClosedPolicy

def NoGapEntries {m : ℕ} (U R : ℝ) (L : LocalList m) : Prop :=
  ∀ i b, L i = some b → b ≤ U ∨ R ≤ b

lemma closedTag_eq_oldTag_on_gap {m : ℕ} {U R : ℝ} (hUR : U < R)
    (L : LocalList m) (hL : NoGapEntries U R L) (i : Fin m) :
    closedTag R (L i) = TaggedLocal.tag U U (L i) := by
  cases he : L i with
  | none => simp [closedTag, TaggedLocal.tag]
  | some b =>
    rcases hL i b he with hb | hb
    · simp [closedTag, TaggedLocal.tag, hb, hb.trans_lt hUR]
    · have hbU : ¬ b ≤ U := not_le.mpr (hUR.trans_le hb)
      simp [closedTag, TaggedLocal.tag, not_lt.mpr hb, hbU]

lemma upperPart_eq_old_on_gap {m : ℕ} {U R : ℝ} (hUR : U < R)
    (L : LocalList m) (hL : NoGapEntries U R L) :
    upperPart R L = FCAppendix.Affine.Hybrid.upperPart U L := by
  funext i
  simp only [upperPart, FCAppendix.Affine.Hybrid.upperPart,
    closedTag_eq_oldTag_on_gap hUR L hL i]

lemma upperSet_eq_old_on_gap {m : ℕ} {U R : ℝ} (hUR : U < R)
    (L : LocalList m) (hL : NoGapEntries U R L) :
    upperSet R L = FCAppendix.Affine.Hybrid.upperSet U L := by
  ext i
  simp only [upperSet, FCAppendix.Affine.Hybrid.upperSet, Finset.mem_filter,
    Finset.mem_univ, true_and, closedTag_eq_oldTag_on_gap hUR L hL i]

lemma localCount_eq_old_on_gap {m : ℕ} {U R : ℝ} (hUR : U < R)
    (L : LocalList m) (hL : NoGapEntries U R L) (k : Fin 4) :
    localCount R L k = TaggedLocal.localCount U U L k := by
  unfold localCount TaggedLocal.localCount
  apply Finset.sum_congr rfl
  intro i _
  rw [closedTag_eq_oldTag_on_gap hUR L hL i]

lemma lowerPart_eq_old_on_gap {m : ℕ} {U R : ℝ} (hUR : U < R)
    (L : LocalList m) (hL : NoGapEntries U R L) :
    lowerPart R L = broadcastPart U L := by
  funext i
  simp only [lowerPart, broadcastPart, TaggedLocal.lowList,
    closedTag_eq_oldTag_on_gap hUR L hL i]

lemma observedClosedContext_eq_old_on_gap {m : ℕ} {U R : ℝ} (hUR : U < R)
    (j : Fin 2) (L : LocalList m) (hL : NoGapEntries U R L) :
    observedClosedContext R j L = observedContext U j L := by
  simp only [observedClosedContext, observedContext,
    lowerPart_eq_old_on_gap hUR L hL, localCount_eq_old_on_gap hUR L hL]

theorem upper_selection_iff_old {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (C D : ContextPolicy m c Seed) {U R b : ℝ} (hUR : U < R)
    (j : Fin 2) (L : LocalList m) (hL : NoGapEntries U R L)
    (s t : Seed) (i : Fin m) (hi : L i = some b) (hb : R ≤ b) :
    i ∈ ClosedPolicy.selection C R j L s ↔
      i ∈ D.selection U j L t := by
  have hclosed : i ∈ upperSet R L := (upperSet_iff_bid L i hi).mpr hb
  have hold : i ∈ FCAppendix.Affine.Hybrid.upperSet U L :=
    (FCAppendix.Affine.Hybrid.upperSet_iff_bid L i hi).mpr (hUR.trans_le hb)
  unfold ClosedPolicy.selection ContextPolicy.selection
  rw [localCount_eq_old_on_gap hUR L hL 2, upperPart_eq_old_on_gap hUR L hL]
  split_ifs
  · simp only [Finset.mem_union, hclosed, hold, true_or]
  · rfl

lemma noGapEntries_observe {m : ℕ} {U R : ℝ} (x : Realization m 2)
    (hx : ∀ i, (x.action i).bid ≤ U ∨ R ≤ (x.action i).bid) (j : Fin 2) :
    NoGapEntries U R (observe x j) := by
  intro i b hi
  by_cases hj : j ∈ x.recipients i
  · have he : (x.action i).bid = b := by
      apply Option.some.inj
      simpa only [observe, if_pos hj] using hi
    simpa only [he] using hx i
  · simp only [observe, if_neg hj] at hi
    cases hi

theorem upper_inclusionCount_eq_old {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (C D : ContextPolicy m c Seed) {U R : ℝ} (hUR : U < R)
    (x : Realization m 2) (hx : ∀ i, (x.action i).bid ≤ U ∨ R ≤ (x.action i).bid)
    (s t : Fin 2 → Seed) (i : Fin m) (hi : R ≤ (x.action i).bid) :
    inclusionCount x (ClosedPolicy.localPolicy C R) s i =
      inclusionCount x (D.localPolicy U) t i := by
  rw [inclusionCount_eq_sum, inclusionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ x.recipients i
  · have ho : observe x j i = some (x.action i).bid := by simp [observe, hj]
    have hh := upper_selection_iff_old C D hUR j (observe x j)
      (noGapEntries_observe x hx j) (s j) (t j) i ho hi
    change (if i ∈ ClosedPolicy.selection C R j (observe x j) (s j) then 1 else 0) =
      (if i ∈ D.selection U j (observe x j) (t j) then 1 else 0)
    simp only [hh]
  · have hn : observe x j i = none := by simp [observe, hj]
    have hclosed : i ∉ allocation x (ClosedPolicy.localPolicy C R) s j := by
      intro hin
      exact ((ClosedPolicy.localPolicy C R j (observe x j) (s j)).property.2 i hin) hn
    have hold : i ∉ allocation x (D.localPolicy U) t j := by
      intro hin
      exact ((D.localPolicy U j (observe x j) (t j)).property.2 i hin) hn
    simp only [if_neg hclosed, if_neg hold]

def closedFallbackGame {m c : ℕ} (Γ : FiniteGame m 2 c unitInterval)
    (R ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) : FiniteGame m 2 c unitInterval :=
  ClosedPolicy.nativeGame (NativeContinuation.contextPolicy ξ hξ hξ1 c) Γ R

theorem closedFallbackGame_proposer_optimal {m c : ℕ}
    (Γ : FiniteGame m 2 c unitInterval) {R η : ℝ}
    (hR : 0 < R) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1.le)
    (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles m R) :
    let C := NativeContinuation.contextPolicy (m := m) ((1-η)/2)
      (by linarith : 0 < (1-η)/2) (by linarith : (1-η)/2 < 1) c
    let game := ClosedPolicy.nativeGame C Γ R
    let belief := closedUpperPosterior game R hfull
    ∀ j L, FeasibleObservedList j L → ∀ s,
      Finite.Optimal c (beliefReceipts game.A (posteriorCountBelief game belief j L) L)
        (game.policy j L s).val := by
  let hξ : 0 < (1-η)/2 := by linarith
  let hξ1 : (1-η)/2 < 1 := by linarith
  let C := NativeContinuation.contextPolicy (m := m) ((1-η)/2) hξ hξ1 c
  apply ClosedPolicy.nativeGame_proposer_optimal C Γ hR hη0 hη1.le hA hfull
  intro j L hL s
  have hn := nonnegative_observedClosedContext R j L
    ((feasibleObservedList_iff_nonnegative j L).mp hL)
  have hopt := NativeContinuation.contextPolicy_lower_optimal ((1-η)/2) hξ hξ1 c
    (ClosedPolicy.nativeGame C Γ R) hseed j (observedClosedContext R j L) hn s
  simpa only [contextUpper_observedClosed] using hopt

end FCAppendix.Affine.Hybrid.Native02
