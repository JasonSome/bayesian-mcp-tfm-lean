import FCAppendix.Affine.Hybrid.ClassifiedPolicy
import FCAppendix.Finite.ReceiptBoundsAE

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Bayes Game Set Filter
open scoped BigOperators

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def lowerContextReceipt (Γ : FiniteGame m 2 c Seed) (C : ContextPolicy m c Seed)
    (ξ : ℝ) (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  entryBid (X.1 i)*(1-ξ*contextAcceptance Γ C.select (otherProposer j) X i)

lemma upperSet_iff_bid {U b : ℝ} (L : LocalList m) (i : Fin m) (hi : L i=some b) :
    i∈upperSet U L ↔ U<b := by
  simp only [upperSet,Finset.mem_filter,Finset.mem_univ,true_and,hi,TaggedLocal.tag]
  by_cases hb : b≤U
  · simp [hb,not_lt.mpr hb]
  · simp [hb,lt_of_not_ge hb]

lemma upperSet_entry_gt {U : ℝ} (L : LocalList m) (i : Fin m) (hi : i∈upperSet U L) :
    U<entryBid (L i) := by
  cases he : L i with
  | none=>exact False.elim (upperSet_present U L i hi he)
  | some b=>simpa only [he,entryBid] using (upperSet_iff_bid L i he).mp hi

lemma nonupper_entry_le {U : ℝ} (hU : 0≤U) (L : LocalList m) (i : Fin m)
    (hi : i∉upperSet U L) : entryBid (L i)≤U := by
  cases he : L i with
  | none=>simpa only [he,entryBid] using hU
  | some b=>
    have hb : ¬U<b := fun h=>hi ((upperSet_iff_bid L i he).mpr h)
    simpa only [he,entryBid] using le_of_not_gt hb

lemma beliefReceipts_nonneg_le (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) (i : Fin m) :
    0≤beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L i ∧
      beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L i≤entryBid (L i) := by
  cases he : L i with
  | none=>simp [beliefReceipts,he,entryBid]
  | some b=>
    have hb : 0≤b := by simpa only [NonnegativeList,he,entryBid] using hL i
    have hh := Finite.conditionalReceipt_bounds Γ.A (posteriorCountBelief Γ B j L i)
      0 b hb (fun r _ hr=>by simpa only [zero_mul] using Γ.A.nonneg r hr)
    simpa only [beliefReceipts,he,entryBid,zero_mul] using hh

namespace ContextPolicy
variable (C : ContextPolicy m c Seed) (Γ : FiniteGame m 2 c Seed) {U R η : ℝ}
    (hU : 0≤U) (hR : U<R) (hη0 : 0≤η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hfull : ∀ᵐd ∂userProfileLaw (C.nativeGame Γ U),d∈classifiedProfiles m U)
local notation "Gamma"=>C.nativeGame Γ U
local notation "Belief"=>classifiedPosterior Gamma (R:=R) hfull
include hU hR hη0 hη1 hA

lemma native_receipt_vector (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) :
    beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L i=
      if i∈upperSet U L then entryBid (L i) else
        lowerContextReceipt Gamma C ((1-η)/2) j (observedContext U j L) i := by
  classical
  have ha : (Gamma).A=Schedule.affine 2 η hη0 hη1 := hA
  cases he : L i with
  | none=>
    have hn : i∉upperSet U L := fun h=>upperSet_present U L i h he
    simp [beliefReceipts,he,hn,lowerContextReceipt,observedContext,broadcastPart,
      TaggedLocal.lowList,TaggedLocal.tag,entryBid]
  | some b=>
    by_cases hb : b≤U
    · have hn : i∉upperSet U L := by simpa only [upperSet_iff_bid L i he] using not_lt.mpr hb
      have hl := classifiedPosterior_lower_receipt Gamma hU hR hfull η hη0 hη1 ha
        C.select C.measurable (C.nativeGame_factors Γ U) j L hL i b he hb
      simp only [beliefReceipts,he,if_neg hn]
      rw [hl]
      simp only [lowerContextReceipt,observedContext,broadcastPart_some L i he hb,entryBid]
    · have hb' : U<b := lt_of_not_ge hb
      have hh : i∈upperSet U L := (upperSet_iff_bid L i he).mpr hb'
      simp only [beliefReceipts,he,if_pos hh,entryBid]
      exact classifiedPosterior_upper_receipt Gamma hU hR hfull η hη0 hη1 ha
        j L hL i b he hb'

lemma native_lower_vector (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) :
    lowerContextReceipt Gamma C ((1-η)/2) j (observedContext U j L)=
      fun i=>if i∈upperSet U L then 0 else
        beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L i := by
  classical
  funext i
  by_cases hi : i∈upperSet U L
  · have ht := (Finset.mem_filter.mp hi).2
    simp only [if_pos hi,lowerContextReceipt,observedContext,broadcastPart,TaggedLocal.lowList]
    have hn : TaggedLocal.tag U U (L i)≠0 := by rw [ht]; decide
    simp only [if_neg hn,entryBid,zero_mul]
  · rw [if_neg hi,native_receipt_vector C Γ hU hR hη0 hη1 hA hfull j L hL i,if_neg hi]

lemma native_upper_priority (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀i∈upperSet U L,∀l∉upperSet U L,
      beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L l≤
        beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L i := by
  intro i hi l hl
  have hb := (beliefReceipts_nonneg_le Gamma Belief j L
    ((feasibleObservedList_iff_nonnegative j L).mp hL) l).2
  rw [native_receipt_vector C Γ hU hR hη0 hη1 hA hfull j L hL i,if_pos hi]
  exact hb.trans ((nonupper_entry_le hU L l hl).trans (upperSet_entry_gt L i hi).le)

theorem nativeGame_proposer_optimal
    (hlower : ∀j L,FeasibleObservedList j L → ∀s,
      Finite.Optimal (c-TaggedLocal.localCount U U L 2)
        (lowerContextReceipt Gamma C ((1-η)/2) j (observedContext U j L))
        (C.select j (observedContext U j L) s)) :
    ∀j L,FeasibleObservedList j L → ∀s,
      Finite.Optimal c (beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L)
        ((Gamma).policy j L s).val := by
  classical
  intro j L hL s
  let r := beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L
  let H := upperSet U L
  let S := C.select j (observedContext U j L) s
  have hr0 (i : Fin m) : 0≤r i :=
    (beliefReceipts_nonneg_le Gamma Belief j L
      ((feasibleObservedList_iff_nonnegative j L).mp hL) i).1
  have hpriority : ∀i∈H,∀l∉H,r l≤r i :=
    native_upper_priority C Γ hU hR hη0 hη1 hA hfull j L hL
  change Finite.Optimal c r (C.selection U j L s)
  unfold selection
  split_ifs with hcap
  · have hH : H.card≤c := by simpa only [H,upperSet_card] using hcap
    have hd : Disjoint H S := Finset.disjoint_left.mpr
      (fun i hi hs=>(C.lower_present U j L s i hs).2 hi)
    apply priority_union_optimal c r H S hH hd hr0 hpriority
    have hopt := hlower j L hL s
    rw [native_lower_vector C Γ hU hR hη0 hη1 hA hfull j L hL] at hopt
    simpa only [H,S,r,upperSet_card] using hopt
  · let T := HighestBid.selection (upperPart U L) c
    have hsub : T⊆H := by
      intro i hi
      exact (upperPart_present_iff U L i).mp
        ((HighestBid.selection_best (upperPart U L) c).1.2 i hi)
    have htop := HighestBid.selection_optimal (upperPart U L) c
    change Finite.Optimal c (fun i=>entryBid (upperPart U L i)) T at htop
    have heq : (fun i=>entryBid (upperPart U L i))=(fun i=>if i∈H then r i else 0) := by
      funext i
      by_cases hi : i∈H
      · have ht := (Finset.mem_filter.mp hi).2
        rw [if_pos hi]
        change entryBid (upperPart U L i)=_
        simp only [upperPart,if_pos ht]
        dsimp only [r]
        rw [native_receipt_vector C Γ hU hR hη0 hη1 hA hfull j L hL i,if_pos hi]
      · have ht : TaggedLocal.tag U U (L i)≠2 := by simpa only [H,upperSet,Finset.mem_filter,
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
      have hri : 0<(if i∈H then r i else 0) := by
        rw [if_pos hiH]
        dsimp only [r]
        rw [native_receipt_vector C Γ hU hR hη0 hη1 hA hfull j L hL i,if_pos hiH]
        exact hU.trans_lt (upperSet_entry_gt L i hiH)
      have hh := Finite.optimal_fills c _ T htop i hiT hri
      omega
    exact priority_full_optimal c r H T hsub hcard hr0 hpriority htop

end ContextPolicy
end FCAppendix.Affine.Hybrid
