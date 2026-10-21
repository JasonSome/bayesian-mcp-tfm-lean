import FCAppendix.Affine.UniformFinite.Late.StrictClassification
import FCAppendix.Affine.UniformFinite.Late.NativeExceptional

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.Strict
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical
open Hybrid
open Uniform05
open scoped BigOperators

variable {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def selection (C : ContextPolicy M c Seed) (R : ℝ) (j : Fin 2)
    (L : LocalList M) (s : Seed) : Finset (Fin M) :=
  if localCount R L 2≤ c then upperSet R L ∪ C.select j (observedContext R j L) s
  else HighestBid.selection (upperPart R L) c

theorem lower_card (C : ContextPolicy M c Seed) (R : ℝ) (j : Fin 2)
    (L : LocalList M) (s : Seed) :
    (C.select j (observedContext R j L) s).card≤ c-localCount R L 2 := by
  simpa only [contextUpper_observed] using (C.feasible j (observedContext R j L) s).1

theorem lower_present (C : ContextPolicy M c Seed) (R : ℝ) (j : Fin 2)
    (L : LocalList M) (s : Seed) (a : Fin M)
    (ha : a∈C.select j (observedContext R j L) s) :
    L a≠none ∧ a∉upperSet R L :=
  lowerPart_present R L a ((C.feasible j (observedContext R j L) s).2 a ha)

theorem selection_feasible (C : ContextPolicy M c Seed) (R : ℝ) (j : Fin 2)
    (L : LocalList M) (s : Seed) : LocallyFeasible L c (selection C R j L s) := by
  unfold selection
  split_ifs with hcap
  · constructor
    · apply (Finset.card_union_le _ _).trans
      rw [upperSet_card]
      have hl := lower_card C R j L s
      omega
    · intro a ha
      rcases Finset.mem_union.mp ha with h | h
      · exact upperSet_present R L a h
      · exact (lower_present C R j L s a h).1
  · obtain ⟨hc,hs⟩ := (HighestBid.selection_best (upperPart R L) c).1
    exact ⟨hc,fun a ha => upperSet_present R L a
      ((upperPart_present_iff R L a).mp (hs a ha))⟩

theorem measurable_selection (C : ContextPolicy M c Seed) (R : ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (selection C R j)) := by
  have hc : Measurable (fun x : LocalList M×Seed =>
      C.select j (observedContext R j x.1) x.2) :=
    (C.measurable j).comp (((measurable_observedContext R j).comp measurable_fst).prodMk measurable_snd)
  have hu : Measurable (fun x : LocalList M×Seed =>
      upperSet R x.1 ∪ C.select j (observedContext R j x.1) x.2) :=
    (measurable_of_countable (fun p : Finset (Fin M)×Finset (Fin M) => p.1∪p.2)).comp
      (((measurable_upperSet R).comp measurable_fst).prodMk hc)
  exact Measurable.ite
    (measurableSet_le ((measurable_localCount R 2).comp measurable_fst) measurable_const)
    hu ((HighestBid.measurable_selection M c).comp ((measurable_upperPart R).comp measurable_fst))

def localPolicy (C : ContextPolicy M c Seed) (R : ℝ) (j : Fin 2) : LocalPolicy M c Seed :=
  fun L s => ⟨selection C R j L s,selection_feasible C R j L s⟩

def nativeGame (C : ContextPolicy M c Seed) (Γ : FiniteGame M 2 c Seed) (R : ℝ) :
    FiniteGame M 2 c Seed :=
  {Γ with policy:=localPolicy C R,policy_measurable:=measurable_selection C R}

theorem nativeGame_fields (C : ContextPolicy M c Seed) (Γ : FiniteGame M 2 c Seed) (R : ℝ) :
    (nativeGame C Γ R).F=Γ.F ∧ (nativeGame C Γ R).σ=Γ.σ ∧
    (nativeGame C Γ R).seedLaw=Γ.seedLaw ∧ (nativeGame C Γ R).A=Γ.A := ⟨rfl,rfl,rfl,rfl⟩

def Factors (Γ : FiniteGame M 2 c Seed) (R : ℝ)
    (C : Fin 2 → ClassifiedContext M → Seed → Finset (Fin M)) : Prop :=
  ∀j L s a,lowerPart R L a≠none →
    (a∈(Γ.policy j L s).val ↔ a∈C j (observedContext R j L) s)

theorem factors (C : ContextPolicy M c Seed) (R : ℝ) (j : Fin 2)
    (L : LocalList M) (s : Seed) (a : Fin M) (ha : lowerPart R L a≠none) :
    a∈selection C R j L s ↔ a∈C.select j (observedContext R j L) s := by
  have hn := (lowerPart_present R L a ha).2
  unfold selection
  split_ifs with hcap
  · simp only [Finset.mem_union,hn,false_or]
  · have hz : C.select j (observedContext R j L) s=∅ := by
      apply Finset.card_eq_zero.mp
      have hc := lower_card C R j L s
      omega
    rw [hz]
    simp only [Finset.notMem_empty,iff_false]
    intro hsel
    have hp := (HighestBid.selection_best (upperPart R L) c).1.2 a hsel
    exact hn ((upperPart_present_iff R L a).mp hp)

theorem nativeGame_factors (C : ContextPolicy M c Seed) (Γ : FiniteGame M 2 c Seed)
    (R : ℝ) : Factors (nativeGame C Γ R) R C.select := factors C R

theorem posterior_lower_mean (Γ : FiniteGame M 2 c Seed) {U R : ℝ}
    (hU : 0≤ U) (hUR : U< R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R)
    (C : Fin 2 → ClassifiedContext M → Seed → Finset (Fin M))
    (hC : ∀j,Measurable (Function.uncurry (C j))) (hfactor : Factors Γ R C)
    (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L)
    (a : Fin M) (b : ℝ) (ha : L a=some b) (hb : b< R) :
    posteriorOtherMean Γ (posterior Γ hfull) j L a=
      contextAcceptance Γ C (otherProposer j) (observedContext R j L) a := by
  rw [posteriorOtherMean_eq_profile_integral]
  have hstat : ∀ᵐd ∂(posterior Γ hfull).posterior j L,
      (∫s : Fin 2→ Seed,((otherInclusionCount Γ j a (d,s)).val:ℝ)
          ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw))=
        contextAcceptance Γ C (otherProposer j) (observedContext R j L) a := by
    filter_upwards [posterior_support Γ hU hUR hfull j L hL] with d hd
    have hctx : observedContext R (otherProposer j)
        (observe (drawsRealization d) (otherProposer j))=observedContext R j L := by
      rw [observedContext_eq_actual d hd.2,← observedContext_eq_actual d hd.2 j,hd.1]
    have hlow : lowerPart R (observe (drawsRealization d) (otherProposer j)) a≠none := by
      rw [lowerPart_common d hd.2 (otherProposer j) j,hd.1,lowerPart_some L a ha hb]
      exact Option.some_ne_none b
    have heq (s : Fin 2→ Seed) : ((otherInclusionCount Γ j a (d,s)).val:ℝ)=
        if a∈C (otherProposer j) (observedContext R j L) (s (otherProposer j)) then 1 else 0 := by
      rw [otherInclusionCount_two]
      have hf := hfactor (otherProposer j) (observe (drawsRealization d) (otherProposer j))
        (s (otherProposer j)) a hlow
      rw [hctx] at hf
      simp only [allocation,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      simp only [hf]
    rw [integral_congr_ae (Eventually.of_forall heq)]
    let f : Seed→ℝ := fun s => if a∈C (otherProposer j) (observedContext R j L) s then 1 else 0
    have hm : Measurable f := Measurable.ite
      (((hC (otherProposer j)).comp (measurable_const.prodMk measurable_id))
        (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin M) | a∈S}))
      measurable_const measurable_const
    have hp := measurePreserving_eval (fun _ : Fin 2 => Γ.seedLaw) (otherProposer j)
    change (∫s : Fin 2→ Seed,f (s (otherProposer j)) ∂Measure.pi (fun _ => Γ.seedLaw))=
      ∫s,f s ∂Γ.seedLaw
    calc
      _ = ∫s,f s ∂(Measure.pi (fun _ : Fin 2 => Γ.seedLaw)).map
          (fun s => s (otherProposer j)) :=
        (integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable).symm
      _ = _ := by rw [hp.map_eq]
  calc
    _ = ∫_d,contextAcceptance Γ C (otherProposer j) (observedContext R j L) a
        ∂(posterior Γ hfull).posterior j L := integral_congr_ae hstat
    _ = _ := by simp

theorem posterior_upper_mean (Γ : FiniteGame M 2 c Seed) {U R : ℝ}
    (hU : 0≤ U) (hUR : U< R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R)
    (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L)
    (a : Fin M) (b : ℝ) (ha : L a=some b) (hb : R≤ b) :
    posteriorOtherMean Γ (posterior Γ hfull) j L a=0 := by
  rw [posteriorOtherMean_eq_profile_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [posterior_support Γ hU hUR hfull j L hL] with d hd
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro s
  have hobs : observe (drawsRealization d) j a=some b := by rw [hd.1,ha]
  have hnone := upper_other_absent d hd.2 j a hobs hb
  have hnot : a∉allocation (drawsRealization d) Γ.policy s (otherProposer j) := by
    intro hin
    exact ((Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j))
      (s (otherProposer j))).property.2 a hin) hnone
  change ((otherInclusionCount Γ j a (d,s)).val:ℝ)=0
  rw [otherInclusionCount_two,if_neg hnot]
  norm_num

theorem posterior_lower_receipt (Γ : FiniteGame M 2 c Seed) {U R : ℝ}
    (hU : 0≤ U) (hUR : U< R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R)
    (η : ℝ) (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (C : Fin 2 → ClassifiedContext M → Seed → Finset (Fin M))
    (hC : ∀j,Measurable (Function.uncurry (C j))) (hfactor : Factors Γ R C)
    (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L)
    (a : Fin M) (b : ℝ) (ha : L a=some b) (hb : b< R) :
    Finite.conditionalReceipt Γ.A (posteriorCountBelief Γ (posterior Γ hfull) j L a) b=
      b*(1-(1-η)/2*contextAcceptance Γ C (otherProposer j) (observedContext R j L) a) := by
  rw [posterior_affine_receipt Γ _ η hη0 hη1 hA,
    posterior_lower_mean Γ hU hUR hfull C hC hfactor j L hL a b ha hb]

theorem posterior_upper_receipt (Γ : FiniteGame M 2 c Seed) {U R : ℝ}
    (hU : 0≤ U) (hUR : U< R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R)
    (η : ℝ) (hη0 : 0≤η) (hη1 : η≤1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L)
    (a : Fin M) (b : ℝ) (ha : L a=some b) (hb : R≤ b) :
    Finite.conditionalReceipt Γ.A (posteriorCountBelief Γ (posterior Γ hfull) j L a) b=b := by
  rw [posterior_affine_receipt Γ _ η hη0 hη1 hA,
    posterior_upper_mean Γ hU hUR hfull j L hL a b ha hb]
  ring

section Optimality
variable (C : ContextPolicy M c Seed) (Γ : FiniteGame M 2 c Seed) {U R η : ℝ}
  (hU : 0≤ U) (hUR : U< R) (hη0 : 0≤η) (hη1 : η≤1)
  (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
  (hfull : ∀ᵐd ∂userProfileLaw (nativeGame C Γ R),d∈strongProfiles M U R)
local notation "Gamma" => nativeGame C Γ R
local notation "Belief" => posterior Gamma hfull
include hU hUR hη0 hη1 hA

theorem native_receipt_vector (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L)
    (a : Fin M) :
    beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L a=
      if a∈upperSet R L then entryBid (L a) else
        lowerContextReceipt Gamma C ((1-η)/2) j (observedContext R j L) a := by
  have hA' : (Gamma).A=Schedule.affine 2 η hη0 hη1 := hA
  cases he : L a with
  | none =>
    have hn : a∉upperSet R L := fun h => upperSet_present R L a h he
    simp [beliefReceipts,he,hn,lowerContextReceipt,observedContext,lowerPart,tag,entryBid]
  | some b =>
    by_cases hb : b< R
    · have hn : a∉upperSet R L := by
        simpa only [upperSet_iff_bid L a he] using not_le.mpr hb
      have hl := posterior_lower_receipt Gamma hU hUR hfull η hη0 hη1 hA'
        C.select C.measurable (nativeGame_factors C Γ R) j L hL a b he hb
      simp only [beliefReceipts,he,if_neg hn]
      rw [hl]
      simp only [lowerContextReceipt,observedContext,lowerPart_some L a he hb,entryBid]
    · have hb' : R≤ b := le_of_not_gt hb
      have hh : a∈upperSet R L := (upperSet_iff_bid L a he).mpr hb'
      simp only [beliefReceipts,he,if_pos hh,entryBid]
      exact posterior_upper_receipt Gamma hU hUR hfull η hη0 hη1 hA' j L hL a b he hb'

theorem native_lower_vector (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L) :
    lowerContextReceipt Gamma C ((1-η)/2) j (observedContext R j L)=
      fun a => if a∈upperSet R L then 0 else
        beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L a := by
  funext a
  by_cases ha : a∈upperSet R L
  · simp only [if_pos ha,lowerContextReceipt,observedContext,
      lowerPart_upper R L a ha,entryBid,zero_mul]
  · rw [if_neg ha,native_receipt_vector C Γ hU hUR hη0 hη1 hA hfull j L hL a,if_neg ha]

theorem native_upper_priority (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L) :
    ∀a∈upperSet R L,∀l∉upperSet R L,
      beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L l≤
        beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L a := by
  intro a ha l hl
  have hb := (beliefReceipts_nonneg_le Gamma Belief j L
    ((feasibleObservedList_iff_nonnegative j L).mp hL) l).2
  rw [native_receipt_vector C Γ hU hUR hη0 hη1 hA hfull j L hL a,if_pos ha]
  exact hb.trans ((nonupper_entry_le (hU.trans hUR.le) L l hl).trans (upperSet_entry_ge L a ha))

theorem nativeGame_proposer_optimal
    (hlower : ∀j L,FeasibleObservedList j L → ∀s,
      Finite.Optimal (c-localCount R L 2)
        (lowerContextReceipt Gamma C ((1-η)/2) j (observedContext R j L))
        (C.select j (observedContext R j L) s)) :
    ∀j L,FeasibleObservedList j L → ∀s,
      Finite.Optimal c (beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L)
        ((Gamma).policy j L s).val := by
  intro j L hL s
  let r := beliefReceipts (Gamma).A (posteriorCountBelief Gamma Belief j L) L
  let H := upperSet R L
  let S := C.select j (observedContext R j L) s
  have hr0 (a : Fin M) : 0≤ r a :=
    (beliefReceipts_nonneg_le Gamma Belief j L
      ((feasibleObservedList_iff_nonnegative j L).mp hL) a).1
  have hpriority : ∀a∈H,∀l∉H,r l≤ r a :=
    native_upper_priority C Γ hU hUR hη0 hη1 hA hfull j L hL
  change Finite.Optimal c r (selection C R j L s)
  unfold selection
  split_ifs with hcap
  · have hH : H.card≤ c := by simpa only [H,upperSet_card] using hcap
    have hd : Disjoint H S := Finset.disjoint_left.mpr
      (fun a ha hs => (lower_present C R j L s a hs).2 ha)
    apply priority_union_optimal c r H S hH hd hr0 hpriority
    have hopt := hlower j L hL s
    rw [native_lower_vector C Γ hU hUR hη0 hη1 hA hfull j L hL] at hopt
    simpa only [H,S,r,upperSet_card] using hopt
  · let T := HighestBid.selection (upperPart R L) c
    have hsub : T⊆H := by
      intro a ha
      exact (upperPart_present_iff R L a).mp
        ((HighestBid.selection_best (upperPart R L) c).1.2 a ha)
    have htop := HighestBid.selection_optimal (upperPart R L) c
    change Finite.Optimal c (fun a => entryBid (upperPart R L a)) T at htop
    have heq : (fun a => entryBid (upperPart R L a))=
        (fun a => if a∈H then r a else 0) := by
      funext a
      by_cases ha : a∈H
      · have ht := (Finset.mem_filter.mp ha).2
        rw [if_pos ha]
        change entryBid (upperPart R L a)=_
        simp only [upperPart,if_pos ht]
        dsimp only [r]
        rw [native_receipt_vector C Γ hU hUR hη0 hη1 hA hfull j L hL a,if_pos ha]
      · have ht : tag R (L a)≠2 := by
          simpa only [H,upperSet,Finset.mem_filter,Finset.mem_univ,true_and] using ha
        simp only [upperPart,if_neg ht,if_neg ha,entryBid]
    rw [heq] at htop
    have hcard : T.card=c := by
      apply le_antisymm htop.1
      by_contra h
      have ht : T.card< H.card := by
        have hH : c< H.card := by simpa only [H,upperSet_card] using lt_of_not_ge hcap
        omega
      obtain ⟨a,haH,haT⟩ := Finset.exists_mem_notMem_of_card_lt_card ht
      have hra : 0<(if a∈H then r a else 0) := by
        rw [if_pos haH]
        dsimp only [r]
        rw [native_receipt_vector C Γ hU hUR hη0 hη1 hA hfull j L hL a,if_pos haH]
        exact (hU.trans_lt hUR).trans_le (upperSet_entry_ge L a haH)
      have hh := Finite.optimal_fills c _ T htop a haT hra
      omega
    exact priority_full_optimal c r H T hsub hcard hr0 hpriority htop

end Optimality

section Constructed
variable [NeZero M]

def constructedGame (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) (R : ℝ) :
    FiniteGame M 2 (Uniform07.capacity M) unitInterval :=
  nativeGame (NativeExceptional.contextPolicy i G μseed) Γ R

theorem constructed_proposer_optimal (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) (hseed : Γ.seedLaw=volume)
    {R : ℝ} (hR : cap i< R)
    (hA : Γ.A=Schedule.affine 2 (eta i) (eta_range i).1.le (eta_range i).2.le)
    (hfull : ∀ᵐd ∂userProfileLaw (constructedGame i G μseed Γ R),
      d∈strongProfiles M (cap i) R) :
    ∀j L,FeasibleObservedList j L → ∀s,
      Finite.Optimal (Uniform07.capacity M)
        (beliefReceipts (constructedGame i G μseed Γ R).A
          (posteriorCountBelief (constructedGame i G μseed Γ R)
            (posterior (constructedGame i G μseed Γ R) hfull) j L) L)
        ((constructedGame i G μseed Γ R).policy j L s).val := by
  apply nativeGame_proposer_optimal (NativeExceptional.contextPolicy i G μseed) Γ
    (cap_pos i).le hR (eta_range i).1.le (eta_range i).2.le hA hfull
  intro j L hL s
  have hn := lowerPart_nonnegative R L ((feasibleObservedList_iff_nonnegative j L).mp hL)
  have hopt := NativeExceptional.context_optimal i G μseed
    (constructedGame i G μseed Γ R) hseed
    (observedContext R j L) (observed_valid R j L) hn j s
  simp only [contextUpper_observed,xi] at hopt
  convert! hopt using 1

theorem constructed_selection_on_path (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    {R : ℝ} (hR : cap i< R) (j : Fin 2) (L : LocalList M)
    (hL : OriginalList (cap i) R L) (s : unitInterval) :
    selection (NativeExceptional.contextPolicy i G μseed) R j L s=
      (NativeContext.contextPolicy i G μseed).selection (cap i) j L s := by
  have hO : NativeExceptional.Ordinary i (Hybrid.observedContext (cap i) j L) := by
    intro a
    change entryBid (Hybrid.broadcastPart (cap i) L a)≤ cap i
    cases he : L a with
    | none => simp [Hybrid.broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,he,entryBid,(cap_pos i).le]
    | some b =>
      by_cases hb : b≤ cap i
      · simp [Hybrid.broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,he,hb,entryBid]
      · simp [Hybrid.broadcastPart,TaggedLocal.lowList,TaggedLocal.tag,he,hb,entryBid,(cap_pos i).le]
  unfold selection Hybrid.ContextPolicy.selection
  rw [localCount_eq_original hR L hL 2,upperSet_eq_original hR L hL,
    upperPart_eq_original hR L hL,observedContext_eq_original hR j L hL]
  by_cases hc : TaggedLocal.localCount (cap i) (cap i) L 2≤ Uniform07.capacity M
  · simp only [if_pos hc,NativeExceptional.contextPolicy,NativeContext.contextPolicy]
    rw [NativeExceptional.select_on_path i G μseed _ hO j s]
  · simp only [if_neg hc]

end Constructed
end FCAppendix.Affine.UniformFinite.Late.Strict
