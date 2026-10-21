import FCAppendix.Affine.Uniform07Finishing.Native.WeightedContinuation

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open StrictNative
variable {m : ℕ} [Nonempty (Fin m)]
  (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
  (plan : ClassifiedContext m→ Option (Finset (Fin m))) (hplan:Measurable plan)
  (bad : ClassifiedContext m→ Prop) [DecidablePred bad] (hbad:MeasurableSet {X | bad X})

def completedSelect (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) : Finset (Fin m) :=
  if bad X then (if j=0 then (purePair ξ c X).1 else (purePair ξ c X).2)
  else select ξ hξ hξ1 c plan j X s

include hplan hbad in
lemma measurable_completedSelect (j : Fin 2) :
    Measurable (Function.uncurry (completedSelect ξ hξ hξ1 c plan bad j)) := by
  have hp : Measurable (purePair (m:=m) ξ c) :=
    ResidualPotential.measurable_selection measurable_const measurable_fst
      (measurable_budget c 0) (measurable_budget c 1)
  apply Measurable.ite (hbad.preimage measurable_fst) _
    (measurable_select ξ hξ hξ1 c plan hplan j)
  by_cases hj:j=0
  · simpa only [hj,if_true,Function.comp_def] using hp.fst.comp measurable_fst
  · simpa only [hj,if_false,Function.comp_def] using hp.snd.comp measurable_fst

lemma completedSelect_feasible (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) :
    LocallyFeasible X.1 (c-contextUpper j X) (completedSelect ξ hξ hξ1 c plan bad j X s) := by
  by_cases hb:bad X
  · rw [completedSelect,if_pos hb]
    have hp:=ResidualPotential.selection_feasible (1-ξ) (by linarith : 0≤ 1-ξ)
      X.1 (budget c 0 X) (budget c 1 X)
    fin_cases j
    · change LocallyFeasible X.1 (c-contextUpper 0 X) (purePair ξ c X).1
      exact ⟨hp.1.1.trans (min_le_left _ _),hp.1.2⟩
    · change LocallyFeasible X.1 (c-contextUpper 1 X) (purePair ξ c X).2
      exact ⟨hp.2.1.trans (min_le_left _ _),hp.2.2⟩
  · rw [completedSelect,if_neg hb]
    exact select_feasible ξ hξ hξ1 c plan j X s

def completedContextPolicy : ContextPolicy m c unitInterval where
  select:=completedSelect ξ hξ hξ1 c plan bad
  measurable:=measurable_completedSelect ξ hξ hξ1 c plan hplan bad hbad
  feasible:=completedSelect_feasible ξ hξ hξ1 c plan bad

lemma completed_acceptance (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) :
    (∫s : unitInterval,if i∈completedSelect ξ hξ hξ1 c plan bad j X s then (1:ℝ) else 0)=
      if bad X then (if i∈(if j=0 then (purePair ξ c X).1 else (purePair ξ c X).2) then 1 else 0)
      else acceptance ξ hξ hξ1 c plan j X i := by
  by_cases hb:bad X
  · simp only [completedSelect,if_pos hb,integral_const,probReal_univ,smul_eq_mul,one_mul]
  · simp only [completedSelect,if_neg hb,acceptance]

 theorem completed_numerical_optimal (j : Fin 2) (X : ClassifiedContext m)
    (hX:NonnegativeList X.1) (s : unitInterval) :
    Finite.Optimal (c-contextUpper j X)
      (fun i=>entryBid (X.1 i)*(1-ξ*(∫u : unitInterval,
        if i∈completedSelect ξ hξ hξ1 c plan bad (otherProposer j) X u then (1:ℝ) else 0)))
      (completedSelect ξ hξ hξ1 c plan bad j X s) := by
  simp_rw [completed_acceptance ξ hξ hξ1 c plan bad]
  by_cases hb:bad X
  · simp only [if_pos hb,completedSelect]
    apply optimal_uncap_present X.1 _ _ _
    · intro i hi
      simp [hi,entryBid]
    · have hp:=Hybrid.NativeContinuation.pure_numerical_optimal hξ1 X.1 hX
        (budget c 0 X) (budget c 1 X)
      fin_cases j
      · convert! hp.1 using 1
      · convert! hp.2 using 1
  · simp only [if_neg hb,completedSelect]
    exact select_optimal ξ hξ hξ1 c plan j X hX s

set_option maxHeartbeats 600000 in

theorem completed_native_proposer_optimal (Γ : FiniteGame m 2 c unitInterval)
    {R η : ℝ} (hR:0< R) (hη0:0≤η) (hη1:η<1)
    (hξeq:ξ=(1-η)/2) (hA:Γ.A=Schedule.affine 2 η hη0 hη1.le)
    (hseed:Γ.seedLaw=volume)
    (hfull:∀ᵐd∂userProfileLaw Γ,d∈classifiedProfiles m R) :
    let C : ContextPolicy m c unitInterval := completedContextPolicy (m:=m) ξ hξ hξ1 c plan hplan bad hbad
    let G:=C.nativeGame Γ R
    let B:=classifiedPosterior (m:=m) (c:=c) G (R:=R) hfull
    ∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal c (beliefReceipts G.A (posteriorCountBelief G B j L) L)
        (G.policy j L s).val := by
  let C : ContextPolicy m c unitInterval := completedContextPolicy (m:=m) ξ hξ hξ1 c plan hplan bad hbad
  apply ContextPolicy.nativeGame_proposer_optimal C Γ hR le_rfl hη0 hη1.le hA hfull
  intro j L hL s
  have hX:NonnegativeList (observedContext R j L).1 := by
    intro i
    change 0≤ entryBid (broadcastPart R L i)
    unfold broadcastPart StrictTags.lowList
    split_ifs
    · exact ((feasibleObservedList_iff_nonnegative j L).mp hL) i
    · exact le_rfl
  change Finite.Optimal (c-StrictTags.localCount R R L 2)
    (fun i => entryBid ((observedContext R j L).1 i)*
      (1-((1-η)/2)*(∫ u : unitInterval,
        if i∈C.select (otherProposer j) (observedContext R j L) u then (1:ℝ) else 0 ∂Γ.seedLaw)))
    (C.select j (observedContext R j L) s)
  rw [hseed,←hξeq,←contextUpper_observed R j L]
  exact completed_numerical_optimal ξ hξ hξ1 c plan bad j (observedContext R j L) hX s

end FCAppendix.Affine.Uniform07Finishing.Weighted
