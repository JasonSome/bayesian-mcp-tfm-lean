import FCAppendix.Affine.Uniform07Finishing.Native.LiteralSourceGame
import FCAppendix.Affine.Uniform07Finishing.Native.GuardedSuccessCap
import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessConstants

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing

open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical
open StrictNative ConditionalSuccess
open scoped BigOperators

variable {m : ℕ} [Nonempty (Fin m)]
set_option maxHeartbeats 600000

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def sourceSuccessPlan (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m)
    (R Λ z width ε : ℝ) (PL : ProbabilityMeasure (ℝ × JointAction 2)) :
    ClassifiedContext m → Option (Finset (Fin m)) :=
  Weighted.sourcePlan (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row)
    (Uniform07.cutoff row / 2) (Uniform07.capacity m) (sourceSeedMeasure row m hc R PL)
    (literalSourceAlpha row Λ z width ε)

lemma measurable_sourceSuccessPlan (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m)
    (R Λ z width ε : ℝ) (hΛ : (54/100 : ℝ) * Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) :
    Measurable (sourceSuccessPlan row hc R Λ z width ε PL) :=
  Weighted.measurable_sourcePlan (Uniform07.xi row) Λ (Early.demandRatio row)
    (Early.bidCap row) (Uniform07.cutoff row / 2) (Uniform07.xi_pos row)
    (source_guard_multiplier_positive row hΛ) (Uniform07.capacity m)
    (sourceSeedMeasure row m hc R PL) (literalSourceAlpha row Λ z width ε)
    (measurable_literalSourceAlpha row hΛ z width ε)

def sourceSuccessGood (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m)
    (R Λ z width ε : ℝ) (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (i : Fin m) (a : JointAction 2) : Set (UserProfile m 2) :=
  {d | ∀ τ j, deviationList i a d τ j i = none ∨
    ∃ E : Finset (Fin m),
      sourceSuccessPlan row hc R Λ z width ε PL
        (observedContext R j (deviationList i a d τ j)) = some E ∧ i ∉ E}

omit [Nonempty (Fin m)] in
lemma measurable_deviationList_profile (i : Fin m) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    Measurable (fun d : UserProfile m 2 => deviationList i a d τ j) := by
  have hinput : Measurable (fun d : UserProfile m 2 =>
      ((d, fun _ : Fin 2 => (0 : unitInterval)), τ)) :=
    (measurable_id.prodMk measurable_const).prodMk measurable_const
  convert! (measurable_observe_deviated (Seed := unitInterval) i a j).comp hinput using 1

theorem measurableSet_sourceSuccessGood (row : Uniform07.Row)
    (hc : 1 ≤ Uniform07.capacity m) (R Λ z width ε : ℝ)
    (hΛ : (54/100 : ℝ) * Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) (i : Fin m) (a : JointAction 2) :
    MeasurableSet (sourceSuccessGood row hc R Λ z width ε PL i a) := by
  simp only [sourceSuccessGood, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro τ
  apply MeasurableSet.iInter
  intro j
  have hL := measurable_deviationList_profile i a τ j
  have hp := (measurable_sourceSuccessPlan row hc R Λ z width ε hΛ PL).comp
    ((measurable_observedContext R j).comp hL)
  have hnone : MeasurableSet {d : UserProfile m 2 | deviationList i a d τ j i = none} :=
    measurableSet_eq_fun ((measurable_pi_apply i).comp hL) measurable_const
  have hsome : MeasurableSet {d : UserProfile m 2 | ∃ E : Finset (Fin m),
      sourceSuccessPlan row hc R Λ z width ε PL
        (observedContext R j (deviationList i a d τ j)) = some E ∧ i ∉ E} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro E
    by_cases hi : i ∉ E
    · simpa only [hi, not_false_eq_true, and_true, Function.comp_apply] using measurableSet_eq_fun hp
        (measurable_const (a := some E))
    · simp only [hi, and_false, Set.setOf_false, MeasurableSet.empty]
  simpa only [Set.setOf_or] using hnone.union hsome

omit [Nonempty (Fin m)] in
lemma source_broadcastPart_nonnegative {R : ℝ} (L : LocalList m)
    (hL : NonnegativeList L) : NonnegativeList (broadcastPart R L) := by
  intro k
  unfold broadcastPart StrictTags.lowList
  split_ifs
  · exact hL k
  · exact le_rfl

omit [Nonempty (Fin m)] in
lemma source_broadcastPart_le_floor {R : ℝ} (hR : 0 ≤ R) (L : LocalList m) :
    ∀ k, entryBid (broadcastPart R L k) ≤ R := by
  intro k
  cases hk : L k with
  | none => simpa [broadcastPart, StrictTags.lowList, StrictTags.tag, hk, entryBid] using hR
  | some b =>
    by_cases hb : b < R
    · simpa [broadcastPart, StrictTags.lowList, StrictTags.tag, hk, hb, entryBid] using hb.le
    · simpa [broadcastPart, StrictTags.lowList, StrictTags.tag, hk, hb, entryBid] using hR

theorem sourceSuccessPlan_acceptance_cap (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hR : 0 < R)
    (hRhi : R ≤ sourceLowerPriceCeiling row)
    (hΛ : (54/100 : ℝ) * Uniform07.cutoff row < Λ) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hb : ∀ k, entryBid (X.1 k) ≤ R)
    (E : Finset (Fin m))
    (hE : sourceSuccessPlan row hc R Λ z width ε PL X = some E) :
    ∀ k, k ∉ E → ∀ j,
      Weighted.acceptance (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) (Uniform07.capacity m)
        (sourceSuccessPlan row hc R Λ z width ε PL) j X k ≤
          sourceLowerMarginalCap row := by
  let α := literalSourceAlpha (m := m) row Λ z width ε
  let c := Uniform07.capacity m
  let μseed := sourceSeedMeasure row m hc R PL
  have ha : 0 < Early.nativeRadius row := (Early.native_sampling_margin_guards row).1
  have hκ : Uniform07.kappa row = 1 - Uniform07.xi row := by
    linarith [source_kappa_add_xi row]
  have hloB : sourceLowerRootBound row < Λ - Early.nativeRadius row := by
    dsimp only [sourceLowerRootBound]
    linarith
  have hroot : (1 - Uniform07.xi row) * R < Λ - Early.nativeRadius row := by
    rw [← hκ]
    exact ((mul_le_mul_of_nonneg_left hRhi (source_kappa_pos row).le).trans_lt
      (sourceLowerPriceCeiling_root_guard row)).trans hloB
  have hlo0 : 0 < Λ - Early.nativeRadius row :=
    (sourceLowerRootBound_pos row).trans hloB
  have hhi0 : 0 < Λ + Early.nativeRadius row := by linarith
  have hs : 0 < ε * m := mul_pos hε (by exact_mod_cast hm)
  have hα : 0 < (α X : ℝ) :=
    Weighted.sourcePlan_some_alpha_pos _ _ _ _ _ c μseed α X E hE
  have hg := Weighted.sourceGuardAlpha_outer c hm hε X hα
  have hlo := hg 0
  have hhi := hg 1
  simp only [Weighted.sourceSlacks, Matrix.cons_val_zero, Matrix.cons_val_one] at hlo hhi
  have hd0 : 0 ≤ Weighted.sourceDemand (Uniform07.xi row)
      (Λ + Early.nativeRadius row) X.1 :=
    Finset.sum_nonneg (fun k _ => ClippedResidual.exposure_nonneg (Uniform07.xi_pos row) hhi0)
  have hd : 0 < min (Weighted.budget c 0 X) (Weighted.budget c 1 X) := by
    have hdR : (0 : ℝ) < Weighted.commonBudget c X := by linarith
    exact_mod_cast hdR
  obtain ⟨hcard, hmargin⟩ := Weighted.sourcePlan_exclusive_margin row hΛ c μseed α X E hE
  have hlow : (min (Weighted.budget c 0 X) (Weighted.budget c 1 X) : ℝ) + E.card + ε * m <
      ∑ k, ClippedResidual.exposure (Uniform07.xi row)
        (Λ - Early.nativeRadius row) (entryBid (X.1 k)) := by
    rw [hcard, ← Nat.cast_min]
    change (Weighted.commonBudget c X : ℝ) +
      (max (Weighted.budget c 0 X) (Weighted.budget c 1 X) - Weighted.commonBudget c X : ℕ) +
        ε * m < Weighted.sourceDemand (Uniform07.xi row) (Λ - Early.nativeRadius row) X.1
    linarith
  have hhigh : (∑ k, ClippedResidual.exposure (Uniform07.xi row)
      (Λ + Early.nativeRadius row) (entryBid (X.1 k))) <
        (min (Weighted.budget c 0 X) (Weighted.budget c 1 X) : ℝ) - ε * m := by
    rw [← Nat.cast_min]
    change Weighted.sourceDemand (Uniform07.xi row) (Λ + Early.nativeRadius row) X.1 <
      (Weighted.commonBudget c X : ℝ) - ε * m
    linarith
  obtain ⟨zr, hzr, hr, hcap⟩ := Weighted.source_U4_acceptance_le_lowerMarginalCap
    (Uniform07.xi_pos row) (source_xi_lt_one row) c
    (sourceSuccessPlan row hc R Λ z width ε PL) X hX E hE
    hR hlo0 (by linarith) (sourceLowerPriceCeiling_pos row) hRhi hroot hb
    hd hs hcard hlow hhigh (fun k hk => by linarith [hmargin k hk])
  have hmono : Weighted.lowerMarginalCap (Uniform07.xi row)
      (Λ - Early.nativeRadius row) (sourceLowerPriceCeiling row) ≤
        sourceLowerMarginalCap row :=
    Weighted.lowerMarginalCap_antitone_root (Uniform07.xi_pos row)
      (sourceLowerPriceCeiling_pos row) hloB.le
  exact fun k hk j => (hcap k hk j).trans hmono

lemma sourceSuccessPlan_no_multiple_exceptional (row : Uniform07.Row)
    (hc : 1 ≤ Uniform07.capacity m) (R Λ z width ε : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) (X : ClassifiedContext m)
    (E : Finset (Fin m))
    (hE : sourceSuccessPlan row hc R Λ z width ε PL X = some E) :
    ¬ 1 < (Weighted.exceptionalSet (Early.bidCap row) X.1).card := by
  intro h
  have hn := Weighted.sourcePlan_multiple_exceptional (Uniform07.xi row) Λ
    (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row / 2)
    (Uniform07.capacity m) (sourceSeedMeasure row m hc R PL)
    (literalSourceAlpha row Λ z width ε) X h
  change sourceSuccessPlan row hc R Λ z width ε PL X = none at hn
  rw [hE] at hn
  cases hn

theorem literalSource_local_acceptance_eq_weighted (row : Uniform07.Row)
    (hc : 1 ≤ Uniform07.capacity m) (R Λ z width ε : ℝ)
    (hΛ : (54/100 : ℝ) * Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L)
    (i : Fin m) (b : ℝ) (hi : L i = some b) (hb : b < R)
    (E : Finset (Fin m))
    (hE : sourceSuccessPlan row hc R Λ z width ε PL (observedContext R j L) = some E) :
    localSeedAcceptance (literalSourceNativeGame row hc R Λ z width ε hΛ PL) j L i =
      Weighted.acceptance (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) (Uniform07.capacity m)
        (sourceSuccessPlan row hc R Λ z width ε PL) j (observedContext R j L) i := by
  let C := sourceWeightedContext row hc R Λ (source_guard_multiplier_positive row hΛ) PL
    (literalSourceAlpha row Λ z width ε) (measurable_literalSourceAlpha row hΛ z width ε)
  have hpres : broadcastPart R L i ≠ none := by
    rw [broadcastPart_some L i hi hb]
    simp
  have hnot := sourceSuccessPlan_no_multiple_exceptional row hc R Λ z width ε PL
    (observedContext R j L) E hE
  rw [localSeedAcceptance_eq_integral]
  change (∫s : unitInterval,
    if i ∈ C.selection R j (AllLists.clean L) s then (1 : ℝ) else 0) = _
  rw [AllLists.clean_eq L hL]
  calc
    _ = ∫s : unitInterval,
        if i ∈ C.select j (observedContext R j L) s then (1 : ℝ) else 0 := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro s
      change (if i ∈ C.selection R j L s then (1:ℝ) else 0) = _
      simp only [C.factors R j L s i hpres]
    _ = _ := by
      simp only [C, sourceWeightedContext, Weighted.sourceContextPolicy,
        Weighted.completedContextPolicy, Weighted.completedSelect, if_neg hnot,
        Weighted.acceptance, sourceSuccessPlan]
      rfl

omit [Nonempty (Fin m)] in
lemma localSeedAcceptance_zero_of_absent {n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (j : Fin n) (L : LocalList m) (i : Fin m)
    (hi : L i = none) : localSeedAcceptance Γ j L i = 0 := by
  have hnone : ∀ s, i ∉ (Γ.policy j L s).val := fun s hs =>
    (Γ.policy j L s).property.2 i hs hi
  rw [localSeedAcceptance_eq_integral]
  simp only [hnone, if_false, integral_zero]

theorem literalSource_local_acceptance_cap_on_good (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hR : 0 < R)
    (hRhi : R ≤ sourceLowerPriceCeiling row)
    (hΛ : (54/100 : ℝ) * Uniform07.cutoff row < Λ) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) (i : Fin m) (a : JointAction 2)
    (ha : a.bid < R) (d : UserProfile m 2)
    (hd : d ∈ sourceSuccessGood row hc R Λ z width ε PL i a) :
    ∀ τ j, localSeedAcceptance
      (literalSourceNativeGame row hc R Λ z width ε hΛ PL) j (deviationList i a d τ j) i ≤
        sourceLowerMarginalCap row := by
  intro τ j
  let L := deviationList i a d τ j
  let Γ := literalSourceNativeGame row hc R Λ z width ε hΛ PL
  by_cases hn : L i = none
  · rw [show deviationList i a d τ j = L from rfl,
      localSeedAcceptance_zero_of_absent Γ j L i hn]
    exact (sourceLowerMarginalCap_bounds row).1
  · obtain ⟨E, hE, hiE⟩ := (hd τ j).resolve_left hn
    have hi : L i = some a.bid := by
      by_cases hj : j ∈ firstK τ a.routeCount
      · simp [L, deviationList, observe, deviate, hj]
      · exact (hn (by simp [L, deviationList, observe, deviate, hj])).elim
    have hL : NonnegativeList L := by
      intro k
      change 0 ≤ entryBid
        (observe (deviate (drawsRealization d) i a.bid a.bid_nonneg
          (firstK τ a.routeCount)) j k)
      unfold observe
      split_ifs
      · exact ((deviate (drawsRealization d) i a.bid a.bid_nonneg
          (firstK τ a.routeCount)).action k).bid_nonneg
      · exact le_rfl
    have hX : NonnegativeList (observedContext R j L).1 :=
      source_broadcastPart_nonnegative L hL
    have hb : ∀ k, entryBid ((observedContext R j L).1 k) ≤ R :=
      source_broadcastPart_le_floor hR.le L
    rw [literalSource_local_acceptance_eq_weighted row hc R Λ z width ε hΛ PL
      j L hL i a.bid hi ha E hE]
    exact sourceSuccessPlan_acceptance_cap row hm hc hR hRhi hΛ hε PL
      (observedContext R j L) hX hb E hE i hiE j

theorem literalSource_all_lower_contracts_success_cap (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hR : 0 < R)
    (hRhi : R ≤ sourceLowerPriceCeiling row)
    (hΛ : (54/100 : ℝ) * Uniform07.cutoff row < Λ) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hbad : ∀ i (a : JointAction 2), a.bid < R →
      (userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)).real
        (sourceSuccessGood row hc R Λ z width ε PL i a)ᶜ ≤
          (1 - sourceLowerMarginalCap row) ^ 2 / 2) :
    (∀ i (a : JointAction 2), a.bid < R →
      ((problem (literalSourceNativeGame row hc R Λ z width ε hΛ PL) i).outcome a).success ≤
        sourceLowerSuccessCap row) ∧ sourceLowerSuccessCap row < 1 := by
  apply all_lower_contracts_success_cap _ {a : JointAction 2 | a.bid < R}
    (sourceLowerMarginalCap_bounds row).1 (sourceLowerMarginalCap_bounds row).2 le_rfl
  intro i a ha
  refine ⟨sourceSuccessGood row hc R Λ z width ε PL i a,
    measurableSet_sourceSuccessGood row hc R Λ z width ε hΛ PL i a,
    hbad i a ha, ?_⟩
  exact Eventually.of_forall (fun d hd =>
    literalSource_local_acceptance_cap_on_good row hm hc hR hRhi hΛ hε PL i a ha d hd)

theorem sourceNative_lower_success_cap_of_plan_bad_mass (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hR : 0 < R)
    (hRhi : R ≤ sourceLowerPriceCeiling row)
    (hΛ : (54/100 : ℝ) * Uniform07.cutoff row < Λ) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hbad : ∀ i (a : JointAction 2), a.bid < R →
      (userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)).real
        (sourceSuccessGood row hc R Λ z width ε PL i a)ᶜ ≤
          (1 - sourceLowerMarginalCap row) ^ 2 / 2) :
    ∀ i (a : JointAction 2), a.bid < R →
      ((problem (sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
        (literalSourceAlpha row Λ z width ε) (measurable_literalSourceAlpha row hΛ z width ε)) i).outcome a).success ≤
          sourceLowerSuccessCap row := by
  intro i a ha
  have h := (literalSource_all_lower_contracts_success_cap row hm hc hR hRhi hΛ hε PL hbad).1 i a ha
  simpa only [literalSourceNativeGame, completeSourceNativeGame_outcome] using h

theorem literalSource_conditional_success_cap (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hR : 0 < R)
    (hRhi : R ≤ sourceLowerPriceCeiling row)
    (hΛ : (54/100 : ℝ) * Uniform07.cutoff row < Λ) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hbad : ∀ i (a : JointAction 2), a.bid < R →
      (userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)).real
        (sourceSuccessGood row hc R Λ z width ε PL i a)ᶜ ≤
          (1 - sourceLowerMarginalCap row) ^ 2 / 2)
    (V : Set ℝ)
    (hsupport : ∀ v ∈ V,
      ∀ᵐ a ∂(literalSourceNativeGame row hc R Λ z width ε hΛ PL).σ v, a.bid < R) :
    ∀ v ∈ V,
      (conditionalTypeCountLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL) hm v).success ≤
        sourceLowerSuccessCap row := by
  have hcap := (literalSource_all_lower_contracts_success_cap row hm hc hR hRhi hΛ hε PL hbad).1
  exact fun v hv => conditional_success_le_of_action_caps _ hm v
    {a : JointAction 2 | a.bid < R} (hsupport v hv) hcap

end FCAppendix.Affine.Uniform07Finishing
