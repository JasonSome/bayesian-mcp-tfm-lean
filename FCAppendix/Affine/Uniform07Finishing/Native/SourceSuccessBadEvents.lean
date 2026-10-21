import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessCap
import FCAppendix.Affine.Uniform07Finishing.Native.WeightedTargetProbability
import FCAppendix.Affine.Uniform07Finishing.Native.ForcedFocalSeed

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Bayes Game Set Classical
open StrictNative ConditionalSuccess
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def sourceSuccessSlacks (row : Uniform07.Row) (Λ z width : ℝ)
    (X : ClassifiedContext m) : Fin 5 → ℝ :=
  Weighted.sourceSlacks (Uniform07.xi row) Λ (Early.nativeRadius row)
    (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
    z (Uniform07.cutoff row) width (Uniform07.capacity m) X

omit [Nonempty (Fin m)] in
lemma measurable_sourceSuccessSlacks (row : Uniform07.Row) {Λ : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (z width : ℝ) (k : Fin 5) :
    Measurable (fun X : ClassifiedContext m => sourceSuccessSlacks row Λ z width X k) :=
  Weighted.measurable_sourceSlacks (Uniform07.xi_pos row)
    (Early.native_sampling_margin_guards row).1 (source_guard_root_positive row hΛ)
    (div_pos (Uniform07.cutoff_pos row) (by norm_num : (0 : ℝ) < 1000))
    (Early.demandRatio row) (Early.bidCap row) z (Uniform07.cutoff row) width
    (Uniform07.capacity m) k

def SourceRivalShape (U R : ℝ) (i : Fin m) (d : UserProfile m 2) : Prop :=
  ∀ u, u ≠ i →
    ((d u).1.2.bid ≤ U ∧ (d u).1.2.routeCount = 2) ∨
      (R ≤ (d u).1.2.bid ∧ (d u).1.2.routeCount = 1)

omit [Nonempty (Fin m)] in
lemma source_rival_broadcast_bid_le {U R : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    (i : Fin m) (a : JointAction 2) (d : UserProfile m 2)
    (hd : SourceRivalShape U R i d) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (u : Fin m) (hui : u ≠ i) :
    entryBid (broadcastPart R (deviationList i a d τ j) u) ≤ U := by
  rcases hd u hui with hl | hh
  · have hbR : (d u).1.2.bid < R := hl.1.trans_lt hUR
    simpa [broadcastPart,StrictTags.lowList,StrictTags.tag,deviationList,
      observe,deviate,drawsRealization,hui,hl.2,firstK_full_two,hbR,entryBid]
      using hl.1
  · by_cases hj : j ∈ firstK (d u).2 (d u).1.2.routeCount <;>
      simpa [broadcastPart,StrictTags.lowList,StrictTags.tag,deviationList,
        observe,deviate,drawsRealization,hui,hj,not_lt.mpr hh.1,entryBid] using hU

omit [Nonempty (Fin m)] in
lemma source_deviation_exceptional_card_le_one {U R : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    (i : Fin m) (a : JointAction 2) (d : UserProfile m 2)
    (hd : SourceRivalShape U R i d) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    (Weighted.exceptionalSet U (observedContext R j (deviationList i a d τ j)).1).card ≤ 1 := by
  have hsub : Weighted.exceptionalSet U
      (observedContext R j (deviationList i a d τ j)).1 ⊆ {i} := by
    intro u hu
    by_contra hui
    have hne : u ≠ i := by simpa only [Finset.mem_singleton] using hui
    have hb := source_rival_broadcast_bid_le hU hUR i a d hd τ j u hne
    have hgt : U < entryBid (broadcastPart R (deviationList i a d τ j) u) := by
      have hx := (Finset.mem_filter.mp hu).2
      exact hx.2
    exact (not_lt_of_ge hb) hgt
  exact (Finset.card_le_card hsub).trans (by simp)

lemma sourceSuccessPlan_some_of_inner (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    (R Λ z width ε : ℝ) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) (X : ClassifiedContext m)
    (hex : (Weighted.exceptionalSet (Early.bidCap row) X.1).card ≤ 1)
    (hinner : ∀ k : Fin 5, 2*(ε*m) ≤ sourceSuccessSlacks row Λ z width X k)
    (hseed : Weighted.sourceSeed (sourceSeedMeasure row m hc R PL)
      (Uniform07.cutoff row/2) X ≠ none) :
    ∃ E, sourceSuccessPlan row hc R Λ z width ε PL X = some E := by
  have hα : literalSourceAlpha row Λ z width ε X = 1 :=
    Weighted.sourceGuardAlpha_inner (Uniform07.capacity m) hm hε X hinner
  have hslack := hinner 2
  have hpos : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
  have hW : ((max (Weighted.budget (Uniform07.capacity m) 0 X)
      (Weighted.budget (Uniform07.capacity m) 1 X)-
        Weighted.commonBudget (Uniform07.capacity m) X : ℕ) : ℝ) <
      FCAppendix.Affine.WeightedSampling.totalWeight
        (Weighted.sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row)
          (Early.bidCap row) X.1) := by
    change 2*(ε*m) ≤ FCAppendix.Affine.WeightedSampling.totalWeight
      (Weighted.sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)-
      (max (Weighted.budget (Uniform07.capacity m) 0 X) (Weighted.budget (Uniform07.capacity m) 1 X)-
        Weighted.commonBudget (Uniform07.capacity m) X : ℕ) at hslack
    linarith
  cases hs : Weighted.sourceSeed (sourceSeedMeasure row m hc R PL)
      (Uniform07.cutoff row/2) X with
  | none => exact (hseed hs).elim
  | some s =>
      obtain ⟨E,hE⟩ := Weighted.planSampler_one_isSome
        (max (Weighted.budget (Uniform07.capacity m) 0 X)
          (Weighted.budget (Uniform07.capacity m) 1 X)-
            Weighted.commonBudget (Uniform07.capacity m) X)
        (Weighted.sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row)
          (Early.bidCap row) X.1) s
      refine ⟨E,?_⟩
      dsimp only [sourceSuccessPlan,Weighted.sourcePlan]
      rw [if_pos (show (Weighted.exceptionalSet (Early.bidCap row) X.1).card ≤ 1 ∧
        ((max (Weighted.budget (Uniform07.capacity m) 0 X)
          (Weighted.budget (Uniform07.capacity m) 1 X)-
          Weighted.commonBudget (Uniform07.capacity m) X : ℕ) : ℝ) <
        FCAppendix.Affine.WeightedSampling.totalWeight
          (Weighted.sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row)
            (Early.bidCap row) X.1) from ⟨hex,hW⟩)]
      simpa only [hs,Weighted.sampleSeedOption,hα] using hE

def sourceScalarGuardFailure (row : Uniform07.Row) (R Λ z width ε : ℝ)
    (i : Fin m) (a : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (k : Fin 5) :
    Set (UserProfile m 2) :=
  {d | deviationList i a d τ j i ≠ none ∧
    sourceSuccessSlacks row Λ z width
      (observedContext R j (deviationList i a d τ j)) k < 2*(ε*m)}

def sourceFocalSeedFailure (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m)
    (R : ℝ) (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (i : Fin m) (a : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    Set (UserProfile m 2) :=
  {d | deviationList i a d τ j i ≠ none ∧
    Weighted.sourceSeed (sourceSeedMeasure row m hc R PL) (Uniform07.cutoff row/2)
      (observedContext R j (deviationList i a d τ j)) = none}

def sourceExclusiveHit (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m)
    (R Λ z width ε : ℝ) (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (i : Fin m) (a : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    Set (UserProfile m 2) :=
  {d | deviationList i a d τ j i ≠ none ∧ ∃ E : Finset (Fin m),
    sourceSuccessPlan row hc R Λ z width ε PL
      (observedContext R j (deviationList i a d τ j)) = some E ∧ i ∈ E}

omit [Nonempty (Fin m)] in
lemma measurableSet_sourceScalarGuardFailure (row : Uniform07.Row) (R Λ z width ε : ℝ)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (i : Fin m) (a : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (k : Fin 5) :
    MeasurableSet (sourceScalarGuardFailure row R Λ z width ε i a τ j k) := by
  have hL := measurable_deviationList_profile i a τ j
  exact (measurableSet_eq_fun ((measurable_pi_apply i).comp hL) measurable_const).compl.inter
    (measurableSet_lt ((measurable_sourceSuccessSlacks row hΛ z width k).comp
      ((measurable_observedContext R j).comp hL)) measurable_const)

omit [Nonempty (Fin m)] in
lemma measurableSet_sourceFocalSeedFailure (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m)
    (R : ℝ) (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (i : Fin m) (a : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    MeasurableSet (sourceFocalSeedFailure row hc R PL i a τ j) := by
  have hL := measurable_deviationList_profile i a τ j
  exact (measurableSet_eq_fun ((measurable_pi_apply i).comp hL) measurable_const).compl.inter
    (((Weighted.measurable_sourceSeed (sourceSeedMeasure row m hc R PL)
      (Uniform07.cutoff row/2)).comp ((measurable_observedContext R j).comp hL))
      (show MeasurableSet ({none} : Set (Option unitInterval)) from by
        change MeasurableSet ((some : unitInterval → Option unitInterval) ⁻¹' ({none} : Set (Option unitInterval)))
        have he : ((some : unitInterval → Option unitInterval) ⁻¹' ({none} : Set (Option unitInterval))) = ∅ := by
          ext x
          simp only [Set.mem_preimage,Set.mem_singleton_iff,Option.some_ne_none,Set.mem_empty_iff_false]
        rw [he]
        exact MeasurableSet.empty))

lemma measurableSet_sourceExclusiveHit (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m)
    (R Λ z width ε : ℝ) (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (i : Fin m) (a : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    MeasurableSet (sourceExclusiveHit row hc R Λ z width ε PL i a τ j) := by
  have hL := measurable_deviationList_profile i a τ j
  apply (measurableSet_eq_fun ((measurable_pi_apply i).comp hL) measurable_const).compl.inter
  have hp := (measurable_sourceSuccessPlan row hc R Λ z width ε hΛ PL).comp
    ((measurable_observedContext R j).comp hL)
  change MeasurableSet {d : UserProfile m 2 | ∃ E : Finset (Fin m),
    sourceSuccessPlan row hc R Λ z width ε PL
      (observedContext R j (deviationList i a d τ j)) = some E ∧ i ∈ E}
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro E
  by_cases hi : i ∈ E
  · simpa only [hi,and_true,Function.comp_apply] using measurableSet_eq_fun hp (measurable_const (a := some E))
  · simp only [hi,and_false,Set.setOf_false,MeasurableSet.empty]

omit [Nonempty (Fin m)] in
lemma source_deviation_focal_bid {R : ℝ} (i : Fin m) (a : JointAction 2)
    (ha : a.bid < R) (d : UserProfile m 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hcontact : deviationList i a d τ j i ≠ none) :
    (observedContext R j (deviationList i a d τ j)).1 i = some a.bid := by
  have hL : deviationList i a d τ j i = some a.bid := by
    by_cases hj : j ∈ firstK τ a.routeCount
    · simp [deviationList,observe,deviate,hj]
    · exact (hcontact (by simp [deviationList,observe,deviate,hj])).elim
  simp only [observedContext,broadcastPart,StrictTags.lowList,StrictTags.tag,hL,if_pos ha,
    if_true]

theorem sourceExclusiveHit_empty_of_ineligible (row : Uniform07.Row)
    (hc : 1 ≤ Uniform07.capacity m) (R Λ z width ε : ℝ)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) (i : Fin m) (a : JointAction 2)
    (ha : a.bid < R) (hineligible : a.bid ≤ Uniform07.cutoff row/2 ∨ Early.bidCap row < a.bid)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    sourceExclusiveHit row hc R Λ z width ε PL i a τ j = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro d hd
  rcases hd with ⟨hcontact,E,hE,hi⟩
  have hL := source_deviation_focal_bid i a ha d τ j hcontact
  have hn : i ∉ E := by
    rcases hineligible with hs | ho
    · have hz : Uniform07.cutoff row/2 ≤ Λ := by
        have ht := Uniform07.cutoff_pos row
        linarith
      exact Weighted.sourcePlan_omits_seed (Uniform07.xi row) Λ (Early.demandRatio row)
        (Early.bidCap row) (Uniform07.cutoff row/2) (Early.demandRatio_pos row) hz
        (Uniform07.capacity m) (sourceSeedMeasure row m hc R PL)
        (literalSourceAlpha row Λ z width ε) _ E hE i a.bid hL hs
    · exact (Weighted.sourcePlan_omits_outside (Uniform07.xi row) Λ (Early.demandRatio row)
        (Early.bidCap row) (Uniform07.cutoff row/2) (Uniform07.capacity m)
        (sourceSeedMeasure row m hc R PL) (literalSourceAlpha row Λ z width ε)
        _ E hE i a.bid hL ho).1
  exact hn hi

omit [Nonempty (Fin m)] in
theorem source_focal_seed_failure_le_exp (row : Uniform07.Row)
    (hc : 1 ≤ Uniform07.capacity m) {R : ℝ} (hUR : Early.bidCap row < R)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] (i : Fin m) (a : JointAction 2)
    (hshape : ∀ᵐ d ∂Measure.pi (fun _ : Fin m => μ),
      SourceRivalShape (Early.bidCap row) R i d)
    (hseed : Uniform07.cutoff row/2 ≤ μ.real (sourceSeedCategory (Uniform07.cutoff row/2)))
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    (Measure.pi (fun _ : Fin m => μ)).real (sourceFocalSeedFailure row hc R PL i a τ j) ≤
      Real.exp (-((m-1 : ℕ) : ℝ)*(Uniform07.cutoff row/2)) := by
  have hzR : Uniform07.cutoff row/2 < R := (source_seed_cutoff_lt_bidCap row).trans hUR
  have hinc : ∀ᵐ d ∂Measure.pi (fun _ : Fin m => μ),
      d ∈ sourceFocalSeedFailure row hc R PL i a τ j →
        d ∈ focalRivalsNoSeed (Uniform07.cutoff row/2) i := by
    filter_upwards [hshape] with d hd
    intro hs
    apply deviation_seed_none_imp_rivals_no_seed (U := Early.bidCap row) i hzR
      (sourceSeedMeasure row m hc R PL) a d τ j _ hs.2
    intro u hui hu
    rcases hd u hui with hl | hh
    · exact hl.2
    · exact ((not_lt_of_ge hh.1) (hu.trans_lt hzR)).elim
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hinc)).trans
    (focal_rivals_no_seed_real_le_exp μ i _ _ hseed)

theorem sourceSuccess_bad_event_inclusion (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hUR : Early.bidCap row < R) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) (i : Fin m) (a : JointAction 2)
    (d : UserProfile m 2) (hd : SourceRivalShape (Early.bidCap row) R i d)
    (hbad : d ∉ sourceSuccessGood row hc R Λ z width ε PL i a) :
    ∃ τ j,
      (∃ k : Fin 5, d ∈ sourceScalarGuardFailure row R Λ z width ε i a τ j k) ∨
      d ∈ sourceFocalSeedFailure row hc R PL i a τ j ∨
      d ∈ sourceExclusiveHit row hc R Λ z width ε PL i a τ j := by
  by_contra hn
  apply hbad
  intro τ j
  by_cases hnone : deviationList i a d τ j i = none
  · exact Or.inl hnone
  · right
    have hinner : ∀ k : Fin 5, 2*(ε*m) ≤ sourceSuccessSlacks row Λ z width
        (observedContext R j (deviationList i a d τ j)) k := by
      intro k
      by_contra hk
      exact hn ⟨τ,j,Or.inl ⟨k,hnone,lt_of_not_ge hk⟩⟩
    have hs : Weighted.sourceSeed (sourceSeedMeasure row m hc R PL)
        (Uniform07.cutoff row/2)
        (observedContext R j (deviationList i a d τ j)) ≠ none := by
      intro he
      exact hn ⟨τ,j,Or.inr (Or.inl ⟨hnone,he⟩)⟩
    have hex := source_deviation_exceptional_card_le_one
      (Early.upper_floor_interface row).2.1.le hUR i a d hd τ j
    obtain ⟨E,hE⟩ := sourceSuccessPlan_some_of_inner row hm hc R Λ z width ε hε PL
      (observedContext R j (deviationList i a d τ j)) hex hinner hs
    refine ⟨E,hE,?_⟩
    intro hi
    exact hn ⟨τ,j,Or.inr (Or.inr ⟨hnone,E,hE,hi⟩)⟩

theorem sourceSuccess_bad_mass_le (row : Uniform07.Row)
    (hm : 0 < m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hUR : Early.bidCap row < R) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (μ : Measure (UserProfile m 2)) [IsProbabilityMeasure μ]
    (i : Fin m) (a : JointAction 2)
    (hshape : ∀ᵐ d ∂μ, SourceRivalShape (Early.bidCap row) R i d)
    {g s e : ℝ}
    (hguard : ∀ τ j k, μ.real (sourceScalarGuardFailure row R Λ z width ε i a τ j k) ≤ g)
    (hseed : ∀ τ j, μ.real (sourceFocalSeedFailure row hc R PL i a τ j) ≤ s)
    (hhit : ∀ τ j, μ.real (sourceExclusiveHit row hc R Λ z width ε PL i a τ j) ≤ e) :
    μ.real (sourceSuccessGood row hc R Λ z width ε PL i a)ᶜ ≤ 4*(5*g+s+e) := by
  let B := fun (τ : Equiv.Perm (Fin 2)) (j : Fin 2) =>
    ((⋃ k : Fin 5, sourceScalarGuardFailure row R Λ z width ε i a τ j k) ∪
      sourceFocalSeedFailure row hc R PL i a τ j) ∪
      sourceExclusiveHit row hc R Λ z width ε PL i a τ j
  have hinc : ∀ᵐ d ∂μ, d ∈ (sourceSuccessGood row hc R Λ z width ε PL i a)ᶜ →
      d ∈ ⋃ τ, ⋃ j, B τ j := by
    filter_upwards [hshape] with d hd
    intro hb
    obtain ⟨τ,j,h⟩ := sourceSuccess_bad_event_inclusion row hm hc hUR hε PL i a d hd hb
    refine mem_iUnion.mpr ⟨τ,mem_iUnion.mpr ⟨j,?_⟩⟩
    rcases h with ⟨k,hk⟩ | hs | he
    · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨k,hk⟩))
    · exact Or.inl (Or.inr hs)
    · exact Or.inr he
  have hB : ∀ τ j, μ.real (B τ j) ≤ 5*g+s+e := by
    intro τ j
    have hg : μ.real (⋃ k : Fin 5,
        sourceScalarGuardFailure row R Λ z width ε i a τ j k) ≤ 5*g := by
      refine (measureReal_iUnion_fintype_le _).trans ?_
      calc
        (∑ k : Fin 5, μ.real (sourceScalarGuardFailure row R Λ z width ε i a τ j k)) ≤
            ∑ _ : Fin 5, g := Finset.sum_le_sum (fun k _ => hguard τ j k)
        _ = 5*g := by simp
    exact (measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans (add_le_add hg (hseed τ j))) (hhit τ j))
  calc
    _ ≤ μ.real (⋃ τ, ⋃ j, B τ j) :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hinc)
    _ ≤ ∑ τ : Equiv.Perm (Fin 2), μ.real (⋃ j : Fin 2, B τ j) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ τ : Equiv.Perm (Fin 2), ∑ j : Fin 2, μ.real (B τ j) :=
      Finset.sum_le_sum (fun τ _ => measureReal_iUnion_fintype_le _)
    _ ≤ ∑ _ : Equiv.Perm (Fin 2), ∑ _ : Fin 2, (5*g+s+e) :=
      Finset.sum_le_sum (fun τ _ => Finset.sum_le_sum (fun j _ => hB τ j))
    _ = 4*(5*g+s+e) := by
      have hperm : Fintype.card (Equiv.Perm (Fin 2)) = 2 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_perm]
        norm_num
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,hperm,nsmul_eq_mul]
      ring

end FCAppendix.Affine.Uniform07Finishing
