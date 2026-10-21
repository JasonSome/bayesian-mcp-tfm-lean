import FCAppendix.Affine.Hybrid.Native02.FullContextExceptional
import FCAppendix.Affine.Hybrid.Native02.FullContextRows
import FCAppendix.Affine.Hybrid.Native02.PhysicalRowIntegration
import FCAppendix.Affine.Hybrid.Native02.FullContextUniformMenus
import FCAppendix.Affine.Hybrid.Native02.PrimitiveMenuMargins
import FCAppendix.Affine.Hybrid.ActivePatternCountBounds

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Filter Topology Classical
open scoped BigOperators

theorem actualClosedContext_eq_physicalRow_zero_lower {N : ℕ} {d U R : ℝ}
    (hdU : d≤ U) (hUR : U< R) (z : UserProfile (N+1) 2)
    (hz : z∈ closedProfiles (N+1) R)
    (hgap : ∀ k : Fin (N+1),k≠0 → (z k).1.2.bid≤ U ∨ R≤(z k).1.2.bid)
    (hf : (z 0).1.2.bid< R) :
    actualClosedContext R z=
      physicalRowContext (z 0).1.2.bid (physicalDeletedRow d U 0 z) := by
  have hu (j : Fin 2) :
      TaggedLocal.upperAt (closedKind R z) (drawsRealization z) j=
        classCount (NativeContinuation.upperTag j) (physicalDeletedRow d U 0 z) := by
    have hf0 : ¬(closedKind R z 0=2 ∧ j∈(drawsRealization z).recipients 0) :=
      fun h => (not_le.mpr hf) ((closedKind_upper_iff R z 0).mp h.1)
    unfold TaggedLocal.upperAt
    rw [Fin.sum_univ_succ]
    simp only [if_neg hf0,zero_add]
    unfold classCount
    apply Finset.sum_congr rfl
    intro k _
    have ht : (closedKind R z k.succ=2 ∧ j∈(drawsRealization z).recipients k.succ) ↔
        (physicalRow d U (z k.succ)).1=NativeContinuation.upperTag j := by
      rw [closedKind_upper_iff]
      exact physicalRow_upper_entry hdU hUR (z k.succ) (hz k.succ)
        (hgap k.succ (Fin.succ_ne_zero k)) j
    simp only [physicalDeletedRow,Fin.succAbove_zero]
    exact if_congr ht rfl rfl
  apply Prod.ext
  · change lowerPart R (observe (drawsRealization z) 0)=_
    rw [lowerPart_observe z hz 0]
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [physicalRowContext,hf]
    · simpa only [physicalRowContext,Fin.cons_succ,physicalDeletedRow,Fin.succAbove_zero] using
        physicalRow_lower_entry hdU hUR (z k.succ) (hgap k.succ (Fin.succ_ne_zero k))
  · exact Prod.ext (by simpa [actualClosedContext, physicalRowContext,NativeContinuation.upperTag] using hu 0)
      (by simpa [actualClosedContext, physicalRowContext,NativeContinuation.upperTag] using hu 1)

theorem actualClosedContext_eq_physicalRow_lower {N : ℕ} {d U R : ℝ}
    (hdU : d≤ U) (hUR : U< R) (z : UserProfile (N+1) 2)
    (hz : z∈ closedProfiles (N+1) R) (i : Fin (N+1))
    (hgap : ∀ k,k≠i → (z k).1.2.bid≤ U ∨ R≤(z k).1.2.bid)
    (hf : (z i).1.2.bid< R) :
    actualClosedContext R z=
      reindexedPhysicalContext i (z i).1.2.bid (physicalDeletedRow d U i z) := by
  let e := NativeContinuation.focalIndex i
  have hg : ∀ k : Fin (N+1),k≠0 → (z (e k)).1.2.bid≤ U ∨ R≤(z (e k)).1.2.bid := by
    intro k hk
    apply hgap (e k)
    intro he
    apply hk
    apply e.injective
    simpa only [e,NativeContinuation.focalIndex_zero] using he
  have he := actualClosedContext_eq_physicalRow_zero_lower hdU hUR (z ∘ e)
    (fun k => hz (e k)) hg
    (by simpa only [e,Function.comp_apply,NativeContinuation.focalIndex_zero] using hf)
  rw [actualClosedContext_reindex] at he
  have hr : physicalDeletedRow d U 0 (z ∘ e)=physicalDeletedRow d U i z := by
    funext k
    simp [physicalDeletedRow,e]
  simp only [Function.comp_apply,e,NativeContinuation.focalIndex_zero,hr] at he
  have hh := congrArg (NativeContinuation.reindexContext e.symm) he
  simpa only [NativeContinuation.reindexContext,reindexedPhysicalContext,
    Function.comp_def,Equiv.apply_symm_apply,e] using hh

theorem insertedLowerContext_eq_physicalRow_all_lower {N : ℕ} {d U R : ℝ}
    (hdU : d≤ U) (hUR : U< R) (i : Fin (N+1)) (act : JointAction 2)
    (hb : act.bid< R) (hk : act.routeCount=2)
    (z : UserProfile (N+1) 2) (hz : z∈ closedProfiles (N+1) R)
    (hgap : ∀ k,(z k).1.2.bid≤ U ∨ R≤(z k).1.2.bid) :
    insertedLowerContext R i act z=
      reindexedPhysicalContext i act.bid (physicalDeletedRow d U i z) := by
  have hi := insertedLowerProfile_mem i act hb hk z hz
  have hg : ∀ k,k≠i → ((insertedLowerProfile i act z) k).1.2.bid≤ U ∨
      R≤((insertedLowerProfile i act z) k).1.2.bid := by
    intro k hki
    simpa only [insertedLowerProfile,Function.update_of_ne hki] using hgap k
  rw [insertedLowerContext_eq_actual i act hb hk z hz,
    actualClosedContext_eq_physicalRow_lower hdU hUR (insertedLowerProfile i act z) hi i hg
      (by simpa [insertedLowerProfile] using hb)]
  have hr : physicalDeletedRow d U i (insertedLowerProfile i act z)=physicalDeletedRow d U i z := by
    funext k
    simp only [physicalDeletedRow,insertedLowerProfile,Function.update_of_ne (Fin.succAbove_ne i k)]
  rw [show (insertedLowerProfile i act z i).1.2.bid = act.bid by simp [insertedLowerProfile]]
  rw [hr]

theorem closed_broadcast_count_physicalRows_all_lower {N c : ℕ}
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {d U R : ℝ} (hdU : d≤ U) (hUR : U< R) (hseed : Γ.seedLaw=volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ,z∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,x.2.bid≤ U ∨ R≤ x.2.bid)
    (ν : Measure RowRival) (hrow : (userLaw Γ).map (physicalRow d U)=ν)
    (i : Fin (N+1)) (act : JointAction 2) (hb : act.bid< R)
    (hk : act.routeCount=2) (f : Fin 3 → ℝ) :
    ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).expect f=
      ∫ r,(privateContextLaw C (reindexedPhysicalContext i act.bid r) i).expect f
        ∂Measure.pi (fun _ : Fin N => ν) := by
  rw [closed_broadcast_count_expectation C Γ hseed hfull i act hb hk]
  calc
    _ = ∫ z,(privateContextLaw C (reindexedPhysicalContext i act.bid
        (physicalDeletedRow d U i z)) i).expect f ∂userProfileLaw Γ := by
      apply integral_congr_ae
      filter_upwards [hfull,profile_noGap_support Γ U R hgap] with z hz hzgap
      rw [insertedLowerContext_eq_physicalRow_all_lower hdU hUR i act hb hk z hz hzgap]
    _ = _ := by
      rw [←deleted_physical_rival_rows_law Γ d U i ν hrow]
      exact (integral_map (measurable_physicalDeletedRow d U i).aemeasurable
        ((measurable_privateContextLaw_expect C i f).comp
          (measurable_reindexedPhysicalContext i act.bid)).aestronglyMeasurable).symm

namespace FullContext
variable {N : ℕ}

lemma activeSet_sourceRow_exceptional {d L U : ℝ} (hsep : d< L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j,low j∈ Icc 0 d) (hactive : ∀ j,active j∈ Icc L U) (hb : d< b) :
    activeSet d (sourceRowContext kind low active b).1=
      Finset.univ.filter (activePatternPred kind) := by
  ext i
  simp only [activeSet,Finset.mem_filter,Finset.mem_univ,true_and]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sourceRowContext_zero,activePatternPred,entryBid,hb]
  · rw [sourceRowContext_succ]
    by_cases h₀ : kind j=0
    · have h₁ : kind j≠1 := by simpa only [h₀] using (show (0:Fin 4)≠1 by decide)
      simp [activePatternPred,h₀,entryBid,not_lt_of_ge (hlow j).2]
    · by_cases h₁ : kind j=1
      · simp [activePatternPred,h₁,entryBid,hsep.trans_le (hactive j).1]
      · simp [activePatternPred,h₀,h₁,entryBid]

lemma activeSet_sourceRow_exceptional_card {d L U : ℝ} (hsep : d< L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j,low j∈ Icc 0 d) (hactive : ∀ j,active j∈ Icc L U) (hb : d< b) :
    (activeSet d (sourceRowContext kind low active b).1).card=
      Fintype.card (ActivePatternIndex kind) := by
  rw [activeSet_sourceRow_exceptional hsep kind low active b hlow hactive hb]
  exact (Fintype.card_subtype (activePatternPred kind)).symm

lemma lowOnlyList_sourceRow_exceptional {d L U : ℝ} (hsep : d< L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j,low j∈ Icc 0 d) (hactive : ∀ j,active j∈ Icc L U) (hb : d< b) :
    lowOnlyList d (sourceRowContext kind low active b).1=
      Fin.cons none (fun j => if kind j=0 then some (low j) else none) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact lowOnlyList_above d _ 0 b (sourceRowContext_zero _ _ _ _) hb
  · by_cases h₀ : kind j=0
    · have he : (sourceRowContext kind low active b).1 j.succ=some (low j) := by
        rw [sourceRowContext_succ,if_pos h₀]
      simpa only [Fin.cons_succ,if_pos h₀] using lowOnlyList_some d _ j.succ (low j) he (hlow j).2
    · by_cases h₁ : kind j=1
      · have he : (sourceRowContext kind low active b).1 j.succ=some (active j) := by
          rw [sourceRowContext_succ,if_neg h₀,if_pos h₁]
        simpa only [Fin.cons_succ,if_neg h₀] using
          lowOnlyList_above d _ j.succ (active j) he (hsep.trans_le (hactive j).1)
      · have he : (sourceRowContext kind low active b).1 j.succ=none := by
          rw [sourceRowContext_succ,if_neg h₀,if_neg h₁]
        simp [Fin.cons_succ,h₀,lowOnlyList,TaggedLocal.lowList,he,TaggedLocal.tag]

lemma visibleLow_sourceRow_exceptional {d L U : ℝ} (hsep : d< L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j,low j∈ Icc 0 d) (hactive : ∀ j,active j∈ Icc L U) (hb : d< b) :
    visibleCount (lowOnlyList d (sourceRowContext kind low active b).1)=
      classCount 0 (patternRow kind) := by
  rw [lowOnlyList_sourceRow_exceptional hsep kind low active b hlow hactive hb]
  simp only [visibleCount,Finset.card_eq_sum_ones,Finset.sum_filter,
    Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,ne_eq,not_true_eq_false,
    if_false,zero_add,classCount,patternRow]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : kind j=0 <;> simp only [hj,if_pos,if_neg,reduceCtorEq,not_false_eq_true,
    not_true_eq_false]

lemma sourceRow_exceptional_other_box {d L U : ℝ} (hsep : d< L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j,low j∈ Icc 0 d) (hactive : ∀ j,active j∈ Icc L U) (hb : d< b) :
    ∀ i∈ activeSet d (sourceRowContext kind low active b).1,i≠0 →
      entryBid ((sourceRowContext kind low active b).1 i)∈ Icc L U := by
  intro i hi hi0
  obtain ⟨j,rfl⟩ := Fin.eq_succ_of_ne_zero hi0
  rw [activeSet_sourceRow_exceptional hsep kind low active b hlow hactive hb] at hi
  have hj : kind j=1 := (Finset.mem_filter.mp hi).2
  have hj0 : kind j≠0 := by simpa only [hj] using (show (1:Fin 4)≠0 by decide)
  simpa only [sourceRowContext_succ,if_neg hj0,if_pos hj,entryBid] using hactive j

theorem countReady_exceptional_of_counts {xi d L U : ℝ} (hxi : 0< xi) (_hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (hL : 0< L) (hgap : d<(1-xi)*L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j,low j∈ Icc 0 d) (hactive : ∀ j,active j∈ Icc L U) (hb : d< b)
    (e : Equiv.Perm (Fin (N+1))) (hg : activePatternGuarded xi L U c z kind) :
    countReady xi d L U z c
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) := by
  have hsep : d< L := hgap.trans (by nlinarith [mul_pos hxi hL])
  let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
  let A := activeSet d X.1
  have hcard : A.card=Fintype.card (ActivePatternIndex kind) := by
    change (activeSet d ((sourceRowContext kind low active b).1 ∘ e)).card=_
    rw [activeSet_reindex,Finset.card_map]
    exact activeSet_sourceRow_exceptional_card hsep kind low active b hlow hactive hb
  have hc₀ : capacity c A X.2.1=activePatternCapacity c kind 0 := by
    unfold capacity activePatternCapacity
    rw [hcard]
    rfl
  have hc₁ : capacity c A X.2.2=activePatternCapacity c kind 1 := by
    unfold capacity activePatternCapacity
    rw [hcard]
    rfl
  have ho (j : Fin 2) : ownerCount z A (activePatternCapacity c kind 0)
      (activePatternCapacity c kind 1) j=activePatternOwner c z kind j := by
    fin_cases j <;> simp only [ownerCount,activePatternOwner,activePatternQuota,
      activePatternGap,hcard] <;> norm_num
  have hlowcount : visibleCount (lowOnlyList d X.1)=classCount 0 (patternRow kind) := by
    change visibleCount (lowOnlyList d ((sourceRowContext kind low active b).1 ∘ e))=_
    rw [lowOnlyList_reindex,visibleCount_reindex]
    exact visibleLow_sourceRow_exceptional hsep kind low active b hlow hactive hb
  have hbad : (A\boxSet L U X.1).card≤1 := by
    have hsub : A\boxSet L U X.1⊆{e.symm 0} := by
      intro j hj
      have hjA := (Finset.mem_sdiff.mp hj).1
      have hjnot := (Finset.mem_sdiff.mp hj).2
      apply Finset.mem_singleton.mpr
      by_contra hji
      have he0 : e j≠0 := by
        intro he
        apply hji
        apply e.injective
        simpa only [Equiv.apply_symm_apply] using he
      have hbox := sourceRow_exceptional_other_box hsep kind low active b hlow hactive hb
        (e j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hjA).2⟩) he0
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hjA).2.1,hbox⟩)
    exact (Finset.card_le_card hsub).trans (by simp)
  unfold countReady
  dsimp only
  rw [hc₀,hc₁,ho 0,ho 1,hcard,hlowcount]
  refine ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2,
    ⟨activePatternGuarded_capacity_lt c z kind hg 0,
      activePatternGuarded_capacity_lt c z kind hg 1⟩,hbad⟩

def originalActiveSet (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1))) :
    Finset (Fin (N+1)) :=
  (Finset.univ.filter (activePatternPred kind)).map e.symm.toEmbedding

lemma originalActiveSet_mem (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (i : Fin (N+1)) : i∈ originalActiveSet kind e ↔ activePatternPred kind (e i) := by
  simp [originalActiveSet]

lemma originalActiveSet_card (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1))) :
    (originalActiveSet kind e).card=Fintype.card (ActivePatternIndex kind) := by
  rw [originalActiveSet,Finset.card_map]
  exact (Fintype.card_subtype (activePatternPred kind)).symm

def originalFocal (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1))) :
    originalActiveSet kind e :=
  ⟨e.symm 0,(originalActiveSet_mem kind e _).mpr (by simp [activePatternPred])⟩

def exceptionalTable (z : ℝ) (c : ℕ) (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) : TableIndex (N+1) :=
  (originalActiveSet kind e,(originalActiveSet kind e).erase (e.symm 0),
    activePatternOwner c z kind 0,activePatternOwner c z kind 1,activePatternResidual c z kind)

def originalEligible (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1))) :
    Finset (originalActiveSet kind e) :=
  Finset.univ.erase (originalFocal kind e)

lemma originalEligible_card (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1))) :
    (originalEligible kind e).card=Fintype.card (ActivePatternIndex kind)-1 := by
  rw [originalEligible,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,
    Fintype.card_coe,originalActiveSet_card]

lemma eligibleOn_exceptionalTable (z : ℝ) (c : ℕ) (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) :
    eligibleOn (exceptionalTable z c kind e).1 (exceptionalTable z c kind e).2.1=
      originalEligible kind e := eligibleOn_erase _ (originalFocal kind e)

lemma originalEligible_iff (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (i : originalActiveSet kind e) : i∈ originalEligible kind e ↔ i≠originalFocal kind e := by
  simp [originalEligible]

lemma originalEligible_ne_zero (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (i : originalEligible kind e) : e i.val.val≠0 := by
  intro h
  have he : i.val=originalFocal kind e := by
    apply Subtype.ext
    apply e.injective
    simpa only [originalFocal,Equiv.apply_symm_apply] using h
  exact ((originalEligible_iff kind e i.val).mp i.property) he

def originalRivalCoordinate (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (i : originalEligible kind e) : Fin N :=
  (Fin.eq_succ_of_ne_zero (originalEligible_ne_zero kind e i)).choose

lemma originalRivalCoordinate_spec (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (i : originalEligible kind e) : e i.val.val=(originalRivalCoordinate kind e i).succ :=
  (Fin.eq_succ_of_ne_zero (originalEligible_ne_zero kind e i)).choose_spec

lemma originalRivalCoordinate_injective (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) : Function.Injective (originalRivalCoordinate kind e) := by
  intro i j hij
  apply Subtype.ext
  apply Subtype.ext
  apply e.injective
  rw [originalRivalCoordinate_spec,originalRivalCoordinate_spec,hij]

def originalActiveBids (_kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (b : ℝ) (active : Fin N → ℝ) : Fin (N+1) → ℝ :=
  Fin.cons (α := fun _ => ℝ) b active ∘ e

lemma originalActiveBids_focal (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (b : ℝ) (active : Fin N → ℝ) : originalActiveBids kind e b active (e.symm 0)=b := by
  simp [originalActiveBids]

lemma originalActiveBids_rival (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (b : ℝ) (active : Fin N → ℝ) (i : originalEligible kind e) :
    originalActiveBids kind e b active i.val.val=active (originalRivalCoordinate kind e i) := by
  simp only [originalActiveBids,Function.comp_apply,originalRivalCoordinate_spec,Fin.cons_succ]

lemma measurable_originalActiveBids (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (b : ℝ) : Measurable (originalActiveBids kind e b) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun active : Fin N → ℝ => Fin.cons (α := fun _ => ℝ) b active (e i))
  refine Fin.cases ?_ (fun j => ?_) (e i)
  · exact measurable_const
  · exact measurable_pi_apply j

theorem tableIndex_sourceRow_exceptional {d L U : ℝ} (hsep : d< L) (z : ℝ) (c : ℕ)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j,low j∈ Icc 0 d) (hactive : ∀ j,active j∈ Icc L U)
    (hb : d< b) (hout : b∉Icc L U) (e : Equiv.Perm (Fin (N+1))) :
    tableIndex d L U z c
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b))=
      exceptionalTable z c kind e := by
  let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
  let A := activeSet d X.1
  have hA : A=originalActiveSet kind e := by
    change activeSet d ((sourceRowContext kind low active b).1 ∘ e)=_
    rw [activeSet_reindex,activeSet_sourceRow_exceptional hsep kind low active b hlow hactive hb]
    rfl
  have hcard : A.card=Fintype.card (ActivePatternIndex kind) := by rw [hA,originalActiveSet_card]
  have hboxother : ∀ j∈ A,j≠e.symm 0 → entryBid (X.1 j)∈ Icc L U := by
    intro j hj hji
    have he0 : e j≠0 := by
      intro he
      exact hji (by apply e.injective; simpa using he)
    exact sourceRow_exceptional_other_box hsep kind low active b hlow hactive hb
      (e j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩) he0
  have hiA : e.symm 0∈ A := by rw [hA]; exact (originalFocal kind e).property
  have houti : entryBid (X.1 (e.symm 0))∉Icc L U := by simpa [X,NativeContinuation.reindexContext, entryBid] using hout
  have hsmall : (A\boxSet L U X.1).card≤1 := by
    apply (Finset.card_le_card (show A\boxSet L U X.1⊆{e.symm 0} from ?_)).trans (by simp)
    intro j hj
    apply Finset.mem_singleton.mpr
    by_contra hji
    have hjA := (Finset.mem_sdiff.mp hj).1
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp hjA).2.1,hboxother j hjA hji⟩)
  have hB : boxSet L U X.1∩A=A.erase (e.symm 0) :=
    box_eligible_eq_erase d L U X _ hiA houti hsmall
  have hc₀ : capacity c A X.2.1=activePatternCapacity c kind 0 := by
    unfold capacity activePatternCapacity
    rw [hcard]
    rfl
  have hc₁ : capacity c A X.2.2=activePatternCapacity c kind 1 := by
    unfold capacity activePatternCapacity
    rw [hcard]
    rfl
  have ho (j : Fin 2) : ownerCount z A (activePatternCapacity c kind 0)
      (activePatternCapacity c kind 1) j=activePatternOwner c z kind j := by
    fin_cases j <;> simp only [ownerCount,activePatternOwner,activePatternQuota,
      activePatternGap,hcard] <;> norm_num
  change (A,boxSet L U X.1∩A,
    ownerCount z A (capacity c A X.2.1) (capacity c A X.2.2) 0,
    ownerCount z A (capacity c A X.2.1) (capacity c A X.2.2) 1,
    min (capacity c A X.2.1) (capacity c A X.2.2)-exclusiveQuota z A.card)=_
  rw [hB,hc₀,hc₁,ho 0,ho 1,hcard,hA]
  rfl

lemma sourceRow_exceptional_active_bids {d L U : ℝ} (_hsep : d< L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (_hlow : ∀ j,low j∈ Icc 0 d) (_hactive : ∀ j,active j∈ Icc L U) (_hb : d< b)
    (e : Equiv.Perm (Fin (N+1))) :
    ∀ i∈ originalActiveSet kind e,
      entryBid ((NativeContinuation.reindexContext e (sourceRowContext kind low active b)).1 i)=
        originalActiveBids kind e b active i := by
  intro i hi
  have hp := (originalActiveSet_mem kind e i).mp hi
  change entryBid ((sourceRowContext kind low active b).1 (e i))=Fin.cons (α := fun _ => ℝ) b active (e i)
  revert hp
  refine Fin.cases ?_ (fun j => ?_) (e i)
  · intro _
    rfl
  · intro hj
    have hj1 : kind j=1 := hj
    have hj0 : kind j≠0 := by simpa only [hj1] using (show (1:Fin 4)≠0 by decide)
    simp only [sourceRowContext_succ,if_neg hj0,if_pos hj1,entryBid,Fin.cons_succ]

def exceptionalPatternGuard (xi L U : ℝ) (c : ℕ) (z : ℝ) (kind : Fin N → Fin 4) : Prop :=
  activePatternGuarded xi L U c z kind ∧
    ClippedCountGuard xi L U
      (Fintype.card (ActivePatternIndex kind)-
        (activePatternOwner c z kind 0+activePatternOwner c z kind 1))
      (activePatternResidual c z kind)

theorem validation_accepts_sourceRow_exceptional {xi d L U : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j,low j∈ Icc 0 d) (hactive : ∀ j,active j∈ Icc L U)
    (hb : d< b) (hout : b∉Icc L U) (e : Equiv.Perm (Fin (N+1)))
    (hg : exceptionalPatternGuard xi L U c z kind) :
    useProposal xi d L U z c μ
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) := by
  have hsep : d< L := hgap.trans (by nlinarith [mul_pos hxi hL])
  let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
  have hready := countReady_exceptional_of_counts hxi hxi1 z c hL hgap kind low active b
    hlow hactive hb e hg.1
  have hi : e.symm 0∈ activeSet d X.1 := by
    change e.symm 0∈ activeSet d ((sourceRowContext kind low active b).1 ∘ e)
    simp only [activeSet,Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply,
      Equiv.apply_symm_apply,sourceRowContext_zero,entryBid]
    exact ⟨by simp,hb⟩
  have hti := tableIndex_sourceRow_exceptional hsep z c kind low active b hlow hactive hb hout e
  have hG : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2 := by
    rw [hti]
    simpa only [exceptionalTable,originalActiveSet_card] using hg.2
  exact validation_accepts_exceptional hxi hxi1 d L U z c μ hd hL hLU hgap X hready
    (e.symm 0) hi (by simpa [X,NativeContinuation.reindexContext, entryBid] using hout) hG

def exceptionalPatternMenuError (xi L U h0 : ℝ) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) : ℝ :=
  let n := Fintype.card (ActivePatternIndex kind)-
    (activePatternOwner c z kind 0+activePatternOwner c z kind 1)-1
  U*|finiteReceiptFactor xi n (activePatternResidual c z kind)-h0|+
    U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ)

def exceptionalGuardError (h delta deltaeq deltaclip : ℝ) (N : ℕ) : ℝ :=
  activeGuardExceptionError h delta deltaeq N+8*Real.exp (-(N:ℝ)*deltaclip^2/2)

lemma exceptionalGuardError_tendsto_zero {h delta deltaeq deltaclip : ℝ}
    (hh : 0< h) (hd : 0< delta) (heq : 0< deltaeq) (hc : 0< deltaclip) :
    Tendsto (exceptionalGuardError h delta deltaeq deltaclip) atTop (nhds 0) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => 8*Real.exp (-(N:ℝ)*deltaclip^2/2)) atTop (nhds 0) := by
    have hp := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hn.const_mul_atTop (by positivity : 0< deltaclip^2/2))
    convert! hp.const_mul 8 using 1
    · funext N
      congr 2
      ring
    · ring
  convert! (activeGuardExceptionError_tendsto_zero hh hd heq).add he using 1
  simp only [add_zero]

theorem exists_eventual_exceptional_pattern_bound
    (s a h rho z xi L U : ℝ)
    (hs : 0< s) (ha : 0< a) (hh : 0< h) (hsum : s+a+h=1)
    (hz0 : 0≤ z) (hz1 : z<1) (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hLU : L≤ U) (hlower : h/2< rho) (hupper : rho< a+h/2)
    (hq0 : 0< sourceExposure a h rho z) (hq1 : sourceExposure a h rho z<1)
    (hboxlo : (1-xi)*U<(1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U< L)
    (c : ℕ → ℕ) (hcap : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (tau : ℝ) (htau : 0< tau) :
    ∃ delta deltaeq deltaclip : ℝ,0< delta ∧ 0< deltaeq ∧ 0< deltaclip ∧
      ∀ᶠ N : ℕ in atTop,∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G),
      let C := categoryLaw s a h hs.le ha.le hh.le hsum G
      (CommonList.iid C N).prob (fun kind =>
        ¬(exceptionalPatternGuard xi L U (c (N+1)) z kind ∧
          exceptionalPatternMenuError xi L U (1-xi*sourceExposure a h rho z)
            (c (N+1)) z kind< tau))≤ exceptionalGuardError h delta deltaeq deltaclip N := by
  obtain ⟨delta,deltaeq,hd,_hds,heq,hactive⟩ := exists_eventual_activePattern_guard_bound
    s a h rho z xi L U hs ha hh hsum hz0 hz1 hxi hxi1 hL hLU hlower hupper
    hq0 hq1 hboxlo hboxhi c hcap
  obtain ⟨deltaclip,hclip,hclipped⟩ := eventually_source_clipped_guards_and_error
    a h rho z xi L U ha hz0 hz1 hxi hxi1 hL hLU hlower hupper
    hq0 hq1 hboxlo hboxhi c hcap tau htau
  have hclipN := (tendsto_add_atTop_nat 1).eventually hclipped
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hprefix : ∀ᶠ N : ℕ in atTop,(1:ℝ)≤(N:ℝ)*deltaclip/2 := by
    have ht : Tendsto (fun N : ℕ => (N:ℝ)*deltaclip/2) atTop atTop := by
      convert! hn.const_mul_atTop (half_pos hclip) using 1
      funext N
      ring
    exact ht.eventually_ge_atTop 1
  refine ⟨delta,deltaeq,deltaclip,hd,heq,hclip,?_⟩
  filter_upwards [hactive,hclipN,hprefix] with N hactN hclipN hprefixN
  intro G hG
  letI := hG
  let C := categoryLaw s a h hs.le ha.le hh.le hsum G
  have hpoint (kind : Fin N → Fin 4)
      (hg : activePatternGuarded xi L U (c (N+1)) z kind)
      (hgood : ¬activePatternCountException C deltaclip kind) :
      exceptionalPatternGuard xi L U (c (N+1)) z kind ∧
        exceptionalPatternMenuError xi L U (1-xi*sourceExposure a h rho z)
          (c (N+1)) z kind< tau := by
    have hclose (k : Fin 4) :
        |(fullCategoryCount activeFocalPrefix kind k:ℝ)-(N+1:ℕ)*C.mass k|<
          (N+1:ℕ)*deltaclip := by
      have h := lt_of_not_ge (fun he => hgood ⟨k,he⟩)
      simpa only [fullCategoryCount,Nat.cast_add] using h
    have hA : |(Fintype.card (ActivePatternIndex kind):ℝ)-(N+1:ℕ)*a|≤
        (N+1:ℕ)*deltaclip := by
      simpa [C,categoryLaw_mass,activePattern_count_active] using (hclose 1).le
    have hH₀ : |(activePatternUpper kind 0:ℝ)-(N+1:ℕ)*(h/2)|≤
        (N+1:ℕ)*deltaclip := by
      have h := (hclose 2).le
      rw [show fullCategoryCount activeFocalPrefix kind 2 = activePatternUpper kind 0 from activePattern_count_upper kind 0] at h
      simpa [C,categoryLaw_mass] using h
    have hH₁ : |(activePatternUpper kind 1:ℝ)-(N+1:ℕ)*(h/2)|≤
        (N+1:ℕ)*deltaclip := by
      have h := (hclose 3).le
      rw [show fullCategoryCount activeFocalPrefix kind 3 = activePatternUpper kind 1 from activePattern_count_upper kind 1] at h
      simpa [C,categoryLaw_mass] using h
    have hp := hclipN (Fintype.card (ActivePatternIndex kind))
      (activePatternUpper kind 0) (activePatternUpper kind 1) hA hH₀ hH₁
    have howners := activePatternOwner_sum_of_ne (c (N+1)) z kind hg.2.1
    have hgclip : ClippedCountGuard xi L U
        (Fintype.card (ActivePatternIndex kind)-
          (activePatternOwner (c (N+1)) z kind 0+activePatternOwner (c (N+1)) z kind 1))
        (activePatternResidual (c (N+1)) z kind) := by
      rw [howners]
      exact hp.2.2.2.2.2.1
    refine ⟨⟨hg,hgclip⟩,?_⟩
    unfold exceptionalPatternMenuError
    rw [howners]
    exact hp.2.2.2.2.2.2
  have hsub : (CommonList.iid C N).prob (fun kind =>
      ¬(exceptionalPatternGuard xi L U (c (N+1)) z kind ∧
        exceptionalPatternMenuError xi L U (1-xi*sourceExposure a h rho z)
          (c (N+1)) z kind< tau))≤
      (CommonList.iid C N).prob (fun kind =>
        ¬activePatternGuarded xi L U (c (N+1)) z kind ∨ activePatternCountException C deltaclip kind) := by
    apply FiniteLaw.prob_mono
    intro kind hbad
    by_cases hg : activePatternGuarded xi L U (c (N+1)) z kind
    · right
      by_contra hn
      exact hbad (hpoint kind hg hn)
    · exact Or.inl hg
  have hu := (CommonList.iid C N).prob_union_le
    (fun kind => ¬activePatternGuarded xi L U (c (N+1)) z kind)
    (activePatternCountException C deltaclip)
  have hb := forced_fractional_count_exception_le C activeFocalPrefix N hclip.le
    (by simpa only [Nat.cast_one] using hprefixN)
  have ha' := (hactN G inferInstance).2
  exact hsub.trans (hu.trans (add_le_add ha' hb))

theorem sourceRow_low_integral_exceptional_table {xi d L U : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (z : ℝ) (c : ℕ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnoatoms : ∀ b,μ {b}=0)
    (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U) (hgap : d<(1-xi)*L)
    (hμ : ∀ᵐ b ∂μ,b∈ Icc 0 d)
    (kind : Fin N → Fin 4) (active : Fin N → ℝ) (b : ℝ)
    (hactive : ∀ j,active j∈ Icc L U) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) (f : Fin 3 → ℝ) :
    (∫ low : Fin N → ℝ,
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ)
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
        (e.symm 0)).expect f ∂Measure.pi (fun _ : Fin N => μ))=
      ∫ u : unitInterval,
        ((tableLaw xi (exceptionalTable z c kind e) 0
          (originalActiveBids kind e b active) u).prod
          (tableLaw xi (exceptionalTable z c kind e) 1
            (originalActiveBids kind e b active) u)).expect
          (fun ST => f (focalCopy ST (e.symm 0))) ∂volume := by
  let X := fun low : Fin N → ℝ => NativeContinuation.reindexContext e
    (sourceRowContext kind low active b)
  let T := exceptionalTable z c kind e
  let F := fun u : unitInterval =>
    ((tableLaw xi T 0 (originalActiveBids kind e b active) u).prod
      (tableLaw xi T 1 (originalActiveBids kind e b active) u)).expect
      (fun ST => f (focalCopy ST (e.symm 0)))
  have hsep : d< L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hlowcount := hguard.1.2.2.2.2.2
  have hlows : ∀ᵐ low ∂Measure.pi (fun _ : Fin N => μ),∀ j,low j∈ Icc 0 d :=
    ae_all_iff.mpr (fun j =>
      (measurePreserving_eval (fun _ : Fin N => μ) j).quasiMeasurePreserving.ae hμ)
  have hF : Measurable F := measurable_table_pair_expect hxi hxi1 T _ _
  have he : ∀ᵐ low ∂Measure.pi (fun _ : Fin N => μ),
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ) (X low)
        (e.symm 0)).expect f=F (maskedLowSeed μ kind hlowcount low) := by
    filter_upwards [hlows] with low hlow
    have hp := validation_accepts_sourceRow_exceptional hxi hxi1 z c μ hd hL hLU hgap
      kind low active b hlow hactive hb hout e hguard
    have hT : tableIndex d L U z c (X low)=T :=
      tableIndex_sourceRow_exceptional hsep z c kind low active b hlow hactive hb hout e
    have hseed : (observedLowMinimumSeed d μ (X low).1).getD 0=
        maskedLowSeed μ kind hlowcount low := by
      change (seedOnList μ (lowOnlyList d
        ((sourceRowContext kind low active b).1 ∘ e))).getD 0=_
      rw [lowOnlyList_reindex,
        lowOnlyList_sourceRow_exceptional hsep kind low active b hlow hactive hb]
      exact congrArg (fun o : Option unitInterval => o.getD 0)
        (maskedLowSeed_formula μ kind hlowcount e low)
    have hbid : ∀ i∈ T.1,entryBid ((X low).1 i)=originalActiveBids kind e b active i :=
      sourceRow_exceptional_active_bids hsep kind low active b hlow hactive hb e
    have hlaw (j : Fin 2) : proposalLaw xi d L U z c μ j (X low)=
        tableLaw xi T j (originalActiveBids kind e b active)
          (maskedLowSeed μ kind hlowcount low) := by
      unfold proposalLaw
      rw [hT,hseed]
      exact tableLaw_congr_active xi T j _ _ _ hbid
    rw [privateContextLaw_expect_proposal hxi hxi1 d L U z c μ (X low) hp,
      hlaw 0,hlaw 1]
  calc
    _ = ∫ low : Fin N → ℝ,F (maskedLowSeed μ kind hlowcount low)
        ∂Measure.pi (fun _ : Fin N => μ) := integral_congr_ae he
    _ = ∫ u : unitInterval,F u ∂volume := by
      rw [←maskedLowSeed_law μ hnoatoms kind hlowcount]
      exact (integral_map (measurable_maskedLowSeed μ kind hlowcount).aemeasurable
        hF.aestronglyMeasurable).symm

lemma tableTargetQ_congr_active (xi : ℝ) (T : TableIndex (N+1))
    (b b' : Fin (N+1) → ℝ) (u : unitInterval) (i : T.1)
    (hb : ∀ j∈ T.1,b j=b' j) :
    tableTargetQ xi T b u i=tableTargetQ xi T b' u i := by
  unfold tableTargetQ
  rw [tableOwners_congr_active T.1 T.2.1 T.2.2.1 T.2.2.2.1 b b' u hb]
  have he : (fun j : T.1 => b j)=(fun j : T.1 => b' j) :=
    funext (fun j => hb j j.property)
  rw [he]

private theorem originalEligible_nonempty_of_guard {xi L U : ℝ} {c : ℕ} {z : ℝ}
    (kind : Fin N→Fin 4) (e : Equiv.Perm (Fin (N+1)))
    (hg : exceptionalPatternGuard xi L U c z kind) : Nonempty (originalEligible kind e) := by
  have hpos := hg.1.2.2.1
  have hD := hg.2.1
  obtain ⟨j,hj⟩ := Finset.card_pos.mp
    (show 0 < (originalEligible kind e).card by rw [originalEligible_card]; omega)
  exact ⟨⟨j,hj⟩⟩

private theorem owner_test_carrier_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C D : Finset ι) [Nonempty C] [Nonempty D] (hCD : C=D)
    (xi : ℝ) (K0 K1 r : ℕ) (bid : ι→ℝ) (b : ℝ) (F : ℝ→ℝ) :
    (sourceOwnersLaw (fun j : C => bid j) K0 K1).expect
      (fun AB => F (canonicalExceptionalQ xi r b (fun j : C => bid j) AB)) =
    (sourceOwnersLaw (fun j : D => bid j) K0 K1).expect
      (fun AB => F (canonicalExceptionalQ xi r b (fun j : D => bid j) AB)) := by
  subst D
  rfl

theorem exceptionalTable_common_owner_test {xi d L U : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (z : ℝ) (c : ℕ) (_hd : 0≤ d)
    (_hL : 0< L) (_hLU : L≤ U) (_hgap : d<(1-xi)*L)
    (kind : Fin N → Fin 4) (active : Fin N → ℝ) (b : ℝ)
    (_hactive : ∀ j,active j∈ Icc L U) (_hb : d< b) (_hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) (F : ℝ → ℝ) :
    let C := originalEligible kind e
    letI : Nonempty C := originalEligible_nonempty_of_guard kind e hguard
    (∫ u : unitInterval,F (tableTargetQ xi (exceptionalTable z c kind e)
      (originalActiveBids kind e b active) u (originalFocal kind e)) ∂volume)=
      (sourceOwnersLaw (fun j : C => active (originalRivalCoordinate kind e j))
        (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)).expect
        (fun AB => F (canonicalExceptionalQ xi (activePatternResidual c z kind) b
          (fun j : C => active (originalRivalCoordinate kind e j)) AB)) := by
  dsimp only [exceptionalTable]
  let T := exceptionalTable z c kind e
  have hA : 2≤ T.1.card := by
    simpa only [T,exceptionalTable,originalActiveSet_card] using hguard.1.1
  have hD := hguard.2.1
  have hKpos := hguard.1.2.2.1
  have hCsize : 2≤(eligibleOn T.1 T.2.1).card := by
    change 2 ≤ (eligibleOn (originalActiveSet kind e) ((originalActiveSet kind e).erase (e.symm 0))).card
    rw [show eligibleOn (originalActiveSet kind e) ((originalActiveSet kind e).erase (e.symm 0))=
      originalEligible kind e from eligibleOn_exceptionalTable z c kind e,originalEligible_card]
    omega
  have hK : T.2.2.1+T.2.2.2.1≤(eligibleOn T.1 T.2.1).card := by
    change activePatternOwner c z kind 0+activePatternOwner c z kind 1 ≤
      (eligibleOn (originalActiveSet kind e) ((originalActiveSet kind e).erase (e.symm 0))).card
    rw [show eligibleOn (originalActiveSet kind e) ((originalActiveSet kind e).erase (e.symm 0))=
      originalEligible kind e from eligibleOn_exceptionalTable z c kind e,originalEligible_card]
    omega
  have he := tableTargetQ_uniform_common_reindex hxi hxi1 T
    (originalActiveBids kind e b active) (originalFocal kind e) hA rfl hCsize hK F
  dsimp only [T,exceptionalTable] at he
  have hbid : (fun j : originalEligible kind e => originalActiveBids kind e b active j.val.val)=
      (fun j : originalEligible kind e => active (originalRivalCoordinate kind e j)) := by
    funext j
    exact originalActiveBids_rival kind e b active j
  have hCD : eligibleOn (originalActiveSet kind e) ((originalActiveSet kind e).erase (e.symm 0))=
      originalEligible kind e := eligibleOn_exceptionalTable z c kind e
  letI : Nonempty (originalEligible kind e) := originalEligible_nonempty_of_guard kind e hguard
  letI : Nonempty (eligibleOn (originalActiveSet kind e) ((originalActiveSet kind e).erase (e.symm 0))) := by
    rw [hCD]
    infer_instance
  have htransport := owner_test_carrier_congr
    (eligibleOn (originalActiveSet kind e) ((originalActiveSet kind e).erase (e.symm 0)))
    (originalEligible kind e) hCD xi (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)
    (activePatternResidual c z kind) (fun j : originalActiveSet kind e =>
      originalActiveBids kind e b active j) b F
  have hbf : originalActiveBids kind e b active (originalFocal kind e)=b :=
    originalActiveBids_focal kind e b active
  rw [hbf] at he
  have he' := he.trans htransport
  simpa only [hbid] using he'

lemma tableTargetQ_index_congr (xi : ℝ) (T T' : TableIndex (N+1))
    (hT : T=T') (b : Fin (N+1)→ℝ) (u : unitInterval) (i : T.1) (i' : T'.1)
    (hi : (i:Fin (N+1))=(i':Fin (N+1))) :
    tableTargetQ xi T b u i=tableTargetQ xi T' b u i' := by
  subst T'
  have hii : i=i' := Subtype.ext hi
  subst i'
  rfl

theorem exceptionalTable_pair_payoffs {xi d L U : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (z : ℝ) (c : ℕ) (hd : 0≤ d)
    (hL : 0< L) (hLU : L≤ U) (hgap : d<(1-xi)*L)
    (kind : Fin N → Fin 4) (active : Fin N → ℝ) (b : ℝ)
    (hactive : ∀ j,active j∈ Icc L U) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) (u : unitInterval) (eta v : ℝ) :
    let T := exceptionalTable z c kind e
    let P := (tableLaw xi T 0 (originalActiveBids kind e b active) u).prod
      (tableLaw xi T 1 (originalActiveBids kind e b active) u)
    let q := tableTargetQ xi T (originalActiveBids kind e b active) u (originalFocal kind e)
    P.expect (singletonPayoff v b (e.symm 0))=q*(v-b) ∧
      P.expect (broadcastPayoff eta v b (e.symm 0))=independentTwo eta v b q := by
  dsimp only
  let X := NativeContinuation.reindexContext e
    (sourceRowContext kind (fun _ => 0) active b)
  have hsep : d< L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hzero : ∀ _ : Fin N,(0:ℝ)∈ Icc 0 d := fun _ => ⟨le_rfl,hd⟩
  have hT : tableIndex d L U z c X=exceptionalTable z c kind e :=
    tableIndex_sourceRow_exceptional hsep z c kind (fun _ => 0) active b hzero hactive hb hout e
  have hA : activeSet d X.1=originalActiveSet kind e := congrArg Prod.fst hT
  let i : activeSet d X.1 := ⟨e.symm 0,by rw [hA]; exact (originalFocal kind e).property⟩
  have hi : entryBid (X.1 i)=b := by
    simp only [X,i,NativeContinuation.reindexContext,Function.comp_apply,
      Equiv.apply_symm_apply,sourceRowContext_zero,entryBid]
  have hready := countReady_exceptional_of_counts hxi hxi1 z c hL hgap
    kind (fun _ => 0) active b hzero hactive hb e hguard.1
  have hG : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2 := by
    rw [hT]
    simpa only [exceptionalTable,originalActiveSet_card] using hguard.2
  have hbid : ∀ j∈ originalActiveSet kind e,entryBid (X.1 j)=
      originalActiveBids kind e b active j :=
    sourceRow_exceptional_active_bids hsep kind (fun _ => 0) active b hzero hactive hb e
  have hlaw (j : Fin 2) : tableLaw xi (tableIndex d L U z c X) j
      (fun a => entryBid (X.1 a)) u=
      tableLaw xi (exceptionalTable z c kind e) j (originalActiveBids kind e b active) u := by
    rw [hT]
    exact tableLaw_congr_active xi _ j _ _ u hbid
  have hq : tableTargetQ xi (tableIndex d L U z c X)
      (fun a => entryBid (X.1 a)) u i=
      tableTargetQ xi (exceptionalTable z c kind e)
        (originalActiveBids kind e b active) u (originalFocal kind e) := by
    have hbid' : ∀ a ∈ (tableIndex d L U z c X).1,
        entryBid (X.1 a) = originalActiveBids kind e b active a := by
      intro a ha
      apply hbid a
      change a ∈ activeSet d X.1 at ha
      rwa [hA] at ha
    have hh := tableTargetQ_congr_active xi (tableIndex d L U z c X)
      (fun a => entryBid (X.1 a)) (originalActiveBids kind e b active) u i hbid'
    exact hh.trans (tableTargetQ_index_congr xi _ _ hT _ u i (originalFocal kind e) rfl)
  have hs := tableLaw_exceptional_singleton_payoff hxi hxi1 d L U z c hd hL hLU hgap
    X hready i (by simpa only [hi] using hout) hG u v
  have ht := tableLaw_exceptional_broadcast_payoff hxi hxi1 d L U z c hd hL hLU hgap
    X hready i (by simpa only [hi] using hout) hG u eta v
  rw [hlaw 0,hlaw 1,hi,hq] at hs ht
  exact ⟨hs,ht⟩

theorem sourceRow_low_integral_exceptional_menus {xi d L U : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (z : ℝ) (c : ℕ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnoatoms : ∀ b,μ {b}=0)
    (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U) (hgap : d<(1-xi)*L)
    (hμ : ∀ᵐ b ∂μ,b∈ Icc 0 d)
    (kind : Fin N → Fin 4) (active : Fin N → ℝ) (eta v b : ℝ)
    (hactive : ∀ j,active j∈ Icc L U) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    let C := originalEligible kind e
    letI : Nonempty C := by
      have hpos := hguard.1.2.2.1
      have hD := hguard.2.1
      obtain ⟨j,hj⟩ := Finset.card_pos.mp
        (show 0< C.card by dsimp [C]; rw [originalEligible_card]; omega)
      exact ⟨⟨j,hj⟩⟩
    let Q := sourceOwnersLaw (fun j : C => active (originalRivalCoordinate kind e j))
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)
    let q := fun AB => canonicalExceptionalQ xi (activePatternResidual c z kind) b
      (fun j : C => active (originalRivalCoordinate kind e j)) AB
    (∫ low : Fin N → ℝ,
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ)
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
        (e.symm 0)).expect (fun k => ((v-b)/2)*(k.val:ℝ))
      ∂Measure.pi (fun _ : Fin N => μ))=Q.expect (fun AB => q AB*(v-b)) ∧
    (∫ low : Fin N → ℝ,
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ)
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
        (e.symm 0)).expect (fun k => realizedPayoff eta v b k.val)
      ∂Measure.pi (fun _ : Fin N => μ))=Q.expect (fun AB => independentTwo eta v b (q AB)) := by
  dsimp only
  have hs (u : unitInterval) := exceptionalTable_pair_payoffs hxi hxi1 z c hd hL hLU hgap
    kind active b hactive hb hout hguard e u eta v
  constructor
  · rw [sourceRow_low_integral_exceptional_table hxi hxi1 z c μ hnoatoms hd hL hLU hgap hμ
      kind active b hactive hb hout hguard e]
    simp_rw [singleton_focalCopy]
    calc
      _ = ∫ u : unitInterval,
          tableTargetQ xi (exceptionalTable z c kind e) (originalActiveBids kind e b active)
            u (originalFocal kind e)*(v-b) ∂volume := integral_congr_ae (ae_of_all _ (fun u => (hs u).1))
      _ = _ := exceptionalTable_common_owner_test hxi hxi1 z c hd hL hLU hgap
        kind active b hactive hb hout hguard e (fun q => q*(v-b))
  · rw [sourceRow_low_integral_exceptional_table hxi hxi1 z c μ hnoatoms hd hL hLU hgap hμ
      kind active b hactive hb hout hguard e]
    simp_rw [realizedPayoff_focalCopy]
    calc
      _ = ∫ u : unitInterval,
          independentTwo eta v b (tableTargetQ xi (exceptionalTable z c kind e)
            (originalActiveBids kind e b active) u (originalFocal kind e)) ∂volume :=
          integral_congr_ae (ae_of_all _ (fun u => (hs u).2))
      _ = _ := exceptionalTable_common_owner_test hxi hxi1 z c hd hL hLU hgap
        kind active b hactive hb hout hguard e (independentTwo eta v b)

lemma measurable_exceptional_owner_test {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1) (K₀ K₁ r : ℕ) (b : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) :
    Measurable (fun x : J → ℝ => (sourceOwnersLaw x K₀ K₁).expect
      (fun AB => F (canonicalExceptionalQ xi r b x AB))) := by
  unfold FiniteLaw.expect
  apply Finset.measurable_sum
  intro AB _
  exact (measurable_sourceOwnersLaw_mass K₀ K₁ AB).mul
    (hF.comp (measurable_canonicalExceptionalQ hxi hxi1 r b AB))

lemma measurable_independentTwo (eta v b : ℝ) : Measurable (independentTwo eta v b) := by
  unfold independentTwo
  fun_prop

theorem patternExceptional_menus_eq {xi d L U : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (z : ℝ) (c : ℕ)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hnoatoms : ∀ b,μ {b}=0) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (hμ : ∀ᵐ b ∂μ,b∈ Icc 0 d)
    (hB : ∀ᵐ b ∂B,b∈ Icc L U)
    (kind : Fin N → Fin 4) (eta v b : ℝ) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    let C := originalEligible kind e
    letI : Nonempty C := by
      have hpos := hguard.1.2.2.1
      have hD := hguard.2.1
      obtain ⟨j,hj⟩ := Finset.card_pos.mp
        (show 0< C.card by dsimp [C]; rw [originalEligible_card]; omega)
      exact ⟨⟨j,hj⟩⟩
    let P := contextPolicy hxi hxi1 d L U z c μ
    patternSingletonMenu P e μ B v b kind=
      ∫ x : C → ℝ,(sourceOwnersLaw x (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1)).expect
        (fun AB => canonicalExceptionalQ xi (activePatternResidual c z kind) b x AB*(v-b))
        ∂Measure.pi (fun _ : C => B) ∧
    patternBroadcastMenu P e μ B eta v b kind=
      ∫ x : C → ℝ,(sourceOwnersLaw x (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1)).expect
        (fun AB => independentTwo eta v b
          (canonicalExceptionalQ xi (activePatternResidual c z kind) b x AB))
        ∂Measure.pi (fun _ : C => B) := by
  dsimp only
  let C := originalEligible kind e
  have hpos := hguard.1.2.2.1
  have hD := hguard.2.1
  letI : Nonempty C := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp
      (show 0< C.card by dsimp [C]; rw [originalEligible_card]; omega)
    exact ⟨⟨j,hj⟩⟩
  let proj := fun active : Fin N → ℝ => fun j : C => active (originalRivalCoordinate kind e j)
  have hmproj : Measurable proj := measurable_pi_lambda _
    (fun j => measurable_pi_apply (originalRivalCoordinate kind e j))
  have hproj := iid_coordinate_restriction_law B (originalRivalCoordinate kind e)
    (originalRivalCoordinate_injective kind e)
  have hvec : ∀ᵐ active : Fin N → ℝ ∂Measure.pi (fun _ : Fin N => B),
      ∀ j,active j∈ Icc L U :=
    ae_all_iff.mpr (fun j =>
      (measurePreserving_eval (fun _ : Fin N => B) j).quasiMeasurePreserving.ae hB)
  have hchange (F : ℝ → ℝ) (hF : Measurable F) :
      (∫ active : Fin N → ℝ,(sourceOwnersLaw (proj active) (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1)).expect (fun AB =>
          F (canonicalExceptionalQ xi (activePatternResidual c z kind) b (proj active) AB))
        ∂Measure.pi (fun _ : Fin N => B))=
      ∫ x : C → ℝ,(sourceOwnersLaw x (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1)).expect
        (fun AB => F (canonicalExceptionalQ xi (activePatternResidual c z kind) b x AB))
        ∂Measure.pi (fun _ : C => B) := by
    rw [←hproj]
    exact (integral_map hmproj.aemeasurable
      (measurable_exceptional_owner_test hxi hxi1 _ _ _ b F hF).aestronglyMeasurable).symm
  constructor
  · unfold patternSingletonMenu
    calc
      _ = ∫ active : Fin N → ℝ,
          (sourceOwnersLaw (proj active) (activePatternOwner c z kind 0)
            (activePatternOwner c z kind 1)).expect
            (fun AB => canonicalExceptionalQ xi (activePatternResidual c z kind) b (proj active) AB*(v-b))
          ∂Measure.pi (fun _ : Fin N => B) := by
          apply integral_congr_ae
          filter_upwards [hvec] with active ha
          exact (sourceRow_low_integral_exceptional_menus hxi hxi1 z c μ hnoatoms hd hL hLU hgap hμ
            kind active eta v b ha hb hout hguard e).1
      _ = _ := hchange (fun q => q*(v-b)) (measurable_id.mul_const _)
  · unfold patternBroadcastMenu
    calc
      _ = ∫ active : Fin N → ℝ,
          (sourceOwnersLaw (proj active) (activePatternOwner c z kind 0)
            (activePatternOwner c z kind 1)).expect
            (fun AB => independentTwo eta v b
              (canonicalExceptionalQ xi (activePatternResidual c z kind) b (proj active) AB))
          ∂Measure.pi (fun _ : Fin N => B) := by
          apply integral_congr_ae
          filter_upwards [hvec] with active ha
          exact (sourceRow_low_integral_exceptional_menus hxi hxi1 z c μ hnoatoms hd hL hLU hgap hμ
            kind active eta v b ha hb hout hguard e).2
      _ = _ := hchange (independentTwo eta v b) (measurable_independentTwo eta v b)

theorem patternExceptional_menus_le {xi eta d L U h0 v b M1 : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi) (hv : 0< v)
    (z : ℝ) (c : ℕ) (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hnoatoms : ∀ b,μ {b}=0) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (hμ : ∀ᵐ b ∂μ,b∈ Icc 0 d) (hB : ∀ᵐ b ∂B,b∈ Icc L U)
    (hh0 : |h0|≤1) (kind : Fin N → Fin 4) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1)))
    (hM1 : ∀ q∈ Icc (0:ℝ) 1,outsideOneAt xi v (h0/reciprocalMean B) q≤ M1) :
    let P := contextPolicy hxi hxi1 d L U z c μ
    let err := exceptionalPatternMenuError xi L U h0 c z kind
    patternSingletonMenu P e μ B v b kind≤ M1+err/(1-xi) ∧
      patternBroadcastMenu P e μ B eta v b kind≤ outsideTwo v (h0/reciprocalMean B)+2*err := by
  dsimp only
  let C := originalEligible kind e
  have hKpos := hguard.1.2.2.1
  have hD := hguard.2.1
  have hCcard : C.card=Fintype.card (ActivePatternIndex kind)-1 := originalEligible_card kind e
  have hN : 2≤ C.card := by rw [hCcard]; omega
  letI : Nonempty C := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0< C.card by omega)
    exact ⟨⟨j,hj⟩⟩
  have hK : activePatternOwner c z kind 0+activePatternOwner c z kind 1< C.card := by
    rw [hCcard]
    omega
  have hn : C.card-(activePatternOwner c z kind 0+activePatternOwner c z kind 1)=
      Fintype.card (ActivePatternIndex kind)-
        (activePatternOwner c z kind 0+activePatternOwner c z kind 1)-1 := by omega
  have hg : ClippedCountGuard xi L U
      (Fintype.card C-(activePatternOwner c z kind 0+activePatternOwner c z kind 1)+1)
      (activePatternResidual c z kind) := by
    have he : Fintype.card C-(activePatternOwner c z kind 0+activePatternOwner c z kind 1)+1=
        Fintype.card (ActivePatternIndex kind)-
          (activePatternOwner c z kind 0+activePatternOwner c z kind 1) := by
      rw [Fintype.card_coe,hCcard]
      omega
    rw [he]
    exact hguard.2
  have hm := primitive_excluded_owner_menus (ι:=C) B hxi hxi1 heta hv (hd.trans_lt hb)
    hL hLU hB hh0 (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)
    (activePatternResidual c z kind) (by simpa only [Fintype.card_coe] using hN)
    (by simpa only [Fintype.card_coe] using hK) hg hM1
  have he := patternExceptional_menus_eq hxi hxi1 z c μ B hnoatoms hd hL hLU hgap hμ hB
    kind eta v b hb hout hguard e
  rw [he.1,he.2]
  simpa only [Fintype.card_coe,hn,exceptionalPatternMenuError] using hm

lemma finite_menu_upper {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (good : Ω → Prop) (f : Ω → ℝ) (target K eps : ℝ)
    (htarget : 0≤ target) (heps : 0≤ eps) (hK : ∀ k,f k≤ K)
    (hgood : ∀ k,good k → f k≤ target+eps) :
    P.expect f≤ target+eps+K*P.prob (fun k => ¬good k) := by
  have hp (k : Ω) : f k≤ target+eps+K*(if ¬good k then (1:ℝ) else 0) := by
    by_cases hk : good k
    · simpa only [not_not,hk,not_true_eq_false,if_false,mul_zero,add_zero] using hgood k hk
    · simpa only [if_pos hk,mul_one] using (hK k).trans (by linarith)
  have he := P.expect_mono hp
  rw [FiniteLaw.prob_eq_expect]
  convert! he using 1
  simp only [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_const_mul]

theorem eventually_native_exceptional_fullrow_menus
    (s a h rho z xi eta d L U R W : ℝ)
    (hs : 0< s) (ha : 0< a) (hh : 0< h) (hsum : s+a+h=1)
    (hz0 : 0≤ z) (hz1 : z<1) (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi)
    (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U) (hR : 0< R) (hW : 0≤ W)
    (hgap : d<(1-xi)*L) (hlower : h/2< rho) (hupper : rho< a+h/2)
    (hq0 : 0< sourceExposure a h rho z) (hq1 : sourceExposure a h rho z<1)
    (hboxlo : (1-xi)*U<(1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U< L)
    (c : ℕ → ℕ) (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0< eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B],
      (∀ b,μ {b}=0) → (∀ᵐ b ∂μ,b∈ Icc 0 d) → (∀ᵐ b ∂B,b∈ Icc L U) →
      ∀ (e : Equiv.Perm (Fin (N+1))) (b : ℝ),d< b → b< R → b∉Icc L U →
      ∀ v : ℝ,0< v → |v|≤ W →
      let C := contextPolicy (m := N+1) hxi hxi1 d L U z (c (N+1)) μ
      let P := CommonList.iid (categoryLaw s a h hs.le ha.le hh.le hsum B) N
      let lam := (1-xi*sourceExposure a h rho z)/reciprocalMean B
      P.expect (patternSingletonMenu C e μ B v b)< Menus.M1 hxi hxi1 lam v+eps ∧
        P.expect (patternBroadcastMenu C e μ B eta v b)< outsideTwo v lam+eps := by
  let tau := eps*(1-xi)/4
  have htau : 0< tau := by dsimp [tau]; positivity
  obtain ⟨delta,deq,dclip,hdelt,hdeq,hdclip,hcount⟩ :=
    exists_eventual_exceptional_pattern_bound s a h rho z xi L U hs ha hh hsum
      hz0 hz1 hxi hxi1 hL hLU hlower hupper hq0 hq1 hboxlo hboxhi c hc tau htau
  let K := W+2*R
  have hK : 0< K := by dsimp [K]; positivity
  have he : Tendsto (fun N => K*exceptionalGuardError h delta deq dclip N) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (exceptionalGuardError_tendsto_zero hh hdelt hdeq hdclip).const_mul K
  have htail := he.eventually (Iio_mem_nhds (half_pos heps))
  filter_upwards [hcount,htail] with N hN htailN
  intro μ B _ _ hnoatoms hμ hB e b hb hbr hout v hv hvW
  dsimp only
  let C := contextPolicy (m := N+1) hxi hxi1 d L U z (c (N+1)) μ
  let P := CommonList.iid (categoryLaw s a h hs.le ha.le hh.le hsum B) N
  let h0 := 1-xi*sourceExposure a h rho z
  let lam := h0/reciprocalMean B
  let good := fun kind : Fin N → Fin 4 =>
    exceptionalPatternGuard xi L U (c (N+1)) z kind ∧
      exceptionalPatternMenuError xi L U h0 (c (N+1)) z kind< tau
  have hprob : P.prob (fun kind => ¬good kind)≤ exceptionalGuardError h delta deq dclip N :=
    hN B inferInstance
  have h0abs : |h0|≤1 := by
    rw [abs_le]
    dsimp [h0]
    constructor <;> nlinarith
  have hetaabs : |eta|≤1 := by rw [abs_le,heta]; constructor <;> linarith
  have hbid : |b|≤ R := by rw [abs_of_pos (hd.trans_lt hb)]; exact hbr.le
  have hSb (kind : Fin N → Fin 4) : patternSingletonMenu C e μ B v b kind≤ K := by
    have h := (abs_le.mp (abs_patternSingletonMenu C e μ B v b kind)).2
    dsimp [K]
    linarith
  have hBb (kind : Fin N → Fin 4) : patternBroadcastMenu C e μ B eta v b kind≤ K := by
    have h := (abs_le.mp (abs_patternBroadcastMenu C e μ B hetaabs v b kind)).2
    dsimp [K]
    linarith
  have hgood (kind : Fin N → Fin 4) (hk : good kind) :
      patternSingletonMenu C e μ B v b kind≤ Menus.M1 hxi hxi1 lam v+eps/2 ∧
        patternBroadcastMenu C e μ B eta v b kind≤ outsideTwo v lam+eps/2 := by
    have hm := patternExceptional_menus_le hxi hxi1 heta hv z (c (N+1)) μ B
      hnoatoms hd hL hLU hgap hμ hB h0abs kind hb hout hk.1 e
      (fun q hq => le_unitMaximum (outsideOneAt xi v lam)
        (continuousOn_M1_unit hxi hxi1 v lam) q hq)
    have hE := hk.2
    have hdiv : exceptionalPatternMenuError xi L U h0 (c (N+1)) z kind/(1-xi)< eps/2 := by
      apply (div_lt_iff₀ (sub_pos.mpr hxi1)).2
      dsimp [tau] at hE
      nlinarith [mul_pos heps (sub_pos.mpr hxi1)]
    have hdouble : 2*exceptionalPatternMenuError xi L U h0 (c (N+1)) z kind< eps/2 := by
      dsimp [tau] at hE
      nlinarith [mul_pos heps hxi]
    change patternSingletonMenu C e μ B v b kind ≤ Menus.M1 hxi hxi1 lam v +
      exceptionalPatternMenuError xi L U h0 (c (N+1)) z kind/(1-xi) ∧
      patternBroadcastMenu C e μ B eta v b kind ≤ outsideTwo v lam +
      2*exceptionalPatternMenuError xi L U h0 (c (N+1)) z kind at hm
    exact ⟨hm.1.trans (by linarith),hm.2.trans (by linarith)⟩
  have htail' : K*P.prob (fun kind => ¬good kind)< eps/2 :=
    (mul_le_mul_of_nonneg_left hprob hK.le).trans_lt htailN
  have hs := finite_menu_upper P good _ (Menus.M1 hxi hxi1 lam v) K (eps/2)
    (Menus.M1_nonneg hxi hxi1 lam v) (half_pos heps).le hSb (fun kind hk => (hgood kind hk).1)
  have ht := finite_menu_upper P good _ (outsideTwo v lam) K (eps/2)
    (by unfold outsideTwo; positivity) (half_pos heps).le hBb (fun kind hk => (hgood kind hk).2)
  exact ⟨by linarith,by linarith⟩

theorem closed_singleton_payoff_physicalRows_all_lower {c : ℕ}
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {d U R : ℝ} (hdU : d≤ U) (hUR : U< R) (hg : Γ.g=0) (hseed : Γ.seedLaw=volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ,z∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,x.2.bid≤ U ∨ R≤ x.2.bid)
    (ν : Measure RowRival) (hrow : (userLaw Γ).map (physicalRow d U)=ν)
    (i : Fin (N+1)) (v : ℝ) (act : JointAction 2) (hb : act.bid< R)
    (hk : act.routeCount=1) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act=
      ∫ r,(privateContextLaw C (reindexedPhysicalContext i act.bid r) i).expect
        (fun k => ((v-act.bid)/2)*(k.val:ℝ)) ∂Measure.pi (fun _ : Fin N => ν) := by
  let broad := NativeLowIncentives.broadcast act.bid act.bid_nonneg
  have hl := closed_broadcast_count_physicalRows_all_lower C Γ hdU hUR hseed hfull hgap ν hrow
    i broad hb rfl (fun k => (k.val:ℝ))
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome broad).load=
    ∫ r,(privateContextLaw C (reindexedPhysicalContext i act.bid r) i).load
      ∂Measure.pi (fun _ : Fin N => ν) at hl
  rw [load_eq_mean _ (by norm_num : 0<2),show broad.routeCount=2 from rfl,Nat.cast_ofNat] at hl
  simp_rw [FiniteLaw.expect_const_mul]
  rw [integral_const_mul,singleton_payoff _ (by norm_num : 0<2) i act hk v]
  change (v-Γ.g-act.bid)*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i act.bid=_
  rw [hg]
  change (v-0-act.bid)*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i act.bid =
    ((v-act.bid)/2)*(∫ r,(privateContextLaw C (reindexedPhysicalContext i act.bid r) i).load
      ∂Measure.pi (fun _ : Fin N => ν))
  rw [←hl]
  change (v-0-act.bid)*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i act.bid=
    ((v-act.bid)/2)*(2*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i act.bid)
  ring

theorem closed_broadcast_payoff_fullRows_all_lower {c : ℕ}
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {eta d U R : ℝ} (heta0 : 0≤ eta) (heta1 : eta≤1)
    (hg : Γ.g=0) (hA : Γ.A=Schedule.affine 2 eta heta0 heta1)
    (hdU : d≤ U) (hUR : U< R) (hseed : Γ.seedLaw=volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ,z∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,x.2.bid≤ U ∨ R≤ x.2.bid)
    (s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hrow : (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B)
    (i : Fin (N+1)) (v : ℝ) (act : JointAction 2) (hb : act.bid< R)
    (hk : act.routeCount=2) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act=
      (CommonList.iid (categoryLaw s a h hs ha hh hsum B) N).expect
        (patternBroadcastMenu C (NativeContinuation.focalIndex i).symm μ B eta v act.bid) := by
  have heta : |eta|≤1 := by rw [abs_of_nonneg heta0]; exact heta1
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).expect
    (fun k => userPayoff v act.bid Γ.g Γ.A.charge Γ.G.charge k.val)=_
  simp_rw [hg,hA,affine_userPayoff_eq_realized]
  rw [closed_broadcast_count_physicalRows_all_lower C Γ hdU hUR hseed hfull hgap
    (physicalRivalLaw s a h μ B) hrow i act hb hk]
  rw [integral_physicalRows_eq_patternMenus s a h hs ha hh hsum μ B C i act.bid
    (fun k => realizedPayoff eta v act.bid k.val) (|v|+2*|act.bid|)
      (abs_realizedPayoff_two heta v act.bid)]
  rw [categoryLaw_eq_low_law s a h hs ha hh hsum μ B]
  apply FiniteLaw.expect_congr
  intro kind
  simp only [patternBroadcastMenu,Equiv.symm_symm,NativeContinuation.focalIndex_zero]

theorem closed_singleton_payoff_fullRows_all_lower {c : ℕ}
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {d U R : ℝ} (hg : Γ.g=0) (hdU : d≤ U) (hUR : U< R) (hseed : Γ.seedLaw=volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ,z∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,x.2.bid≤ U ∨ R≤ x.2.bid)
    (s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hrow : (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B)
    (i : Fin (N+1)) (v : ℝ) (act : JointAction 2) (hb : act.bid< R)
    (hk : act.routeCount=1) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act=
      (CommonList.iid (categoryLaw s a h hs ha hh hsum B) N).expect
        (patternSingletonMenu C (NativeContinuation.focalIndex i).symm μ B v act.bid) := by
  rw [closed_singleton_payoff_physicalRows_all_lower C Γ hdU hUR hg hseed hfull hgap
    (physicalRivalLaw s a h μ B) hrow i v act hb hk]
  rw [integral_physicalRows_eq_patternMenus s a h hs ha hh hsum μ B C i act.bid
    (fun k => ((v-act.bid)/2)*(k.val:ℝ)) (|v|+|act.bid|)
      (abs_singletonCountPayoff_two v act.bid)]
  rw [categoryLaw_eq_low_law s a h hs ha hh hsum μ B]
  apply FiniteLaw.expect_congr
  intro kind
  simp only [patternSingletonMenu,Equiv.symm_symm,NativeContinuation.focalIndex_zero]

theorem eventually_original_game_exceptional_menus
    (s a h rho z xi eta d L U R W : ℝ)
    (hs : 0< s) (ha : 0< a) (hh : 0< h) (hsum : s+a+h=1)
    (hz0 : 0≤ z) (hz1 : z<1) (hxi : 0< xi) (hxi1 : xi<1)
    (heta : eta=1-2*xi) (heta0 : 0≤ eta) (heta1 : eta≤1)
    (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U) (hUR : U< R) (hW : 0≤ W)
    (hgap : d<(1-xi)*L) (hlower : h/2< rho) (hupper : rho< a+h/2)
    (hq0 : 0< sourceExposure a h rho z) (hq1 : sourceExposure a h rho z<1)
    (hboxlo : (1-xi)*U<(1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U< L)
    (c : ℕ → ℕ) (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0< eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B],
      (∀ b,μ {b}=0) → (∀ᵐ b ∂μ,b∈ Icc 0 d) → (∀ᵐ b ∂B,b∈ Icc L U) →
      ∀ Γ : FiniteGame (N+1) 2 (c (N+1)) unitInterval,
      Γ.g=0 → Γ.A=Schedule.affine 2 eta heta0 heta1 → Γ.seedLaw=volume →
      (∀ᵐ x ∂userProfileLaw Γ,x∈ closedProfiles (N+1) R) →
      (∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,x.2.bid≤ U ∨ R≤ x.2.bid) →
      (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B →
      ∀ (i : Fin (N+1)) (act : JointAction 2),
      d< act.bid → act.bid< R → act.bid∉Icc L U → ∀ v : ℝ,0< v → |v|≤ W →
      let G := ClosedPolicy.nativeGame (contextPolicy hxi hxi1 d L U z (c (N+1)) μ) Γ R
      let lam := (1-xi*sourceExposure a h rho z)/reciprocalMean B
      (act.routeCount=1 → (problem G i).payoff v act< Menus.M1 hxi hxi1 lam v+eps) ∧
        (act.routeCount=2 → (problem G i).payoff v act< outsideTwo v lam+eps) := by
  have hR : 0< R := (hL.trans_le hLU).trans hUR
  have hdU : d≤ U := (hgap.trans (by nlinarith [mul_pos hxi hL])).le.trans hLU
  have hm := eventually_native_exceptional_fullrow_menus s a h rho z xi eta d L U R W
    hs ha hh hsum hz0 hz1 hxi hxi1 heta hd hL hLU hR hW hgap hlower hupper
    hq0 hq1 hboxlo hboxhi c hc eps heps
  filter_upwards [hm] with N hN
  intro μ B _ _ hnoatoms hμ hB Γ hg hA hseed hfull hpopgap hrow i act hb hbr hout v hv hvW
  dsimp only
  let C := contextPolicy (m := N+1) hxi hxi1 d L U z (c (N+1)) μ
  have ht := hN μ B hnoatoms hμ hB (NativeContinuation.focalIndex i).symm act.bid hb hbr hout v hv hvW
  constructor
  · intro hk
    rw [closed_singleton_payoff_fullRows_all_lower C Γ hg hdU hUR hseed hfull hpopgap
      s a h hs.le ha.le hh.le hsum μ B hrow i v act hbr hk]
    exact ht.1
  · intro hk
    rw [closed_broadcast_payoff_fullRows_all_lower C Γ heta0 heta1 hg hA hdU hUR hseed hfull hpopgap
      s a h hs.le ha.le hh.le hsum μ B hrow i v act hbr hk]
    exact ht.2

lemma low_bid_cutoff_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] {d : ℝ}
    (hnoatoms : ∀ b,μ {b}=0) (hμ : ∀ᵐ b ∂μ,b∈ Icc 0 d) : 0< d := by
  have hne : ∀ᵐ b ∂μ,b≠0 := by
    rw [ae_iff]
    simpa only [not_not,Set.setOf_eq_eq_singleton] using hnoatoms 0
  obtain ⟨b,hb,hb0⟩ := (hμ.and hne).exists
  exact (lt_of_le_of_ne hb.1 hb0.symm).trans_le hb.2

def zeroSourceLoss (xi qbar L U vmin vmax : ℝ) : ℝ :=
  vmin*(min (lowerEndpointGap xi ((1-xi*qbar)*L) L vmin)
    (upperEndpointGap xi ((1-xi*qbar)*U) U vmax))^2

lemma zeroSourceLoss_pos {xi qbar L U vmin vmax : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hq0 : 0< qbar) (hq1 : qbar<1)
    (hL : 0< L) (hLU : L≤ U) (hUv : U< vmin) (hv : vmin≤ vmax)
    (hleft : L<(1-qbar)/(1-xi*qbar)*vmin)
    (hright : (1-qbar)/(1-xi*qbar)*vmax< U) :
    0< zeroSourceLoss xi qbar L U vmin vmax := by
  have hU : 0< U := hL.trans_le hLU
  have hvmin : 0< vmin := hU.trans hUv
  have hvmax : 0< vmax := hvmin.trans_le hv
  have hg := source_zero_endpoint_gaps hxi hxi1 hq0 hq1 hL hU hvmin hvmax hleft hright
  exact mul_pos hvmin (sq_pos_of_pos (lt_min hg.1 hg.2))

theorem patternExceptional_zero_menu_le {xi eta d L U R qbar vmin vmax v b : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi)
    (hq0 : 0< qbar) (hq1 : qbar<1) (c : ℕ)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hnoatoms : ∀ b,μ {b}=0) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (hμ : ∀ᵐ b ∂μ,b∈ Icc 0 d) (hB : ∀ᵐ b ∂B,b∈ Icc L U)
    (hUv : U< vmin) (hvmin : vmin≤ v) (hvmax : v≤ vmax)
    (hboxlo : (1-xi)*U<(1-xi*qbar)*L) (hboxhi : (1-xi*qbar)*U< L)
    (hleft : L<(1-qbar)/(1-xi*qbar)*vmin)
    (hright : (1-qbar)/(1-xi*qbar)*vmax< U)
    (kind : Fin N → Fin 4) (hb : d< b) (hbR : b< R) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c 0 kind)
    (e : Equiv.Perm (Fin (N+1))) :
    patternBroadcastMenu (contextPolicy hxi hxi1 d L U 0 c μ) e μ B eta v b kind≤
      outsideTwo v ((1-xi*qbar)/reciprocalMean B)-zeroSourceLoss xi qbar L U vmin vmax+
        (broadcastExposureModulus eta vmax R/(xi*d))*
          exceptionalPatternMenuError xi L U (1-xi*qbar) c 0 kind := by
  have hd := low_bid_cutoff_pos μ hnoatoms hμ
  have hU : 0< U := hL.trans_le hLU
  have hvmin0 : 0< vmin := hU.trans hUv
  have hv : 0< v := hvmin0.trans_le hvmin
  have hvmax0 : 0< vmax := hv.trans_le hvmax
  have h0 : 0<1-xi*qbar := by nlinarith
  have h01 : 1-xi*qbar≤1 := by nlinarith
  have hgaps := source_zero_endpoint_gaps hxi hxi1 hq0 hq1 hL hU hvmin0 hvmax0 hleft hright
  let C := originalEligible kind e
  have hKpos := hguard.1.2.2.1
  have hD := hguard.2.1
  have hCcard : C.card=Fintype.card (ActivePatternIndex kind)-1 := originalEligible_card kind e
  have hN : 2≤ C.card := by rw [hCcard]; omega
  letI : Nonempty C := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0< C.card by omega)
    exact ⟨⟨j,hj⟩⟩
  have hK : activePatternOwner c 0 kind 0+activePatternOwner c 0 kind 1< C.card := by
    rw [hCcard]
    omega
  have hn : C.card-(activePatternOwner c 0 kind 0+activePatternOwner c 0 kind 1)=
      Fintype.card (ActivePatternIndex kind)-
        (activePatternOwner c 0 kind 0+activePatternOwner c 0 kind 1)-1 := by omega
  have hg : ClippedCountGuard xi L U
      (Fintype.card C-(activePatternOwner c 0 kind 0+activePatternOwner c 0 kind 1)+1)
      (activePatternResidual c 0 kind) := by
    have he : Fintype.card C-(activePatternOwner c 0 kind 0+activePatternOwner c 0 kind 1)+1=
        Fintype.card (ActivePatternIndex kind)-
          (activePatternOwner c 0 kind 0+activePatternOwner c 0 kind 1) := by
      rw [Fintype.card_coe,hCcard]
      omega
    rw [he]
    exact hguard.2
  have hout' : b≤ L ∨ U≤ b := by
    by_cases hbl : b≤ L
    · exact Or.inl hbl
    · exact Or.inr (lt_of_not_ge (fun hbu => hout ⟨(lt_of_not_ge hbl).le,hbu⟩)).le
  have hm := primitive_excluded_owner_zero_menu (ι:=C) (W := vmax) B hxi hxi1 heta hd hb.le hbR.le
    (by rw [abs_of_pos hv]; exact hvmax) hL hLU hB h0 h01 hUv hvmin hvmax
    hboxlo hboxhi hout' hgaps.1 hgaps.2
    (activePatternOwner c 0 kind 0) (activePatternOwner c 0 kind 1) (activePatternResidual c 0 kind)
    (by simpa only [Fintype.card_coe] using hN) (by simpa only [Fintype.card_coe] using hK) hg
  have he := patternExceptional_menus_eq hxi hxi1 0 c μ B hnoatoms hd.le hL hLU hgap hμ hB
    kind eta v b hb hout hguard e
  rw [he.2]
  simpa only [Fintype.card_coe,hn,exceptionalPatternMenuError,zeroSourceLoss] using hm

theorem eventually_native_exceptional_zero_fullrow
    (s a h rho xi eta d L U R vmin vmax : ℝ)
    (hs : 0< s) (ha : 0< a) (hh : 0< h) (hsum : s+a+h=1)
    (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi)
    (hL : 0< L) (hLU : L≤ U) (hUR : U< R) (hUv : U< vmin) (hvv : vmin≤ vmax)
    (hgap : d<(1-xi)*L) (hlower : h/2< rho) (hupper : rho< a+h/2)
    (hq0 : 0< sourceExposure a h rho 0) (hq1 : sourceExposure a h rho 0<1)
    (hboxlo : (1-xi)*U<(1-xi*sourceExposure a h rho 0)*L)
    (hboxhi : (1-xi*sourceExposure a h rho 0)*U< L)
    (hleft : L<(1-sourceExposure a h rho 0)/(1-xi*sourceExposure a h rho 0)*vmin)
    (hright : (1-sourceExposure a h rho 0)/(1-xi*sourceExposure a h rho 0)*vmax< U)
    (c : ℕ → ℕ) (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0< eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B],
      (∀ b,μ {b}=0) → (∀ᵐ b ∂μ,b∈ Icc 0 d) → (∀ᵐ b ∂B,b∈ Icc L U) →
      ∀ (e : Equiv.Perm (Fin (N+1))) (b : ℝ),d< b → b< R → b∉Icc L U →
      ∀ v∈ Icc vmin vmax,
      let C := contextPolicy (m := N+1) hxi hxi1 d L U 0 (c (N+1)) μ
      let P := CommonList.iid (categoryLaw s a h hs.le ha.le hh.le hsum B) N
      let lam := (1-xi*sourceExposure a h rho 0)/reciprocalMean B
      P.expect (patternBroadcastMenu C e μ B eta v b)< outsideTwo v lam-
        zeroSourceLoss xi (sourceExposure a h rho 0) L U vmin vmax+eps := by
  by_cases hd : 0< d
  swap
  · refine Filter.Eventually.of_forall ?_
    intro N μ B _ _ hnoatoms hμ
    exact False.elim (hd (low_bid_cutoff_pos μ hnoatoms hμ))
  let qbar := sourceExposure a h rho 0
  let loss := zeroSourceLoss xi qbar L U vmin vmax
  have hloss : 0< loss := zeroSourceLoss_pos hxi hxi1 hq0 hq1 hL hLU hUv hvv hleft hright
  have hU : 0< U := hL.trans_le hLU
  have hR : 0< R := hU.trans hUR
  have hvmin : 0< vmin := hU.trans hUv
  have hvmax : 0< vmax := hvmin.trans_le hvv
  let B0 := broadcastExposureModulus eta vmax R/(xi*d)
  have hB0 : 0≤ B0 := div_nonneg (broadcastExposureModulus_nonneg hvmax.le hR.le)
    (mul_pos hxi hd).le
  let tau := eps/(2*(B0+1))
  have htau : 0< tau := div_pos heps (by positivity)
  have hetaabs : |eta|≤1 := by rw [heta,abs_le]; constructor <;> linarith
  obtain ⟨delta,deq,dclip,hdelt,hdeq,hdclip,hcount⟩ :=
    exists_eventual_exceptional_pattern_bound s a h rho 0 xi L U hs ha hh hsum
      (by norm_num) (by norm_num) hxi hxi1 hL hLU hlower hupper hq0 hq1 hboxlo hboxhi c hc tau htau
  let K := vmax+2*R+loss
  have hK : 0< K := by dsimp [K]; positivity
  have he : Tendsto (fun N => K*exceptionalGuardError h delta deq dclip N) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (exceptionalGuardError_tendsto_zero hh hdelt hdeq hdclip).const_mul K
  have htail := he.eventually (Iio_mem_nhds (half_pos heps))
  filter_upwards [hcount,htail] with N hN htailN
  intro μ B _ _ hnoatoms hμ hB e b hb hbR hout v hv
  dsimp only
  let C := contextPolicy (m := N+1) hxi hxi1 d L U 0 (c (N+1)) μ
  let P := CommonList.iid (categoryLaw s a h hs.le ha.le hh.le hsum B) N
  let lam := (1-xi*qbar)/reciprocalMean B
  let good := fun kind : Fin N → Fin 4 =>
    exceptionalPatternGuard xi L U (c (N+1)) 0 kind ∧
      exceptionalPatternMenuError xi L U (1-xi*qbar) (c (N+1)) 0 kind< tau
  have hv0 : 0< v := hvmin.trans_le hv.1
  have hvW : |v|≤ vmax := by rw [abs_of_pos hv0]; exact hv.2
  have hbid : |b|≤ R := by rw [abs_of_pos (hd.trans hb)]; exact hbR.le
  have hprob : P.prob (fun kind => ¬good kind)≤ exceptionalGuardError h delta deq dclip N :=
    hN B inferInstance
  have hbound (kind : Fin N → Fin 4) : patternBroadcastMenu C e μ B eta v b kind+loss≤ K := by
    have h := (abs_le.mp (abs_patternBroadcastMenu C e μ B hetaabs v b kind)).2
    dsimp [K]
    linarith
  have hgood (kind : Fin N → Fin 4) (hk : good kind) :
      patternBroadcastMenu C e μ B eta v b kind+loss≤ outsideTwo v lam+eps/2 := by
    have hm := patternExceptional_zero_menu_le hxi hxi1 heta hq0 hq1 (c (N+1)) μ B
      hnoatoms hL hLU hgap hμ hB hUv hv.1 hv.2 hboxlo hboxhi hleft hright
      kind hb hbR hout hk.1 e
    have hEtau := mul_le_mul_of_nonneg_left hk.2.le hB0
    have heq : 2*(B0+1)*tau=eps := by dsimp [tau]; field_simp
    have hsmall : B0*exceptionalPatternMenuError xi L U (1-xi*qbar) (c (N+1)) 0 kind< eps/2 := by
      nlinarith [htau]
    dsimp only [loss,lam] at hm ⊢
    linarith
  have ht := finite_menu_upper P good (fun kind => patternBroadcastMenu C e μ B eta v b kind+loss)
    (outsideTwo v lam) K (eps/2) (by unfold outsideTwo; positivity) (half_pos heps).le hbound hgood
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const] at ht
  have htail' : K*P.prob (fun kind => ¬good kind)< eps/2 :=
    (mul_le_mul_of_nonneg_left hprob hK.le).trans_lt htailN
  linarith

theorem eventually_original_game_exceptional_zero_strict
    (s a h rho xi eta d L U R vmin vmax : ℝ)
    (hs : 0< s) (ha : 0< a) (hh : 0< h) (hsum : s+a+h=1)
    (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi) (heta0 : 0≤ eta) (heta1 : eta≤1)
    (hL : 0< L) (hLU : L≤ U) (hUR : U< R) (hUv : U< vmin) (hvv : vmin≤ vmax)
    (hgap : d<(1-xi)*L) (hlower : h/2< rho) (hupper : rho< a+h/2)
    (hq0 : 0< sourceExposure a h rho 0) (hq1 : sourceExposure a h rho 0<1)
    (hboxlo : (1-xi)*U<(1-xi*sourceExposure a h rho 0)*L)
    (hboxhi : (1-xi*sourceExposure a h rho 0)*U< L)
    (hleft : L<(1-sourceExposure a h rho 0)/(1-xi*sourceExposure a h rho 0)*vmin)
    (hright : (1-sourceExposure a h rho 0)/(1-xi*sourceExposure a h rho 0)*vmax< U)
    (c : ℕ → ℕ) (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (nhds rho)) :
    let loss := zeroSourceLoss xi (sourceExposure a h rho 0) L U vmin vmax/2
    0< loss ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B],
      (∀ b,μ {b}=0) → (∀ᵐ b ∂μ,b∈ Icc 0 d) → (∀ᵐ b ∂B,b∈ Icc L U) →
      ∀ Γ : FiniteGame (N+1) 2 (c (N+1)) unitInterval,
      Γ.g=0 → Γ.A=Schedule.affine 2 eta heta0 heta1 → Γ.seedLaw=volume →
      (∀ᵐ x ∂userProfileLaw Γ,x∈ closedProfiles (N+1) R) →
      (∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,x.2.bid≤ U ∨ R≤ x.2.bid) →
      (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B →
      ∀ (i : Fin (N+1)) (act : JointAction 2),
      d< act.bid → act.bid< R → act.bid∉Icc L U → act.routeCount=2 → ∀ v∈ Icc vmin vmax,
      let G := ClosedPolicy.nativeGame (contextPolicy hxi hxi1 d L U 0 (c (N+1)) μ) Γ R
      let lam := (1-xi*sourceExposure a h rho 0)/reciprocalMean B
      (problem G i).payoff v act< outsideTwo v lam-loss := by
  let loss := zeroSourceLoss xi (sourceExposure a h rho 0) L U vmin vmax/2
  have hloss : 0< loss := half_pos
    (zeroSourceLoss_pos hxi hxi1 hq0 hq1 hL hLU hUv hvv hleft hright)
  refine ⟨hloss,?_⟩
  have hm := eventually_native_exceptional_zero_fullrow s a h rho xi eta d L U R vmin vmax
    hs ha hh hsum hxi hxi1 heta hL hLU hUR hUv hvv hgap hlower hupper
    hq0 hq1 hboxlo hboxhi hleft hright c hc loss hloss
  filter_upwards [hm] with N hN
  intro μ B _ _ hnoatoms hμ hB Γ hg hA hseed hfull hpopgap hrow i act hb hbr hout hk v hv
  dsimp only
  have hdU : d≤ U := (hgap.trans (by nlinarith [mul_pos hxi hL])).le.trans hLU
  let C := contextPolicy (m := N+1) hxi hxi1 d L U 0 (c (N+1)) μ
  rw [closed_broadcast_payoff_fullRows_all_lower C Γ heta0 heta1 hg hA hdU hUR hseed hfull hpopgap
    s a h hs.le ha.le hh.le hsum μ B hrow i v act hbr hk]
  have ht := hN μ B hnoatoms hμ hB (NativeContinuation.focalIndex i).symm act.bid hb hbr hout v hv
  dsimp only [loss] at ht ⊢
  linarith

theorem exists_positive_null_error_of_eventually (P : ℕ → ℝ → Prop)
    (hP : ∀ eps>0,∀ᶠ m : ℕ in atTop,P m eps) :
    ∃ err : ℕ → ℝ,(∀ m,0< err m) ∧ Tendsto err atTop (nhds 0) ∧
      ∀ᶠ m : ℕ in atTop,P m (err m) := by
  let first (j : ℕ) : ℕ :=
    (eventually_atTop.mp (hP (1/((j:ℝ)+1)) (by positivity))).choose
  have hfirst (j : ℕ) : ∀ m≥ first j,P m (1/((j:ℝ)+1)) :=
    (eventually_atTop.mp (hP (1/((j:ℝ)+1)) (by positivity))).choose_spec
  let threshold (j : ℕ) := max j (first j)
  let eligible (m : ℕ) := (Finset.range (m+1)).filter (fun j => threshold j≤ m)
  let level (m : ℕ) := if hm : (eligible m).Nonempty then (eligible m).max' hm else 0
  have hmem (j m : ℕ) (hjm : threshold j≤ m) : j∈ eligible m := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,hjm⟩
    have hj : j≤ m := (le_max_left j (first j)).trans hjm
    omega
  have hlevel (j m : ℕ) (hjm : threshold j≤ m) : j≤ level m := by
    have he := hmem j m hjm
    have hn : (eligible m).Nonempty := ⟨j,he⟩
    simp only [level,dif_pos hn]
    exact Finset.le_max' (eligible m) j he
  have hlevels : Tendsto level atTop atTop := by
    apply tendsto_atTop.2
    intro j
    exact eventually_atTop.mpr ⟨threshold j,fun m hm => hlevel j m hm⟩
  let err (m : ℕ) : ℝ := 1/((level m:ℝ)+1)
  have herr : Tendsto err atTop (nhds 0) := by
    have hn : Tendsto (fun m => (level m:ℝ)+1) atTop atTop := by
      convert! (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hlevels) :
          Tendsto (fun m => ((level m+1:ℕ):ℝ)) atTop atTop) using 1
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
    exact tendsto_const_nhds.div_atTop hn
  refine ⟨err,fun m => by dsimp [err]; positivity,herr,?_⟩
  filter_upwards [eventually_ge_atTop (threshold 0)] with m hm
  have hn : (eligible m).Nonempty := ⟨0,hmem 0 m hm⟩
  have hl : level m∈ eligible m := by
    simp only [level,dif_pos hn]
    exact Finset.max'_mem (eligible m) hn
  have ht : threshold (level m)≤ m := (Finset.mem_filter.mp hl).2
  exact hfirst (level m) m ((le_max_right _ _).trans ht)

end FullContext
end FCAppendix.Affine.Hybrid.Native02
