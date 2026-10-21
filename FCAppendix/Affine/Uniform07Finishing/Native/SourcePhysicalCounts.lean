import FCAppendix.Affine.Uniform07Finishing.Native.SourceSeedAveraging
import FCAppendix.Affine.Hybrid.NativeRealizedContext

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative Weighted ConditionalSuccess
open scoped BigOperators

variable {m : ℕ} [Nonempty (Fin m)]

attribute [local irreducible] privateCountMoment sourceCountCorrection finitePathCountCorrection

namespace StrictNative.ContextPolicy

def selectionPair {c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (C : ContextPolicy m c Seed) (X : ClassifiedContext m) (s : Fin 2 → Seed) :
    Finset (Fin m) × Finset (Fin m) := (C.select 0 X (s 0),C.select 1 X (s 1))

omit [Nonempty (Fin m)] in
theorem native_allocation_mem_iff {c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (C : ContextPolicy m c Seed) (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hpolicy : Γ.policy = C.localPolicy R) (d : UserProfile m 2)
    (hd : d ∈ classifiedProfiles m R) (s : Fin 2 → Seed) (j : Fin 2)
    (i : Fin m) (hi : (d i).1.2.bid < R) :
    i ∈ allocation (drawsRealization d) Γ.policy s j ↔
      i ∈ C.select j (actualContext R d) (s j) := by
  have hlow : broadcastPart R (observe (drawsRealization d) j) i ≠ none := by
    rw [broadcastPart_observe d hd j]
    simp only [if_pos hi,ne_eq,Option.some_ne_none,not_false_eq_true]
  have hf := C.factors R j (observe (drawsRealization d) j) (s j) i hlow
  rw [observedContext_eq_actual d hd j] at hf
  simpa only [allocation,hpolicy,localPolicy] using hf

omit [Nonempty (Fin m)] in
theorem native_inclusionCount_eq_focalCopy {c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (C : ContextPolicy m c Seed) (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hpolicy : Γ.policy = C.localPolicy R) (d : UserProfile m 2)
    (hd : d ∈ classifiedProfiles m R) (s : Fin 2 → Seed)
    (i : Fin m) (hi : (d i).1.2.bid < R) :
    inclusionCount (drawsRealization d) Γ.policy s i =
      (focalCopy (C.selectionPair (actualContext R d) s) i).val := by
  rw [inclusionCount_eq_sum,Fin.sum_univ_two]
  simp only [C.native_allocation_mem_iff Γ R hpolicy d hd s 0 i hi,
    C.native_allocation_mem_iff Γ R hpolicy d hd s 1 i hi]
  by_cases h0 : i ∈ C.select 0 (actualContext R d) (s 0) <;>
    by_cases h1 : i ∈ C.select 1 (actualContext R d) (s 1) <;>
    simp [selectionPair,focalCopy,h0,h1]

end StrictNative.ContextPolicy

def sourceDrawShape (U R : ℝ) (u : UserDraw 2) : Prop :=
  (u.1.2.bid ≤ U ∧ u.1.2.routeCount = 2) ∨
    (R ≤ u.1.2.bid ∧ u.1.2.routeCount = 1)

omit [Nonempty (Fin m)] in
theorem sourceDrawShape_classified {U R : ℝ} (hUR : U < R)
    {d : UserProfile m 2} (hd : ∀k, sourceDrawShape U R (d k)) :
    d ∈ classifiedProfiles m R := by
  intro k
  rcases hd k with hl | hh
  · exact Or.inl ⟨hl.1.trans_lt hUR,hl.2⟩
  · exact Or.inr hh

omit [Nonempty (Fin m)] in
theorem source_focal_exceptional_subset {U R : ℝ} (hUR : U < R)
    (d : UserProfile m 2) (hd : ∀k, sourceDrawShape U R (d k))
    (i : Fin m) (a : JointAction 2) (haR : a.bid < R) (ha2 : a.routeCount = 2)
    (τ : Equiv.Perm (Fin 2)) :
    exceptionalSet U (observedContext R 0 (deviationList i a d τ 0)).1 ⊆ {i} := by
  have hfull := sourceDrawShape_classified hUR hd
  have hz := updated_broadcast_classified d hfull i 0 a haR ha2 τ
  have hL : deviationList i a d τ 0 =
      observe (drawsRealization (Function.update d i ((0,a),τ))) 0 := by
    rw [deviationList_eq_focalLocalList]
    simp only [focalLocalList,insert_deleteFocal]
  intro k hk
  by_contra hki
  have hki' : k ≠ i := by simpa only [Finset.mem_singleton] using hki
  have hh := (Finset.mem_filter.mp hk).2
  change broadcastPart R (deviationList i a d τ 0) k ≠ none ∧
    U < entryBid (broadcastPart R (deviationList i a d τ 0) k) at hh
  rw [hL,broadcastPart_observe _ hz 0] at hh
  simp only [Function.update_of_ne hki'] at hh
  rcases hd k with hl | hupper
  · simp only [if_pos (hl.1.trans_lt hUR),entryBid] at hh
    exact (not_lt_of_ge hl.1) hh.2
  · simp only [if_neg (not_lt.mpr hupper.1),ne_eq,not_true_eq_false] at hh
    exact hh.1

theorem source_focal_private_moment
    (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m) (R Λ : ℝ) (hΛ : 0 < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (α : ClassifiedContext m → unitInterval) (hα : Measurable α)
    (hUR : Early.bidCap row < R) (d : UserProfile m 2)
    (hd : ∀k, sourceDrawShape (Early.bidCap row) R (d k))
    (i : Fin m) (a : JointAction 2) (haR : a.bid < R) (ha2 : a.routeCount = 2)
    (τ : Equiv.Perm (Fin 2)) (q : Fin 3 → ℝ) :
    let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
    let C := observedContext R 0 (deviationList i a d τ 0)
    (∫s : Fin 2 → unitInterval, q (focalCount Γ i a ((d,s),τ))
      ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) =
    privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      (Uniform07.capacity m) C
        (sourcePlan (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row)
          (Uniform07.cutoff row/2) (Uniform07.capacity m) (sourceSeedMeasure row m hc R PL) α C)
        i q := by
  let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
  let C := sourceWeightedContext row hc R Λ hΛ PL α hα
  let X := observedContext R 0 (deviationList i a d τ 0)
  let d' := Function.update d i ((0,a),τ)
  have hd' : d' ∈ classifiedProfiles m R :=
    updated_broadcast_classified d (sourceDrawShape_classified hUR hd) i 0 a haR ha2 τ
  have hX : X = actualContext R d' := by
    dsimp only [X]
    rw [deviationList_eq_focalLocalList]
    simp only [focalLocalList,insert_deleteFocal]
    exact observedContext_eq_actual d' hd' 0
  have hbad : ¬1 < (exceptionalSet (Early.bidCap row) X.1).card := by
    have hs := Finset.card_le_card (source_focal_exceptional_subset hUR d hd i a haR ha2 τ)
    simpa only [Finset.card_singleton,not_lt] using hs
  have hcount (s : Fin 2 → unitInterval) :
      focalCount Γ i a ((d,s),τ) = focalCopy (C.selectionPair X s) i := by
    apply Fin.ext
    rw [Hybrid.focalCount_eq_inserted_count Γ i 0 a d s τ]
    rw [C.native_inclusionCount_eq_focalCopy Γ R rfl d' hd' s i
      (by simpa only [d',Function.update_self] using haR),←hX]
  change (∫s : Fin 2 → unitInterval, q (focalCount Γ i a ((d,s),τ))
    ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) = _
  have he : (fun s : Fin 2 → unitInterval => q (focalCount Γ i a ((d,s),τ))) =
      (fun s => q (focalCopy (C.selectionPair X s) i)) :=
    funext (fun s => congrArg q (hcount s))
  rw [he]
  change (∫s : Fin 2 → unitInterval,
    q (focalCopy (completedSelect _ _ _ _ _ _ 0 X (s 0),
      completedSelect _ _ _ _ _ _ 1 X (s 1)) i)
        ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) = _
  simp only [completedSelect,if_neg hbad]
  exact privateCountMoment_at_actual_plan _ _ _ _ _ X i q

def focalInputContext (R : ℝ) (i : Fin m) (a : JointAction 2)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) : ClassifiedContext m :=
  observedContext R 0 (deviationList i a x.1 x.2 0)

omit [Nonempty (Fin m)] in
theorem measurable_focalInputContext (R : ℝ) (i : Fin m) (a : JointAction 2) :
    Measurable (focalInputContext R i a) := by
  have hinput : Measurable (fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
      ((x.1,fun _ : Fin 2 => (0 : unitInterval)),x.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hL : Measurable (fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
      deviationList i a x.1 x.2 0) := by
    convert! (measurable_observe_deviated (Seed := unitInterval) i a 0).comp hinput using 1
  convert! (measurable_observedContext R 0).comp hL using 1

def sourcePhysicalCountTest (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U zs R : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (i : Fin m) (a : JointAction 2) (q : Fin 3 → ℝ)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) : ℝ :=
  let X := focalInputContext R i a x
  privateCountMoment ξ hξ hξ1 c X none i q +
    if rivalHasSeed zs i (deleteFocal i x.1) then
      finitePathCountCorrection ξ hξ hξ1 Λ r U c α X i q else 0

theorem measurable_sourcePhysicalCountTest (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U zs R : ℝ) (hΛ : 0 < Λ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (hα : Measurable α)
    (i : Fin m) (a : JointAction 2) (q : Fin 3 → ℝ) :
    Measurable (sourcePhysicalCountTest ξ hξ hξ1 Λ r U zs R c α i a q) := by
  have hC := measurable_focalInputContext R i a
  exact ((measurable_privateCountMoment ξ hξ hξ1 c i q).comp
    (hC.prodMk measurable_const)).add
      (Measurable.ite ((measurableSet_rivalHasSeed zs i).preimage
        ((measurable_deleteFocal i).comp measurable_fst))
        ((measurable_finitePathCountCorrection ξ hξ hξ1 Λ r U hΛ c α hα i q).comp hC)
        measurable_const)

theorem abs_sourcePhysicalCountTest_le (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U zs R : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (i : Fin m) (a : JointAction 2) (q : Fin 3 → ℝ)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) :
    |sourcePhysicalCountTest ξ hξ hξ1 Λ r U zs R c α i a q x| ≤
      3*∑r : Fin 3, |q r| := by
  have hb := abs_privateCountMoment_le ξ hξ hξ1 c (focalInputContext R i a x) none i q
  have hp := abs_finitePathCountCorrection_le ξ hξ hξ1 Λ r U c α
    (focalInputContext R i a x) i q
  unfold sourcePhysicalCountTest
  split_ifs
  · exact (abs_add_le _ _).trans (by linarith)
  · simp only [add_zero]
    have hh : 0 ≤ ∑r : Fin 3, |q r| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith

omit [Nonempty (Fin m)] in
theorem focalContext_entry_bid {R : ℝ} (i : Fin m) (a : JointAction 2)
    (haR : a.bid < R) (ha2 : a.routeCount = 2) (τ : Equiv.Perm (Fin 2))
    (j : Fin 2) (d : RivalIndex i → UserDraw 2) :
    entryBid ((observedContext R j (focalLocalList i a τ j d)).1 i) = a.bid := by
  simp [observedContext,broadcastPart,StrictTags.lowList,StrictTags.tag,
    focalLocalList,observe,drawsRealization,insertFocalProfile,haR,ha2,firstK_full_two,entryBid]

theorem source_correction_integral_broadcast (row : Uniform07.Row)
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] (i : Fin m)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hUR : Early.bidCap row < R) (hzG : Uniform07.cutoff row/2 ≤ zG)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (a : JointAction 2) (haR : a.bid < R) (ha2 : a.routeCount = 2)
    (τ : Equiv.Perm (Fin 2)) (q : Fin 3 → ℝ)
    (hroute : ∀ᵐu ∂μ, u.1.2.bid ≤ Uniform07.cutoff row/2 → u.1.2.routeCount = 2)
    (hgeneric : ∀ᵐd ∂Measure.pi (fun _ : RivalIndex i => μ),
      contextCopyGeneric (1-Uniform07.xi row) i (observedContext R 0 (focalLocalList i a τ 0 d)))
    (hnoatoms : ∀b : ℝ,
      ((cond μ (sourceDrawTag (Uniform07.cutoff row/2) (Early.bidCap row) ⁻¹' {0})).map
        (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0) :
    let zs := Uniform07.cutoff row/2
    let μB := (cond μ (sourceDrawTag zs (Early.bidCap row) ⁻¹' {0})).map
      (fun u : UserDraw 2 => u.1.2.bid)
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    let C := fun d => observedContext R 0 (focalLocalList i a τ 0 d)
    (∫d, sourceCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) c α (C d)
      (sourceSeed μB zs (C d)) i q ∂Measure.pi (fun _ : RivalIndex i => μ)) =
    ∫d, (if rivalHasSeed zs i d then
      finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ (Early.demandRatio row) (Early.bidCap row) c α (C d) i q else 0)
      ∂Measure.pi (fun _ : RivalIndex i => μ) := by
  by_cases ha : Uniform07.cutoff row/2 < a.bid
  · exact source_correction_integral row μ i hΛ hR hguard hUR hzG hm hε c
      a ha τ 0 q hroute hgeneric hnoatoms
  · have hlo : a.bid ≤ Uniform07.cutoff row/2 := le_of_not_gt ha
    dsimp only
    apply integral_congr_ae
    apply ae_of_all
    intro d
    let X := observedContext R 0 (focalLocalList i a τ 0 d)
    have hX := focalContext_nonnegative R i a τ 0 d
    have hb := focalContext_le_floor hR.le i a τ 0 d
    have hi : entryBid (X.1 i) ≤ Uniform07.cutoff row/2 := by
      rw [focalContext_entry_bid i a haR ha2 τ 0 d]
      exact hlo
    have hz (seed : Option unitInterval) := literal_sourceCountCorrection_seed_focal_zero (width := width) row
      hΛ hR hguard hzG hm hε c seed X hX hb i hi q
    dsimp only
    rw [hz]
    split_ifs
    · rw [←integral_sourceCountCorrection]
      apply Eq.symm
      apply integral_eq_zero_of_ae
      exact ae_of_all _ (fun s => hz (some s))
    · rfl

section SourceShape

variable (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
  {R Λ : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
  (hRt : R < Uniform07.cutoff row) (hΛ : 0 < Λ)
  (PL : ProbabilityMeasure (ℝ × JointAction 2))
  (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw row : Measure ℝ))
  (hLroute : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)),
    x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
  (α : ClassifiedContext m → unitInterval) (hα : Measurable α)

include hm hR hRt hLvalue hLroute in
theorem sourceNativeGame_draw_shape :
    ∀ᵐu ∂userLaw (sourceNativeGame row hc R Λ hΛ PL α hα),
      sourceDrawShape (Early.bidCap row) R u := by
  let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
  have hj : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,
      (x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2) ∨
      (R ≤ x.2.bid ∧ x.2.routeCount = 1) := by
    rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute α hα]
    filter_upwards [source_population_support row m hm hc hR hRt PL hLvalue hLroute] with x hx
    rcases hx with hl | hh
    · exact Or.inl hl.2.2
    · exact Or.inr ⟨hh.2.2.2.1,hh.2.2.2.2.2⟩
  exact (measurePreserving_fst (μ := Γ.F⊗ₘΓ.σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hj

include hm hR hRt hLvalue hLroute in
theorem sourceNativeGame_profile_shape :
    ∀ᵐd ∂userProfileLaw (sourceNativeGame row hc R Λ hΛ PL α hα),
      ∀k, sourceDrawShape (Early.bidCap row) R (d k) :=
  ae_all_iff.mpr (fun k =>
    (measurePreserving_eval
      (fun _ : Fin m => userLaw (sourceNativeGame row hc R Λ hΛ PL α hα)) k).quasiMeasurePreserving.ae
      (sourceNativeGame_draw_shape row hm hc hR hRt hΛ PL hLvalue hLroute α hα))

end SourceShape

def sourcePhysicalCountTestOfRow (row : Uniform07.Row) (R Λ zG width ε : ℝ)
    (i : Fin m) (a : JointAction 2) (q : Fin 3 → ℝ) :
    UserProfile m 2 × Equiv.Perm (Fin 2) → ℝ :=
  sourcePhysicalCountTest (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
    Λ (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2) R
    (Uniform07.capacity m) (literalSourceAlpha row Λ zG width ε) i a q

theorem sourceNativeGame_broadcast_count_expect_physical
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ zG width ε : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2 ≤ zG) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (hLatom : ∀b : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = b} = 0)
    (i : Fin m) (a : JointAction 2) (ha0 : 0 < a.bid) (haR : a.bid < R)
    (ha2 : a.routeCount = 2) (q : Fin 3 → ℝ) :
    let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    ((problem Γ i).outcome a).expect q =
      ∫x, sourcePhysicalCountTestOfRow row R Λ zG width ε i a q x
        ∂(userProfileLaw Γ).prod (permLaw 2) := by
  let ξ := Uniform07.xi row
  let U := Early.bidCap row
  let zs := Uniform07.cutoff row/2
  let r := Early.demandRatio row
  let c := Uniform07.capacity m
  let α : ClassifiedContext m → unitInterval := literalSourceAlpha row Λ zG width ε
  have hα : Measurable α := measurable_literalSourceAlpha row hΛ zG width ε
  have hΛ0 := source_guard_multiplier_positive row hΛ
  let Γ := sourceNativeGame row hc R Λ hΛ0 PL α hα
  let μ := userLaw Γ
  let ρ := userProfileLaw Γ
  let V := ρ.prod (permLaw 2)
  letI : NullSingletonClass (submittedBidMeasure Γ) := by
    unfold submittedBidMeasure
    rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα]
    exact source_population_bid_atomless row m hm hc hR hRt PL hLatom
  let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
  have hseed : sourceSeedMeasure row m hc R PL = μB := by
    rw [sourceNativeGame_seed_measure row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα]
    simp only [μB,μ,sourceDrawTag_seed]
    rfl
  let X := focalInputContext R i a
  let B := fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
    privateCountMoment ξ (Uniform07.xi_pos row) (source_xi_lt_one row) c (X x) none i q
  let F := fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
    sourceCountCorrection ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ r U c α (X x) (sourceSeed μB zs (X x)) i q
  let H := fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
    if rivalHasSeed zs i (deleteFocal i x.1) then
      finitePathCountCorrection ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ r U c α (X x) i q else 0
  have hX : Measurable X := measurable_focalInputContext R i a
  have hB : Measurable B := (measurable_privateCountMoment ξ (Uniform07.xi_pos row)
    (source_xi_lt_one row) c i q).comp (hX.prodMk measurable_const)
  have hF : Measurable F := (measurable_sourceCountCorrection ξ (Uniform07.xi_pos row)
    (source_xi_lt_one row) Λ r U hΛ0 c α hα i q).comp
      (hX.prodMk ((measurable_sourceSeed μB zs).comp hX))
  have hH : Measurable H := Measurable.ite ((measurableSet_rivalHasSeed zs i).preimage
    ((measurable_deleteFocal i).comp measurable_fst))
    ((measurable_finitePathCountCorrection ξ (Uniform07.xi_pos row)
      (source_xi_lt_one row) Λ r U hΛ0 c α hα i q).comp hX) measurable_const
  have hBi : Integrable B V := Integrable.of_bound hB.aestronglyMeasurable
    (∑r : Fin 3, |q r|) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,B] using
        (abs_privateCountMoment_le ξ (Uniform07.xi_pos row) (source_xi_lt_one row) c (X x) none i q)))
  have hFi : Integrable F V := Integrable.of_bound hF.aestronglyMeasurable
    (2*∑r : Fin 3, |q r|) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,F] using
        (abs_sourceCountCorrection_le ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
          Λ r U c α (X x) (sourceSeed μB zs (X x)) i q)))
  have hHi : Integrable H V := by
    apply Integrable.of_bound hH.aestronglyMeasurable (2*∑r : Fin 3, |q r|)
    apply ae_of_all
    intro x
    dsimp only [H]
    split_ifs
    · simpa only [Real.norm_eq_abs] using abs_finitePathCountCorrection_le ξ
        (Uniform07.xi_pos row) (source_xi_lt_one row) Λ r U c α (X x) i q
    · simp only [norm_zero]
      positivity
  have hshape := sourceNativeGame_profile_shape row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα
  have hfull := sourceNativeGame_profile_support row hm hc hR hUR hRt hΛ0 PL hLvalue hLroute α hα
  have hroute : ∀ᵐu ∂μ, u.1.2.bid ≤ zs → u.1.2.routeCount = 2 := by
    filter_upwards [sourceNativeGame_draw_shape row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα]
      with u hu
    intro hb
    rcases hu with hl | hh
    · exact hl.2
    · exact False.elim ((not_le_of_gt ((source_seed_cutoff_lt_bidCap row).trans hUR))
        (hh.1.trans hb))
  have hnoatoms := actual_conditional_bid_atomless Γ
    ((measurable_sourceDrawTag zs U) (measurableSet_singleton 0))
  have hFH : (∫x, F x ∂V) = ∫x, H x ∂V := by
    rw [integral_prod_symm F hFi,integral_prod_symm H hHi]
    apply integral_congr_ae
    apply ae_of_all
    intro τ
    let Cr := fun d : RivalIndex i → UserDraw 2 => observedContext R 0 (focalLocalList i a τ 0 d)
    let Fr := fun d : RivalIndex i → UserDraw 2 =>
      sourceCountCorrection ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ r U c α (Cr d) (sourceSeed μB zs (Cr d)) i q
    let Hr := fun d : RivalIndex i → UserDraw 2 =>
      if rivalHasSeed zs i d then finitePathCountCorrection ξ (Uniform07.xi_pos row)
        (source_xi_lt_one row) Λ r U c α (Cr d) i q else 0
    have hCr : Measurable Cr := (measurable_observedContext R 0).comp (measurable_focalLocalList i a τ 0)
    have hFr : Measurable Fr := (measurable_sourceCountCorrection ξ (Uniform07.xi_pos row)
      (source_xi_lt_one row) Λ r U hΛ0 c α hα i q).comp
        (hCr.prodMk ((measurable_sourceSeed μB zs).comp hCr))
    have hHr : Measurable Hr := Measurable.ite (measurableSet_rivalHasSeed zs i)
      ((measurable_finitePathCountCorrection ξ (Uniform07.xi_pos row)
        (source_xi_lt_one row) Λ r U hΛ0 c α hα i q).comp hCr) measurable_const
    have hp := deleteFocal_preserves_iid i μ
    have heF : (fun d => F (d,τ)) = Fr ∘ deleteFocal i := by
      funext d
      simp only [F,X,focalInputContext,deviationList_eq_focalLocalList,Fr,Cr,Function.comp_apply]
    have heH : (fun d => H (d,τ)) = Hr ∘ deleteFocal i := by
      funext d
      simp only [H,X,focalInputContext,deviationList_eq_focalLocalList,Hr,Cr,Function.comp_apply]
    change (∫ d, F (d,τ) ∂ρ) = ∫ d, H (d,τ) ∂ρ
    rw [heF,heH]
    have hgen := ae_native_focal_context_generic Γ (κ := 1-ξ) (R := R)
      (by dsimp only [ξ]; linarith [source_xi_lt_one row])
      hfull i a ha0 haR ha2 τ 0
    calc
      _ = ∫d, Fr d ∂Measure.pi (fun _ : RivalIndex i => μ) := by
        rw [←hp.map_eq]
        exact (integral_map hp.measurable.aemeasurable hFr.aestronglyMeasurable).symm
      _ = ∫d, Hr d ∂Measure.pi (fun _ : RivalIndex i => μ) :=
        source_correction_integral_broadcast row μ i hΛ hR hguard hUR hzG (by omega) hε c
          a haR ha2 τ q hroute hgen hnoatoms
      _ = _ := by
        rw [←hp.map_eq]
        exact integral_map hp.measurable.aemeasurable hHr.aestronglyMeasurable
  dsimp only
  simp only [problem_outcome,CountLaw.expect_ofMeasure,integral_focalCount_eq_inputs]
  change (∫x, (∫s : Fin 2 → unitInterval, q (focalCount Γ i a ((x.1,s),x.2))
    ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) ∂V) = _
  calc
    _ = ∫x, B x+F x ∂V := by
      apply integral_congr_ae
      filter_upwards [(measurePreserving_fst (μ := ρ) (ν := permLaw 2)).quasiMeasurePreserving.ae hshape]
        with x hx
      rw [source_focal_private_moment row hc R Λ hΛ0 PL α hα hUR x.1 hx i a haR ha2 x.2 q,
        actual_privateCount_baseline_add_correction,hseed]
      rfl
    _ = ∫x, B x+H x ∂V := by rw [integral_add hBi hFi,integral_add hBi hHi,hFH]
    _ = _ := rfl

end FCAppendix.Affine.Uniform07Finishing
