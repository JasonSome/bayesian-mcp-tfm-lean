import FCAppendix.Affine.Uniform07Finishing.Native.SourcePhysicalCounts
import FCAppendix.Affine.Uniform07Finishing.Native.AuxiliaryProducerData

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine LowBody StrictNative Weighted ConditionalSuccess
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

omit [Nonempty (Fin m)] in
theorem observedContext_relabel (R : ℝ) (j : Fin 2) (L : LocalList m)
    (e : Equiv.Perm (Fin m)) :
    observedContext R j (L ∘ e.symm) = relabelContext e (observedContext R j L) := by
  have hc (k : Fin 4) : StrictTags.localCount R R (L ∘ e.symm) k =
      StrictTags.localCount R R L k :=
    Equiv.sum_comp e.symm (fun u => if StrictTags.tag R R (L u)=k then (1 : ℕ) else 0)
  have hb : broadcastPart R (L ∘ e.symm) = broadcastPart R L ∘ e.symm := rfl
  simp only [observedContext,relabelContext,hb,hc]

omit [Nonempty (Fin m)] in
theorem focalInputContext_relabel (R : ℝ) (e : Equiv.Perm (Fin m))
    (i : Fin m) (a : JointAction 2) (x : UserProfile m 2 × Equiv.Perm (Fin 2)) :
    focalInputContext R (e i) a (x.1 ∘ e.symm,x.2) =
      relabelContext e (focalInputContext R i a x) := by
  have hL := observe_deviated_relabel e i a x.1
    (fun _ : Fin 2 => (0 : unitInterval)) x.2 0
  change observedContext R 0 (deviationList (e i) a (x.1 ∘ e.symm) x.2 0) = _
  rw [show deviationList (e i) a (x.1 ∘ e.symm) x.2 0 =
    deviationList i a x.1 x.2 0 ∘ e.symm from hL]
  exact observedContext_relabel R 0 _ e

omit [Nonempty (Fin m)] in
theorem rivalHasSeed_relabel (zs : ℝ) (e : Equiv.Perm (Fin m)) (i : Fin m)
    (d : UserProfile m 2) :
    rivalHasSeed zs (e i) (deleteFocal (e i) (d ∘ e.symm)) ↔
      rivalHasSeed zs i (deleteFocal i d) := by
  constructor
  · rintro ⟨u,hu⟩
    have hne : e.symm u.val ≠ i := by
      intro h
      apply u.property
      exact (e.apply_symm_apply u.val).symm.trans (congrArg e h)
    exact ⟨⟨e.symm u.val,hne⟩,hu⟩
  · rintro ⟨u,hu⟩
    refine ⟨⟨e u.val,fun h => u.property (e.injective h)⟩,?_⟩
    simpa only [deleteFocal,Function.comp_apply,Equiv.symm_apply_apply] using hu

theorem sourcePhysicalCountTestOfRow_relabel (row : Uniform07.Row)
    (R Λ zG width ε : ℝ) (e : Equiv.Perm (Fin m)) (i : Fin m)
    (a : JointAction 2) (q : Fin 3 → ℝ) (x : UserProfile m 2 × Equiv.Perm (Fin 2))
    (hgeneric : contextCopyGeneric (1-Uniform07.xi row) i (focalInputContext R i a x)) :
    sourcePhysicalCountTestOfRow row R Λ zG width ε (e i) a q (x.1 ∘ e.symm,x.2) =
      sourcePhysicalCountTestOfRow row R Λ zG width ε i a q x := by
  have hg := fun P Q (_ : ResidualPotential.Feasible (focalInputContext R i a x).1
      (budget (Uniform07.capacity m) 0 (focalInputContext R i a x))
      (budget (Uniform07.capacity m) 1 (focalInputContext R i a x)) P)
    (_ : ResidualPotential.Feasible (focalInputContext R i a x).1
      (budget (Uniform07.capacity m) 0 (focalInputContext R i a x))
      (budget (Uniform07.capacity m) 1 (focalInputContext R i a x)) Q) => hgeneric P Q
  have hB := privateCountMoment_relabel (Uniform07.xi_pos row) (source_xi_lt_one row)
    (Uniform07.capacity m) e (focalInputContext R i a x) none i q hg
  simp only [Option.map_none] at hB
  have hP := finitePathCountCorrection_relabel (Uniform07.xi_pos row) (source_xi_lt_one row)
    Λ (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row)
    (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε (Uniform07.capacity m)
    e (focalInputContext R i a x) i q hg
  simp only [sourcePhysicalCountTestOfRow,sourcePhysicalCountTest,
    focalInputContext_relabel,rivalHasSeed_relabel,hB,literalSourceAlpha,hP]

theorem sourceNativeGame_positive_broadcast_outcome_identity
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
    (i l : Fin m) (a : JointAction 2) (ha0 : 0 < a.bid) (haR : a.bid < R)
    (ha2 : a.routeCount = 2) :
    let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    (problem Γ i).outcome a = (problem Γ l).outcome a := by
  let α : ClassifiedContext m → unitInterval := literalSourceAlpha row Λ zG width ε
  have hα : Measurable α := measurable_literalSourceAlpha row hΛ zG width ε
  have hΛ0 := source_guard_multiplier_positive row hΛ
  let Γ := sourceNativeGame row hc R Λ hΛ0 PL α hα
  let V := (userProfileLaw Γ).prod (permLaw 2)
  let e : Equiv.Perm (Fin m) := Equiv.swap i l
  have he : e i = l := Equiv.swap_apply_left _ _
  letI : NullSingletonClass (submittedBidMeasure Γ) := by
    unfold submittedBidMeasure
    rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα]
    exact source_population_bid_atomless row m hm hc hR hRt PL hLatom
  have hfull := sourceNativeGame_profile_support row hm hc hR hUR hRt hΛ0 PL hLvalue hLroute α hα
  have hgeneric : ∀ᵐx ∂V,
      contextCopyGeneric (1-Uniform07.xi row) i (focalInputContext R i a x) := by
    have hτ (τ : Equiv.Perm (Fin 2)) : ∀ᵐd ∂userProfileLaw Γ,
        contextCopyGeneric (1-Uniform07.xi row) i
          (focalInputContext R i a (d,τ)) := by
      have hg := ae_native_focal_context_generic Γ (κ := 1-Uniform07.xi row) (R := R)
        (by linarith [source_xi_lt_one row]) hfull i a ha0 haR ha2 τ 0
      have hd := (deleteFocal_preserves_iid i (userLaw Γ)).quasiMeasurePreserving.ae hg
      simpa only [userProfileLaw,focalInputContext,deviationList_eq_focalLocalList,
        Function.comp_def] using hd
    have hall : ∀ᵐd ∂userProfileLaw Γ, ∀τ,
        contextCopyGeneric (1-Uniform07.xi row) i (focalInputContext R i a (d,τ)) :=
      ae_all_iff.mpr hτ
    filter_upwards [(measurePreserving_fst (μ := userProfileLaw Γ)
      (ν := permLaw 2)).quasiMeasurePreserving.ae hall] with x hx
    exact hx x.2
  apply FiniteLaw.ext_expect
  intro q
  rw [sourceNativeGame_broadcast_count_expect_physical row hm hc hR hUR hRt hΛ
      hguard hzG hε PL hLvalue hLroute hLatom i a ha0 haR ha2 q,
    sourceNativeGame_broadcast_count_expect_physical row hm hc hR hUR hRt hΛ
      hguard hzG hε PL hLvalue hLroute hLatom l a ha0 haR ha2 q]
  let F := sourcePhysicalCountTestOfRow row R Λ zG width ε l a q
  have hF : Measurable F := measurable_sourcePhysicalCountTest
    (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
    Λ (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2) R hΛ0
    (Uniform07.capacity m) α hα l a q
  have hp := relabelInputs_measurePreserving Γ e
  calc
    _ = ∫x, F (x.1 ∘ e.symm,x.2) ∂V := by
      apply integral_congr_ae
      filter_upwards [hgeneric] with x hx
      simpa only [F,he] using (sourcePhysicalCountTestOfRow_relabel
        row R Λ zG width ε e i a q x hx).symm
    _ = ∫x, F x ∂V.map (fun x => (x.1 ∘ e.symm,x.2)) :=
      (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by
      dsimp only [V,userProfileLaw]
      rw [hp.map_eq]

theorem literalSourceNativeGame_positive_broadcast_outcome_identity
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
    (i l : Fin m) (a : JointAction 2) (ha0 : 0 < a.bid) (haR : a.bid < R)
    (ha2 : a.routeCount = 2) :
    (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).outcome a =
      (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) l).outcome a := by
  unfold literalSourceNativeGame
  rw [completeSourceNativeGame_outcome,completeSourceNativeGame_outcome]
  exact sourceNativeGame_positive_broadcast_outcome_identity row hm hc hR hUR hRt hΛ
    hguard hzG hε PL hLvalue hLroute hLatom i l a ha0 haR ha2

theorem UniformAuxiliaryData05.eventually_all_auxiliaryBoundary_identity
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D) :
    ∀ᶠ k in atTop, ∀row : Uniform07.Row, ∀u : Fin (D.start+k),
      (problem (D.market row k).native u).outcome (D.auxiliaryBoundary row k) =
        (problem (D.market row k).native (D.focal k)).outcome (D.auxiliaryBoundary row k) := by
  have hpos : ∀ᶠ k in atTop, ∀row : Uniform07.Row,
      0 < (D.auxiliaryBoundary row k).bid :=
    Filter.eventually_all.mpr (fun row => D.auxiliaryBoundary_eventually_positive K row)
  filter_upwards [hpos] with k hk
  intro row u
  let M := D.market row k
  letI : Nonempty (Fin (D.start+k)) := M.fin_nonempty
  have hguard : Uniform07.kappa row*M.R < M.Λ-Early.nativeRadius row := by
    have hg := (Crossover.Physical.source_auxiliary_floor_guards row).2.2.2
    have hR : M.R = sourceLowerPriceCeiling row := D.auxiliary_floor row k
    rw [hR]
    have hΛ := M.multiplier_lower
    have h54 : (54/100 : ℝ) = 27/50 := by norm_num
    rw [h54] at hΛ
    linarith
  have hz : Uniform07.cutoff row/2 ≤ M.z := by
    have hh := D.rejection_root row k
    have ht := Uniform07.cutoff_pos row
    linarith
  exact sourceNativeGame_positive_broadcast_outcome_identity row M.market_ge_two M.capacity_positive
    M.floor_positive M.cap_lt_floor M.floor_lt_cutoff M.multiplier_lower hguard hz
    M.guard_margin_positive M.lower M.lower_value M.lower_routes M.lower_atomless
    u (D.focal k) (D.auxiliaryBoundary row k) (hk row)
    ((D.auxiliaryBoundary_spec row k).1.trans_lt M.cap_lt_floor)
    (D.auxiliaryBoundary_spec row k).2.1

end FCAppendix.Affine.Uniform07Finishing
