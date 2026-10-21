import FCAppendix.Affine.Uniform07Finishing.Native.CountContinuity

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine LowBody StrictNative Weighted ConditionalSuccess
open scoped BigOperators
variable {m : ℕ}

theorem observedContext_update_lower {R b b₀ : ℝ} (hb : b < R) (hb₀ : b₀ < R)
    (L : LocalList m) (i : Fin m) (hi : L i=some b₀) :
    observedContext R 0 (Function.update L i (some b)) =
      (Function.update (observedContext R 0 L).1 i (some b),(observedContext R 0 L).2) := by
  have ht (k : Fin m) : StrictTags.tag R R (Function.update L i (some b) k) =
      StrictTags.tag R R (L k) := by
    by_cases hk : k=i
    · subst k
      simp only [Function.update_self,hi,StrictTags.tag,if_pos hb,if_pos hb₀]
    · simp only [Function.update_of_ne hk]
  have hc (j : Fin 4) : StrictTags.localCount R R (Function.update L i (some b)) j =
      StrictTags.localCount R R L j := by
    simp only [StrictTags.localCount,ht]
  have hL : broadcastPart R (Function.update L i (some b)) =
      Function.update (broadcastPart R L) i (some b) := by
    funext k
    by_cases hk : k=i
    · subst k
      simp [broadcastPart,StrictTags.lowList,StrictTags.tag,Function.update_self,hb]
    · simp only [broadcastPart,StrictTags.lowList,Function.update_of_ne hk]
  simp only [observedContext,hc,hL]

theorem focalInputContext_capped_eq {U R : ℝ} (hUR : U < R)
    (i : Fin m) (b b₀ : Icc (0 : ℝ) U)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) :
    focalInputContext R i (sourceLowerBroadcastAction U b) x =
      cappedFocalContext (focalInputContext R i (sourceLowerBroadcastAction U b₀) x) i b := by
  let A := sourceLowerBroadcastAction U b
  let A₀ := sourceLowerBroadcastAction U b₀
  let L := deviationList i A₀ x.1 x.2 0
  have hi : L i=some (b₀ : ℝ) := by
    dsimp only [L]
    rw [deviationList_eq_focalLocalList]
    simp [focalLocalList,observe,drawsRealization,insertFocalProfile,A₀,
      sourceLowerBroadcastAction,firstK_full_two]
  have hupdate : deviationList i A x.1 x.2 0=Function.update L i (some (b : ℝ)) := by
    rw [deviationList_eq_focalLocalList]
    funext k
    by_cases hk : k=i
    · subst k
      simp [focalLocalList,observe,drawsRealization,insertFocalProfile,A,
        sourceLowerBroadcastAction,firstK_full_two]
    · simp only [Function.update_of_ne hk]
      dsimp only [L]
      rw [deviationList_eq_focalLocalList]
      simp only [focalLocalList,observe,drawsRealization,insertFocalProfile,dif_neg hk]
  change observedContext R 0 (deviationList i A x.1 x.2 0) = _
  rw [hupdate,observedContext_update_lower (b.2.2.trans_lt hUR) (b₀.2.2.trans_lt hUR) L i hi]
  rfl

theorem focalInputContext_capped_focal {U R : ℝ} (hUR : U < R)
    (i : Fin m) (b : Icc (0 : ℝ) U)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) :
    (focalInputContext R i (sourceLowerBroadcastAction U b) x).1 i = some (b : ℝ) := by
  simp [focalInputContext,observedContext,broadcastPart,StrictTags.lowList,StrictTags.tag,
    deviationList_eq_focalLocalList,focalLocalList,observe,drawsRealization,insertFocalProfile,
    sourceLowerBroadcastAction,firstK_full_two,b.2.2.trans_lt hUR]

theorem focalInputContext_capped_nonnegative {U R : ℝ}
    (i : Fin m) (b : Icc (0 : ℝ) U)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) :
    NonnegativeList (focalInputContext R i (sourceLowerBroadcastAction U b) x).1 := by
  simpa only [focalInputContext,deviationList_eq_focalLocalList] using
    focalContext_nonnegative R i (sourceLowerBroadcastAction U b) x.2 0 (deleteFocal i x.1)

theorem focalInputContext_capped_bid_le {U R : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    (i : Fin m) (b : Icc (0 : ℝ) U)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2))
    (hx : ∀k, sourceDrawShape U R (x.1 k)) :
    ∀k, entryBid ((focalInputContext R i (sourceLowerBroadcastAction U b) x).1 k) ≤ U := by
  let A := sourceLowerBroadcastAction U b
  let d' := Function.update x.1 i ((0,A),x.2)
  have hd' := updated_broadcast_classified x.1 (sourceDrawShape_classified hUR hx)
    i 0 A (b.2.2.trans_lt hUR) rfl x.2
  have hL : deviationList i A x.1 x.2 0=observe (drawsRealization d') 0 := by
    rw [deviationList_eq_focalLocalList]
    simp only [focalLocalList,insert_deleteFocal,d']
  change ∀k, entryBid (broadcastPart R (deviationList i A x.1 x.2 0) k) ≤ U
  rw [hL,broadcastPart_observe d' hd' 0]
  intro k
  by_cases hk : k=i
  · subst k
    simpa only [d',Function.update_self,A,sourceLowerBroadcastAction,
      if_pos (b.2.2.trans_lt hUR),entryBid] using b.2.2
  · simp only [d',Function.update_of_ne hk]
    rcases hx k with hl | hh
    · simpa only [if_pos (hl.1.trans_lt hUR),entryBid] using hl.1
    · simpa only [if_neg (not_lt.mpr hh.1),entryBid] using hU

variable [Nonempty (Fin m)]

theorem sourcePhysicalCountTest_positive_continuousAt
    (row : Uniform07.Row) {R Λ zG width ε : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε)
    (i : Fin m) (b₀ : Icc (0 : ℝ) (Early.bidCap row)) (hb₀ : 0 < (b₀ : ℝ))
    (q : Fin 3 → ℝ) (x : UserProfile m 2 × Equiv.Perm (Fin 2))
    (hx : ∀k, sourceDrawShape (Early.bidCap row) R (x.1 k))
    (hg : contextCopyGeneric (1-Uniform07.xi row) i
      (focalInputContext R i (sourceLowerBroadcastAction (Early.bidCap row) b₀) x)) :
    ContinuousAt (fun b : Icc (0 : ℝ) (Early.bidCap row) =>
      sourcePhysicalCountTestOfRow row R Λ zG width ε i
        (sourceLowerBroadcastAction (Early.bidCap row) b) q x) b₀ := by
  let X := focalInputContext R i (sourceLowerBroadcastAction (Early.bidCap row) b₀) x
  have hi := focalInputContext_capped_focal hUR i b₀ x
  have hX := focalInputContext_capped_nonnegative (R := R) i b₀ x
  have hcap := focalInputContext_capped_bid_le (Early.upper_floor_interface row).2.1.le
    hUR i b₀ x hx
  have hB := continuousAt_cappedFocalContext_privateNone (Uniform07.xi_pos row)
    (source_xi_lt_one row) (Uniform07.capacity m) X hX i b₀ hb₀ hi hg q
  have hC := continuousAt_cappedFocalContext_finiteCorrection (zG := zG) (width := width) row hΛ hR hguard hUR hm hε
    (Uniform07.capacity m) X hX hcap i b₀ hb₀ hi hg q
  let f := fun b : Icc (0 : ℝ) (Early.bidCap row) =>
    focalInputContext R i (sourceLowerBroadcastAction (Early.bidCap row) b) x
  have he : f = fun b => cappedFocalContext X i b := by
    funext b
    exact focalInputContext_capped_eq hUR i b b₀ x
  change ContinuousAt (fun b =>
    privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      (Uniform07.capacity m) (f b) none i q +
    if rivalHasSeed (Uniform07.cutoff row/2) i (deleteFocal i x.1) then
      finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) Λ (Early.demandRatio row) (Early.bidCap row)
        (Uniform07.capacity m) (literalSourceAlpha row Λ zG width ε) (f b) i q else 0) b₀
  rw [he]
  by_cases hs : rivalHasSeed (Uniform07.cutoff row/2) i (deleteFocal i x.1)
  · simp only [if_pos hs, literalSourceAlpha]
    convert! hB.add hC using 1
  · simpa only [if_neg hs,add_zero] using hB

theorem sourceNativeGame_positive_bid_count_expect_continuousAt
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ zG width ε : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2 ≤ zG) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (hLatom : ∀b : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = b} = 0)
    (i : Fin m) (b₀ : Icc (0 : ℝ) (Early.bidCap row))
    (hb₀ : 0 < (b₀ : ℝ)) (q : Fin 3 → ℝ) :
    let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    ContinuousAt (fun b : Icc (0 : ℝ) (Early.bidCap row) =>
      ((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).expect q) b₀ := by
  let α := literalSourceAlpha (m := m) row Λ zG width ε
  have hα : Measurable α := measurable_literalSourceAlpha row hΛ zG width ε
  have hΛ0 := source_guard_multiplier_positive row hΛ
  let Γ := sourceNativeGame row hc R Λ hΛ0 PL α hα
  let V := (userProfileLaw Γ).prod (permLaw 2)
  let F := fun (b : Icc (0 : ℝ) (Early.bidCap row))
      (x : UserProfile m 2 × Equiv.Perm (Fin 2)) =>
    sourcePhysicalCountTestOfRow row R Λ zG width ε i
      (sourceLowerBroadcastAction (Early.bidCap row) b) q x
  let A₀ := sourceLowerBroadcastAction (Early.bidCap row) b₀
  letI : NullSingletonClass (submittedBidMeasure Γ) := by
    unfold submittedBidMeasure
    rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα]
    exact source_population_bid_atomless row m hm hc hR hRt PL hLatom
  have hfull := sourceNativeGame_profile_support row hm hc hR hUR hRt hΛ0
    PL hLvalue hLroute α hα
  have hgeneric : ∀ᵐx ∂V,
      contextCopyGeneric (1-Uniform07.xi row) i (focalInputContext R i A₀ x) := by
    have hτ (τ : Equiv.Perm (Fin 2)) : ∀ᵐd ∂userProfileLaw Γ,
        contextCopyGeneric (1-Uniform07.xi row) i (focalInputContext R i A₀ (d,τ)) := by
      have hg := ae_native_focal_context_generic Γ (κ := 1-Uniform07.xi row) (R := R)
        (by linarith [source_xi_lt_one row]) hfull i A₀ hb₀
        (b₀.2.2.trans_lt hUR) rfl τ 0
      have hd := (deleteFocal_preserves_iid i (userLaw Γ)).quasiMeasurePreserving.ae hg
      simpa only [focalInputContext,deviationList_eq_focalLocalList,userProfileLaw] using hd
    have hall : ∀ᵐd ∂userProfileLaw Γ, ∀τ,
        contextCopyGeneric (1-Uniform07.xi row) i (focalInputContext R i A₀ (d,τ)) :=
      ae_all_iff.mpr hτ
    filter_upwards [(measurePreserving_fst (μ := userProfileLaw Γ)
      (ν := permLaw 2)).quasiMeasurePreserving.ae hall] with x hx
    exact hx x.2
  have hshape := (measurePreserving_fst (μ := userProfileLaw Γ)
    (ν := permLaw 2)).quasiMeasurePreserving.ae
      (sourceNativeGame_profile_shape row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα)
  have hmeas (b : Icc (0 : ℝ) (Early.bidCap row)) : Measurable (F b) :=
    measurable_sourcePhysicalCountTest (Uniform07.xi row) (Uniform07.xi_pos row)
      (source_xi_lt_one row) Λ (Early.demandRatio row) (Early.bidCap row)
      (Uniform07.cutoff row/2) R hΛ0 (Uniform07.capacity m) α hα i _ q
  have hint : ContinuousAt (fun b : Icc (0 : ℝ) (Early.bidCap row) => ∫x, F b x ∂V) b₀ := by
    apply MeasureTheory.continuousAt_of_dominated
      (F := F) (bound := fun _ => 3*∑r : Fin 3, |q r|)
      (Eventually.of_forall (fun b => (hmeas b).aestronglyMeasurable))
      (Eventually.of_forall (fun b => ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs,F,sourcePhysicalCountTestOfRow] using
          abs_sourcePhysicalCountTest_le (Uniform07.xi row) (Uniform07.xi_pos row)
            (source_xi_lt_one row) Λ (Early.demandRatio row) (Early.bidCap row)
            (Uniform07.cutoff row/2) R (Uniform07.capacity m) α i
            (sourceLowerBroadcastAction (Early.bidCap row) b) q x)))
      (integrable_const _) ?_
    filter_upwards [hshape,hgeneric] with x hx hg
    exact sourcePhysicalCountTest_positive_continuousAt row hR hUR hΛ hguard
      (by omega) hε i b₀ hb₀ q x hx hg
  apply hint.congr_of_eventuallyEq
  filter_upwards [(continuous_subtype_val : Continuous
    (fun b : Icc (0 : ℝ) (Early.bidCap row) => (b : ℝ))).continuousAt
      (Ioi_mem_nhds hb₀)] with b hb
  exact sourceNativeGame_broadcast_count_expect_physical row hm hc hR hUR hRt hΛ
    hguard hzG hε PL hLvalue hLroute hLatom i
    (sourceLowerBroadcastAction (Early.bidCap row) b) hb (b.2.2.trans_lt hUR) rfl q

theorem sourceNativeGame_positive_bid_payoff_continuousAt
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ zG width ε : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2 ≤ zG) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (hLatom : ∀b : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = b} = 0)
    (i : Fin m) (z : ℝ × Icc (0 : ℝ) (Early.bidCap row)) (hz : 0 < (z.2 : ℝ)) :
    let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    ContinuousAt (fun w : ℝ × Icc (0 : ℝ) (Early.bidCap row) =>
      (problem Γ i).payoff w.1 (sourceLowerBroadcastAction (Early.bidCap row) w.2)) z := by
  let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
    (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
  have hcount (q : Fin 3 → ℝ) := sourceNativeGame_positive_bid_count_expect_continuousAt
    row hm hc (width := width) hR hUR hRt hΛ hguard hzG hε PL hLvalue hLroute hLatom i z.2 hz q
  have hS : ContinuousAt (fun w : ℝ × Icc (0 : ℝ) (Early.bidCap row) =>
      ((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) w.2)).success) z :=
    (hcount (fun r => successIndicator r.val)).comp continuous_snd.continuousAt
  have hA : ContinuousAt (fun w : ℝ × Icc (0 : ℝ) (Early.bidCap row) =>
      ((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) w.2)).charge Γ.A) z :=
    (hcount (fun r => Γ.A.charge r.val)).comp continuous_snd.continuousAt
  have hG : ContinuousAt (fun w : ℝ × Icc (0 : ℝ) (Early.bidCap row) =>
      ((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) w.2)).charge Γ.G) z :=
    (hcount (fun r => Γ.G.charge r.val)).comp continuous_snd.continuousAt
  have hb : ContinuousAt (fun w : ℝ × Icc (0 : ℝ) (Early.bidCap row) => (w.2 : ℝ)) z :=
    (continuous_subtype_val.comp continuous_snd).continuousAt
  change ContinuousAt (fun w : ℝ × Icc (0 : ℝ) (Early.bidCap row) =>
    ((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) w.2)).utility
      w.1 (w.2 : ℝ) Γ.g Γ.A Γ.G) z
  simp only [CountLaw.utility_eq]
  exact ((continuous_fst.continuousAt.mul hS).sub (hb.mul hA)).sub
    (continuousAt_const.mul hG)

end FCAppendix.Affine.Uniform07Finishing
