import FCAppendix.Affine.Uniform07Finishing.Native.BoundaryIdentity
import FCAppendix.Affine.LowBody.PureCopyMonotonicity
import FCAppendix.Affine.Hybrid.EqualActiveResidual
import FCAppendix.Affine.Hybrid.NativeLowIncentives

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine LowBody StrictNative Weighted ConditionalSuccess
open Existence.PayOnceBounded (listBids)
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

theorem residual_selection_focalCopy_mono_of_bid_update
    {κ x : ℝ} (hκ : 0 < κ) (L L' : LocalList m) (d₀ d₁ : ℕ) (i : Fin m)
    (hpres : ∀ k, L k ≠ none ↔ L' k ≠ none)
    (hbid : ResidualPotential.bid L' = Function.update (ResidualPotential.bid L) i x)
    (hx : ResidualPotential.bid L i < x) :
    focalCopy (ResidualPotential.selection κ L d₀ d₁) i ≤
      focalCopy (ResidualPotential.selection κ L' d₀ d₁) i := by
  let P := ResidualPotential.selection κ L d₀ d₁
  let Q := ResidualPotential.selection κ L' d₀ d₁
  have hP := ResidualPotential.selection_feasible κ hκ.le L d₀ d₁
  have hQ := ResidualPotential.selection_feasible κ hκ.le L' d₀ d₁
  have hP' := (feasible_seed_change L L' d₀ d₁ hpres P).mp hP
  have hQ' := (feasible_seed_change L L' d₀ d₁ hpres Q).mpr hQ
  have hm₀ := residual_selection_max hκ.le L d₀ d₁ Q hQ'
  have hm₁ := residual_selection_max hκ.le L' d₀ d₁ P hP'
  change CompleteInformation.potential κ (ResidualPotential.bid L) Q.1 Q.2 ≤
    CompleteInformation.potential κ (ResidualPotential.bid L) P.1 P.2 at hm₀
  change CompleteInformation.potential κ (ResidualPotential.bid L') P.1 P.2 ≤
    CompleteInformation.potential κ (ResidualPotential.bid L') Q.1 Q.2 at hm₁
  rw [hbid,potential_update_focal,potential_update_focal] at hm₁
  exact focalCopy_mono_of_coefficient hκ P Q i (by nlinarith)

omit [Nonempty (Fin m)] in

theorem focalLocalList_broadcast_self (i : Fin m) (a : JointAction 2)
    (ha : a.routeCount = 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (d : RivalIndex i → UserDraw 2) : focalLocalList i a τ j d i = some a.bid := by
  simp [focalLocalList,observe,drawsRealization,insertFocalProfile,ha,firstK_full_two]

omit [Nonempty (Fin m)] in
theorem focalLocalList_other_action (i : Fin m) (a a' : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (d : RivalIndex i → UserDraw 2)
    (k : Fin m) (hk : k ≠ i) :
    focalLocalList i a τ j d k = focalLocalList i a' τ j d k := by
  simp [focalLocalList,observe,drawsRealization,insertFocalProfile,hk]

omit [Nonempty (Fin m)] in

theorem focal_lower_context_bid_change {R : ℝ} (i : Fin m) (a a' : JointAction 2)
    (haR : a.bid < R) (haR' : a'.bid < R) (ha : a.routeCount = 2)
    (ha' : a'.routeCount = 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (d : RivalIndex i → UserDraw 2) :
    let X := observedContext R j (focalLocalList i a τ j d)
    let Y := observedContext R j (focalLocalList i a' τ j d)
    X.2 = Y.2 ∧ X.1 i = some a.bid ∧ Y.1 i = some a'.bid ∧
      ∀ k, k ≠ i → X.1 k = Y.1 k := by
  let L := focalLocalList i a τ j d
  let L' := focalLocalList i a' τ j d
  have hself : L i = some a.bid := focalLocalList_broadcast_self i a ha τ j d
  have hself' : L' i = some a'.bid := focalLocalList_broadcast_self i a' ha' τ j d
  have hother (k : Fin m) (hk : k ≠ i) : L k = L' k :=
    focalLocalList_other_action i a a' τ j d k hk
  have htag (k : Fin m) : StrictTags.tag R R (L k) = StrictTags.tag R R (L' k) := by
    by_cases hk : k = i
    · subst k
      simp only [hself,hself',StrictTags.tag,if_pos haR,if_pos haR']
    · rw [hother k hk]
  have hcount (q : Fin 4) : StrictTags.localCount R R L q = StrictTags.localCount R R L' q := by
    unfold StrictTags.localCount
    exact Finset.sum_congr rfl (fun k _ => by rw [htag k])
  change (observedContext R j L).2 = (observedContext R j L').2 ∧
    (observedContext R j L).1 i = some a.bid ∧
    (observedContext R j L').1 i = some a'.bid ∧
    ∀ k, k ≠ i → (observedContext R j L).1 k = (observedContext R j L').1 k
  refine ⟨?_,?_,?_,?_⟩
  · simp only [observedContext,hcount]
  · simp only [observedContext,broadcastPart,StrictTags.lowList,hself,StrictTags.tag,if_pos haR,ite_true]
  · simp only [observedContext,broadcastPart,StrictTags.lowList,hself',StrictTags.tag,if_pos haR',ite_true]
  · intro k hk
    simp only [observedContext,broadcastPart,StrictTags.lowList,hother k hk]

private theorem success_test_mono {r s : Fin 3} (h : r ≤ s) :
    successIndicator r.val ≤ successIndicator s.val := by
  fin_cases r <;> fin_cases s <;> norm_num [successIndicator] at *

theorem private_baseline_success_mono_from_zero
    {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hb : 0 < b)
    (c : ℕ) (X Y : ClassifiedContext m) (i : Fin m)
    (hcounts : X.2 = Y.2) (hzero : X.1 i = some 0) (hnew : Y.1 i = some b)
    (hother : ∀ k, k ≠ i → X.1 k = Y.1 k) :
    privateCountMoment ξ hξ hξ1 c X none i (fun r => successIndicator r.val) ≤
      privateCountMoment ξ hξ hξ1 c Y none i (fun r => successIndicator r.val) := by
  have hpres (k : Fin m) : X.1 k ≠ none ↔ Y.1 k ≠ none := by
    by_cases hk : k = i
    · subst k
      simp [hzero,hnew]
    · rw [hother k hk]
  have hp : presentSet X.1 = presentSet Y.1 := by
    ext k
    simp only [presentSet,Finset.mem_filter,Finset.mem_univ,true_and,hpres]
  have hd (j : Fin 2) : budget c j X = budget c j Y := by
    simp only [budget,contextUpper,hcounts,hp]
  have hbid : ResidualPotential.bid Y.1 = Function.update (ResidualPotential.bid X.1) i b := by
    funext k
    by_cases hk : k = i
    · subst k
      simp only [ResidualPotential.bid,hnew,entryBid,Function.update_self,max_eq_left hb.le]
    · simp only [Function.update_of_ne hk,ResidualPotential.bid,←hother k hk]
  by_cases he : budget c 0 X = budget c 1 X
  · have hz : EqualCapacity.positiveMarginal ξ (budget c 0 X) (listBids X.1) i = 0 :=
      Hybrid.NativeContinuation.positiveMarginal_zero_of_nonpos ξ (budget c 0 X)
        (listBids X.1) i (by simp only [listBids_eq_entry,hzero,entryBid,le_refl])
    rw [privateCountMoment_equal _ _ _ _ _ _ he,hz]
    have hn : 0 ≤ privateCountMoment ξ hξ hξ1 c Y none i (fun r => successIndicator r.val) :=
      integral_nonneg (fun _ => successIndicator_nonneg _)
    simpa [twoCountPolynomial,successIndicator] using hn
  · have he' : budget c 0 Y ≠ budget c 1 Y := by simpa only [←hd 0,←hd 1] using he
    rw [privateCountMoment_none _ _ _ _ _ he,privateCountMoment_none _ _ _ _ _ he']
    apply success_test_mono
    unfold purePair
    rw [←hd 0,←hd 1]
    exact residual_selection_focalCopy_mono_of_bid_update (by linarith : 0 < 1-ξ)
      X.1 Y.1 _ _ i hpres hbid (by simpa only [ResidualPotential.bid,hzero,entryBid,max_self] using hb)

theorem sourceNativeGame_seed_broadcast_expect_baseline
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
    (i : Fin m) (a : JointAction 2) (haR : a.bid < R) (ha2 : a.routeCount = 2)
    (haz : a.bid ≤ Uniform07.cutoff row/2) (q : Fin 3 → ℝ) :
    let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    ((problem Γ i).outcome a).expect q =
      ∫x, privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        (Uniform07.capacity m) (focalInputContext R i a x) none i q
          ∂(userProfileLaw Γ).prod (permLaw 2) := by
  let α : ClassifiedContext m → unitInterval := literalSourceAlpha row Λ zG width ε
  have hα : Measurable α := measurable_literalSourceAlpha row hΛ zG width ε
  have hΛ0 := source_guard_multiplier_positive row hΛ
  let Γ := sourceNativeGame row hc R Λ hΛ0 PL α hα
  have hshape := sourceNativeGame_profile_shape row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα
  dsimp only
  simp only [problem_outcome,CountLaw.expect_ofMeasure,integral_focalCount_eq_inputs]
  change (∫x, (∫s : Fin 2 → unitInterval, q (focalCount Γ i a ((x.1,s),x.2))
    ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)))
      ∂(userProfileLaw Γ).prod (permLaw 2)) = _
  apply integral_congr_ae
  filter_upwards [(measurePreserving_fst (μ := userProfileLaw Γ)
    (ν := permLaw 2)).quasiMeasurePreserving.ae hshape] with x hx
  rw [source_focal_private_moment row hc R Λ hΛ0 PL α hα hUR x.1 hx i a haR ha2 x.2 q,
    actual_privateCount_baseline_add_correction]
  have hX := focalContext_nonnegative R i a x.2 0 (deleteFocal i x.1)
  have hB := focalContext_le_floor hR.le i a x.2 0 (deleteFocal i x.1)
  have hi : entryBid ((observedContext R 0 (focalLocalList i a x.2 0 (deleteFocal i x.1))).1 i) ≤
      Uniform07.cutoff row/2 := by
    rw [focalContext_entry_bid i a haR ha2 x.2 0]
    exact haz
  have hz := literal_sourceCountCorrection_seed_focal_zero row (width := width) hΛ hR hguard hzG
    (by omega : 0 < m) hε (Uniform07.capacity m)
    (sourceSeed (sourceSeedMeasure row m hc R PL) (Uniform07.cutoff row/2)
      (focalInputContext R i a x))
    (observedContext R 0 (focalLocalList i a x.2 0 (deleteFocal i x.1))) hX hB i hi q
  simp only [focalInputContext,deviationList_eq_focalLocalList] at hz
  simp only [focalInputContext,deviationList_eq_focalLocalList,α,literalSourceAlpha,
    hz,add_zero]

theorem sourceNativeGame_zero_broadcast_success_le
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
    (i : Fin m) (a₀ a : JointAction 2) (ha₀ : a₀.bid = 0) (ha₀2 : a₀.routeCount = 2)
    (ha : 0 < a.bid) (haz : a.bid ≤ Uniform07.cutoff row/2) (ha2 : a.routeCount = 2) :
    let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    ((problem Γ i).outcome a₀).success ≤ ((problem Γ i).outcome a).success := by
  let ξ := Uniform07.xi row
  let c := Uniform07.capacity m
  let α : ClassifiedContext m → unitInterval := literalSourceAlpha row Λ zG width ε
  have hα : Measurable α := measurable_literalSourceAlpha row hΛ zG width ε
  have hΛ0 := source_guard_multiplier_positive row hΛ
  let Γ := sourceNativeGame row hc R Λ hΛ0 PL α hα
  let V := (userProfileLaw Γ).prod (permLaw 2)
  let q : Fin 3 → ℝ := fun r => successIndicator r.val
  let B := fun a' : JointAction 2 => fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
    privateCountMoment ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
      c (focalInputContext R i a' x) none i q
  have hBi (a' : JointAction 2) : Integrable (B a') V := by
    have hinput : Measurable (fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
        (focalInputContext R i a' x, (none : Option (Finset (Fin m))))) :=
      (measurable_focalInputContext R i a').prodMk measurable_const
    have hb : Measurable (B a') := by
      convert! (measurable_privateCountMoment ξ (Uniform07.xi_pos row)
        (source_xi_lt_one row) c i q).comp hinput using 1
    exact Integrable.of_bound hb.aestronglyMeasurable (∑r : Fin 3, |q r|)
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using
        (abs_privateCountMoment_le ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
          c (focalInputContext R i a' x) none i q)))
  have hzR := (source_seed_cutoff_lt_bidCap row).trans hUR
  have haR : a.bid < R := haz.trans_lt hzR
  have ha₀R : a₀.bid < R := by simpa only [ha₀] using hR
  have ha₀z : a₀.bid ≤ Uniform07.cutoff row/2 := by
    rw [ha₀]
    exact (div_pos (Uniform07.cutoff_pos row) (by norm_num : (0 : ℝ) < 2)).le
  change ((problem Γ i).outcome a₀).expect q ≤ ((problem Γ i).outcome a).expect q
  rw [sourceNativeGame_seed_broadcast_expect_baseline row hm hc hR hUR hRt hΛ hguard hzG hε
      PL hLvalue hLroute i a₀ ha₀R ha₀2 ha₀z q,
    sourceNativeGame_seed_broadcast_expect_baseline row hm hc hR hUR hRt hΛ hguard hzG hε
      PL hLvalue hLroute i a haR ha2 haz q]
  apply integral_mono (hBi a₀) (hBi a)
  intro x
  obtain ⟨hcX,hzero,hnew,hother⟩ := focal_lower_context_bid_change i a₀ a ha₀R haR
    ha₀2 ha2 x.2 0 (deleteFocal i x.1)
  rw [ha₀] at hzero
  simpa only [B,ξ,c,q,focalInputContext,deviationList_eq_focalLocalList] using
    private_baseline_success_mono_from_zero (Uniform07.xi_pos row) (source_xi_lt_one row)
      ha c _ _ i hcX hzero hnew hother

theorem literalSourceNativeGame_zero_broadcast_payoff_le
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
    (i : Fin m) (v : ℝ) (hv : 0 ≤ v) (a₀ a : JointAction 2)
    (ha₀ : a₀.bid = 0) (ha₀2 : a₀.routeCount = 2)
    (ha : 0 < a.bid) (haz : a.bid ≤ Uniform07.cutoff row/2) (ha2 : a.routeCount = 2) :
    let Γ := literalSourceNativeGame row hc R Λ zG width ε hΛ PL
    (problem Γ i).payoff v a₀ ≤ (problem Γ i).payoff v a+2*a.bid := by
  let Γ := literalSourceNativeGame row hc R Λ zG width ε hΛ PL
  have hs : ((problem Γ i).outcome a₀).success ≤ ((problem Γ i).outcome a).success := by
    simpa only [Γ,literalSourceNativeGame,completeSourceNativeGame_outcome] using
      sourceNativeGame_zero_broadcast_success_le row hm hc hR hUR hRt hΛ hguard hzG hε
        PL hLvalue hLroute i a₀ a ha₀ ha₀2 ha haz ha2
  have hcA := actualBidPayment_le_two_bid Γ i a
  have hc₀ : actualBidPayment Γ i a₀ = 0 := by simp only [actualBidPayment,ha₀,zero_mul]
  change (problem Γ i).payoff v a₀ ≤ (problem Γ i).payoff v a+2*a.bid
  rw [actual_zero_base_payoff Γ rfl,actual_zero_base_payoff Γ rfl,hc₀,sub_zero]
  have hh := mul_le_mul_of_nonneg_left hs hv
  linarith

theorem literalSourceNativeGame_zero_broadcast_IC
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
    (i : Fin m) (v : ℝ) (hv : 0 ≤ v) (incumbent a₀ : JointAction 2)
    (ha₀ : a₀.bid = 0) (ha₀2 : a₀.routeCount = 2)
    (hpositive : ∀ a : JointAction 2, 0 < a.bid → a.routeCount = 2 → a.bid < R →
      (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).payoff v a ≤
        (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).payoff v incumbent) :
    (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).payoff v a₀ ≤
      (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).payoff v incumbent := by
  let Γ := literalSourceNativeGame row hc R Λ zG width ε hΛ PL
  by_contra hn
  have hgap : 0 < (problem Γ i).payoff v a₀-(problem Γ i).payoff v incumbent :=
    sub_pos.mpr (lt_of_not_ge hn)
  let b := min (Uniform07.cutoff row/4)
    (((problem Γ i).payoff v a₀-(problem Γ i).payoff v incumbent)/4)
  have hb : 0 < b := lt_min (div_pos (Uniform07.cutoff_pos row) (by norm_num))
    (div_pos hgap (by norm_num))
  have hbz : b ≤ Uniform07.cutoff row/2 :=
    (min_le_left _ _).trans (by linarith [Uniform07.cutoff_pos row])
  have hbR : b < R := hbz.trans_lt ((source_seed_cutoff_lt_bidCap row).trans hUR)
  let a := Hybrid.NativeLowIncentives.broadcast b hb.le
  have hi := hpositive a hb rfl hbR
  have hdom := literalSourceNativeGame_zero_broadcast_payoff_le row (width := width) hm hc hR hUR hRt hΛ
    hguard hzG hε PL hLvalue hLroute i v hv a₀ a ha₀ ha₀2 hb hbz rfl
  have hsmall : b ≤ ((problem Γ i).payoff v a₀-(problem Γ i).payoff v incumbent)/4 :=
    min_le_right _ _
  change (problem Γ i).payoff v a ≤ (problem Γ i).payoff v incumbent at hi
  change (problem Γ i).payoff v a₀ ≤ (problem Γ i).payoff v a+2*b at hdom
  linarith

theorem literalSourceNativeGame_common_broadcast_IC_of_positive_reference
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
    (reference : Fin m)
    (hIC : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)), ∀ a : JointAction 2,
      0 < a.bid → a.routeCount = 2 → a.bid < R →
      (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) reference).payoff x.1 a ≤
        (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) reference).payoff x.1 x.2) :
    ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)), ∀ i : Fin m, ∀ a : JointAction 2,
      a.routeCount = 2 → a.bid < R →
      (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).payoff x.1 a ≤
        (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).payoff x.1 x.2 := by
  let Γ := literalSourceNativeGame row hc R Λ zG width ε hΛ PL
  have hvalue : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)), x.1 ∈ Icc 0 (Uniform07.cutoff row) := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp
    rw [hLvalue]
    exact sourceLowerValueLaw_support row
  have hnonzero : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp (hLatom 0)
  have hsame (i l : Fin m) (a : JointAction 2) (ha : 0 < a.bid)
      (haR : a.bid < R) (ha2 : a.routeCount = 2) (v : ℝ) :
      (problem Γ i).payoff v a = (problem Γ l).payoff v a := by
    have he := literalSourceNativeGame_positive_broadcast_outcome_identity row (width := width) hm hc
      hR hUR hRt hΛ hguard hzG hε PL hLvalue hLroute hLatom i l a ha haR ha2
    change ((problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G =
      ((problem Γ l).outcome a).utility v a.bid Γ.g Γ.A Γ.G
    rw [he]
  filter_upwards [hIC,hLroute,hvalue,hnonzero] with x hx hshape hv hzero
  have hxb : 0 < x.2.bid := lt_of_le_of_ne x.2.bid_nonneg (Ne.symm hzero)
  have hpositive (i : Fin m) (a : JointAction 2) (ha : 0 < a.bid)
      (ha2 : a.routeCount = 2) (haR : a.bid < R) :
      (problem Γ i).payoff x.1 a ≤ (problem Γ i).payoff x.1 x.2 := by
    rw [hsame i reference a ha haR ha2,
      hsame i reference x.2 hxb (hshape.1.trans_lt hUR) hshape.2]
    exact hx a ha ha2 haR
  intro i a ha2 haR
  by_cases ha : 0 < a.bid
  · exact hpositive i a ha ha2 haR
  · have ha0 : a.bid = 0 := le_antisymm (le_of_not_gt ha) a.bid_nonneg
    exact literalSourceNativeGame_zero_broadcast_IC row hm hc hR hUR hRt hΛ
      hguard hzG hε PL hLvalue hLroute i x.1 hv.1 x.2 a ha0 ha2 (hpositive i)

end FCAppendix.Affine.Uniform07Finishing
