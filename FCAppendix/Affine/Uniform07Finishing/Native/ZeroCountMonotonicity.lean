import FCAppendix.Affine.Uniform07Finishing.Native.ZeroBroadcastDomination
import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalKernels

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine LowBody StrictNative Weighted ConditionalSuccess
open Existence.PayOnceBounded (listBids)
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

theorem private_baseline_moment_mono_from_zero
    {ξ b : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hb : 0< b)
    (c : ℕ) (X Y : ClassifiedContext m) (i : Fin m)
    (hcounts : X.2=Y.2) (hzero : X.1 i=some 0) (hnew : Y.1 i=some b)
    (hother : ∀ k,k≠i→ X.1 k=Y.1 k)
    (q : Fin 3→ℝ) (hq : Monotone q) (hq0 : q 0=0) :
    privateCountMoment ξ hξ hξ1 c X none i q≤
      privateCountMoment ξ hξ hξ1 c Y none i q := by
  have hpres (k : Fin m) : X.1 k≠none↔Y.1 k≠none := by
    by_cases hk : k=i
    · subst k
      simp [hzero,hnew]
    · rw [hother k hk]
  have hp : presentSet X.1=presentSet Y.1 := by
    ext k
    simp only [presentSet,Finset.mem_filter,Finset.mem_univ,true_and,hpres]
  have hd (j : Fin 2) : budget c j X=budget c j Y := by
    simp only [budget,contextUpper,hcounts,hp]
  have hbid : ResidualPotential.bid Y.1=Function.update (ResidualPotential.bid X.1) i b := by
    funext k
    by_cases hk : k=i
    · subst k
      simp only [ResidualPotential.bid,hnew,entryBid,Function.update_self,max_eq_left hb.le]
    · simp only [Function.update_of_ne hk,ResidualPotential.bid,←hother k hk]
  by_cases he : budget c 0 X=budget c 1 X
  · have hz : EqualCapacity.positiveMarginal ξ (budget c 0 X) (listBids X.1) i=0 :=
      Hybrid.NativeContinuation.positiveMarginal_zero_of_nonpos ξ (budget c 0 X)
        (listBids X.1) i (by simp only [listBids_eq_entry,hzero,entryBid,le_refl])
    rw [privateCountMoment_equal _ _ _ _ _ _ he,hz]
    have hn : 0≤ privateCountMoment ξ hξ hξ1 c Y none i q := by
      apply integral_nonneg
      intro s
      change (0 : ℝ) ≤ q _
      rw [←hq0]
      exact hq (Fin.zero_le _)
    simpa only [twoCountPolynomial,hq0,mul_zero,mul_one,one_mul,add_zero,
      zero_add,sub_zero,zero_mul] using hn
  · have he' : budget c 0 Y≠budget c 1 Y := by simpa only [←hd 0,←hd 1] using he
    rw [privateCountMoment_none _ _ _ _ _ he,privateCountMoment_none _ _ _ _ _ he']
    apply hq
    unfold purePair
    rw [←hd 0,←hd 1]
    exact residual_selection_focalCopy_mono_of_bid_update (by linarith : 0<1-ξ)
      X.1 Y.1 _ _ i hpres hbid
      (by simpa only [ResidualPotential.bid,hzero,entryBid,max_self] using hb)

theorem sourceNativeGame_zero_broadcast_moment_le
    (row : Uniform07.Row) (hm : 2≤ m) (hc : 1≤ Uniform07.capacity m)
    {R Λ zG width ε : ℝ} (hR : 0< R) (hUR : Early.bidCap row< R)
    (hRt : R< Uniform07.cutoff row)
    (hΛ : (54/100:ℝ)*Uniform07.cutoff row<Λ)
    (hguard : Uniform07.kappa row*R<Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2≤ zG) (hε : 0<ε)
    (PL : ProbabilityMeasure (ℝ×JointAction 2))
    (hLvalue : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=(sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐx∂(PL : Measure (ℝ×JointAction 2)),
      x.2.bid≤ Early.bidCap row∧x.2.routeCount=2)
    (i : Fin m) (a₀ a : JointAction 2) (ha₀ : a₀.bid=0) (ha₀2 : a₀.routeCount=2)
    (ha : 0< a.bid) (haz : a.bid≤ Uniform07.cutoff row/2) (ha2 : a.routeCount=2)
    (q : Fin 3→ℝ) (hq : Monotone q) (hq0 : q 0=0) :
    let Γ:=sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    ((problem Γ i).outcome a₀).expect q≤((problem Γ i).outcome a).expect q := by
  let ξ:=Uniform07.xi row
  let c:=Uniform07.capacity m
  let α : ClassifiedContext m→ unitInterval:=literalSourceAlpha row Λ zG width ε
  have hα : Measurable α:=measurable_literalSourceAlpha row hΛ zG width ε
  let Γ:=sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL α hα
  let V:=(userProfileLaw Γ).prod (permLaw 2)
  let B:=fun a' : JointAction 2=>fun x : UserProfile m 2×Equiv.Perm (Fin 2)=>
    privateCountMoment ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
      c (focalInputContext R i a' x) none i q
  have hBi (a' : JointAction 2) : Integrable (B a') V := by
    have hinput : Measurable (fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
        (focalInputContext R i a' x, (none : Option (Finset (Fin m))))) :=
      (measurable_focalInputContext R i a').prodMk measurable_const
    have hb : Measurable (B a') := by
      convert! (measurable_privateCountMoment ξ (Uniform07.xi_pos row)
        (source_xi_lt_one row) c i q).comp hinput using 1
    exact Integrable.of_bound hb.aestronglyMeasurable (∑r : Fin 3,|q r|)
      (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs] using
        (abs_privateCountMoment_le ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
          c (focalInputContext R i a' x) none i q)))
  have hzR:=(source_seed_cutoff_lt_bidCap row).trans hUR
  have haR : a.bid< R:=haz.trans_lt hzR
  have ha₀R : a₀.bid< R:=by simpa only [ha₀] using hR
  have ha₀z : a₀.bid≤ Uniform07.cutoff row/2:=by
    rw [ha₀]
    exact (half_pos (Uniform07.cutoff_pos row)).le
  dsimp only
  rw [sourceNativeGame_seed_broadcast_expect_baseline row hm hc hR hUR hRt hΛ hguard hzG hε
      PL hLvalue hLroute i a₀ ha₀R ha₀2 ha₀z q,
    sourceNativeGame_seed_broadcast_expect_baseline row hm hc hR hUR hRt hΛ hguard hzG hε
      PL hLvalue hLroute i a haR ha2 haz q]
  apply integral_mono (hBi a₀) (hBi a)
  intro x
  obtain ⟨hcX,hzero,hnew,hother⟩:=focal_lower_context_bid_change i a₀ a ha₀R haR
    ha₀2 ha2 x.2 0 (deleteFocal i x.1)
  rw [ha₀] at hzero
  simpa only [B,ξ,c,focalInputContext,deviationList_eq_focalLocalList] using
    private_baseline_moment_mono_from_zero (Uniform07.xi_pos row) (source_xi_lt_one row)
      ha c _ _ i hcX hzero hnew hother q hq hq0

theorem literalSourceNativeGame_zero_broadcast_moment_le
    (row : Uniform07.Row) (hm : 2≤ m) (hc : 1≤ Uniform07.capacity m)
    {R Λ zG width ε : ℝ} (hR : 0< R) (hUR : Early.bidCap row< R)
    (hRt : R< Uniform07.cutoff row)
    (hΛ : (54/100:ℝ)*Uniform07.cutoff row<Λ)
    (hguard : Uniform07.kappa row*R<Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2≤ zG) (hε : 0<ε)
    (PL : ProbabilityMeasure (ℝ×JointAction 2))
    (hLvalue : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=(sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐx∂(PL : Measure (ℝ×JointAction 2)),
      x.2.bid≤ Early.bidCap row∧x.2.routeCount=2)
    (i : Fin m) (a₀ a : JointAction 2) (ha₀ : a₀.bid=0) (ha₀2 : a₀.routeCount=2)
    (ha : 0< a.bid) (haz : a.bid≤ Uniform07.cutoff row/2) (ha2 : a.routeCount=2)
    (q : Fin 3→ℝ) (hq : Monotone q) (hq0 : q 0=0) :
    let Γ:=literalSourceNativeGame row hc R Λ zG width ε hΛ PL
    ((problem Γ i).outcome a₀).expect q≤((problem Γ i).outcome a).expect q := by
  simpa only [literalSourceNativeGame,completeSourceNativeGame_outcome] using
    sourceNativeGame_zero_broadcast_moment_le row hm hc hR hUR hRt hΛ hguard hzG hε
      PL hLvalue hLroute i a₀ a ha₀ ha₀2 ha haz ha2 q hq hq0

end FCAppendix.Affine.Uniform07Finishing
