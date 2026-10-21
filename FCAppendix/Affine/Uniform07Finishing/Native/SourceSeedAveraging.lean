import FCAppendix.Affine.Uniform07Finishing.Native.CountRelabel
import FCAppendix.Affine.Uniform07Finishing.Native.SourceSamplingProbability

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative Weighted
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

theorem measurable_sourceCountCorrection (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (hΛ : 0 < Λ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (hα : Measurable α) (i : Fin m) (q : Fin 3 → ℝ) :
    Measurable (fun p : ClassifiedContext m × Option unitInterval =>
      sourceCountCorrection ξ hξ hξ1 Λ r U c α p.1 p.2 i q) := by
  have hp := Weighted.measurable_sourcePlanFromSeed ξ Λ r U hξ hΛ c α hα
  have hinput : Measurable (fun p : ClassifiedContext m × Option unitInterval =>
      (p.1,sourcePlanFromSeed ξ Λ r U c α p.1 p.2)) := measurable_fst.prodMk hp
  have hzero : Measurable (fun p : ClassifiedContext m × Option unitInterval =>
      (p.1,(none : Option (Finset (Fin m))))) := measurable_fst.prodMk measurable_const
  have hf := (measurable_privateCountMoment ξ hξ hξ1 c i q).comp hinput
  have hz := (measurable_privateCountMoment ξ hξ hξ1 c i q).comp hzero
  change Measurable (fun p : ClassifiedContext m × Option unitInterval =>
    privateCountMoment ξ hξ hξ1 c p.1 (sourcePlanFromSeed ξ Λ r U c α p.1 p.2) i q -
      privateCountMoment ξ hξ hξ1 c p.1 none i q)
  exact hf.sub hz

theorem abs_sourceCountCorrection_le (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (X : ClassifiedContext m) (seed : Option unitInterval) (i : Fin m) (q : Fin 3 → ℝ) :
    |sourceCountCorrection ξ hξ hξ1 Λ r U c α X seed i q| ≤ 2*∑r : Fin 3, |q r| := by
  unfold sourceCountCorrection
  have h1 := abs_privateCountMoment_le ξ hξ hξ1 c X
    (sourcePlanFromSeed ξ Λ r U c α X seed) i q
  have h0 := abs_privateCountMoment_le ξ hξ hξ1 c X none i q
  exact (abs_sub _ _).trans (by linarith)

theorem measurable_finitePathCountCorrection (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (hΛ : 0 < Λ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (hα : Measurable α) (i : Fin m) (q : Fin 3 → ℝ) :
    Measurable (fun X : ClassifiedContext m => finitePathCountCorrection ξ hξ hξ1 Λ r U c α X i q) := by
  have hh := (measurable_sourceCountCorrection ξ hξ hξ1 Λ r U hΛ c α hα i q).comp
    (measurable_fst.prodMk (measurable_some.comp measurable_snd))
  have hi := (hh.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure unitInterval))).measurable
  simpa only [Function.comp_def,integral_sourceCountCorrection] using hi

theorem abs_finitePathCountCorrection_le (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ) :
    |finitePathCountCorrection ξ hξ hξ1 Λ r U c α X i q| ≤ 2*∑r : Fin 3, |q r| := by
  rw [←integral_sourceCountCorrection]
  have hb : ∀ᵐs : unitInterval ∂volume,
      ‖sourceCountCorrection ξ hξ hξ1 Λ r U c α X (some s) i q‖ ≤ 2*∑r : Fin 3, |q r| :=
    ae_of_all _ (fun s => by simpa only [Real.norm_eq_abs] using
      abs_sourceCountCorrection_le ξ hξ hξ1 Λ r U c α X (some s) i q)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

omit [Nonempty (Fin m)] in
theorem focalContext_nonnegative (R : ℝ) (i : Fin m) (A : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (d : RivalIndex i → UserDraw 2) :
    NonnegativeList (observedContext R j (focalLocalList i A τ j d)).1 :=
  source_broadcastPart_nonnegative _
    ((feasibleObservedList_iff_nonnegative j _).mp ⟨insertFocalProfile i 0 A τ d,rfl⟩)

omit [Nonempty (Fin m)] in
theorem focalContext_le_floor {R : ℝ} (hR : 0 ≤ R) (i : Fin m) (A : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (d : RivalIndex i → UserDraw 2) :
    ∀k, entryBid ((observedContext R j (focalLocalList i A τ j d)).1 k) ≤ R :=
  source_broadcastPart_le_floor hR _

attribute [local irreducible] sourceCountCorrection finitePathCountCorrection

theorem conditional_source_correction_integral (row : Uniform07.Row)
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] (i : Fin m)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hUR : Early.bidCap row < R) (hzG : Uniform07.cutoff row/2 ≤ zG)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (A : JointAction 2) (hA : Uniform07.cutoff row/2 < A.bid)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (q : Fin 3 → ℝ)
    (hroute : ∀ᵐu ∂μ, u.1.2.bid ≤ Uniform07.cutoff row/2 → u.1.2.routeCount = 2)
    (hgeneric : ∀ᵐd ∂Measure.pi (fun _ : RivalIndex i => μ),
      contextCopyGeneric (1-Uniform07.xi row) i (observedContext R j (focalLocalList i A τ j d)))
    (k : RivalIndex i → Fin 3)
    (hmass : ∀u, μ (sourceDrawTag (Uniform07.cutoff row/2) (Early.bidCap row) ⁻¹' {k u}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {u : RivalIndex i // k u = 0})
    (hnoatoms : ∀b : ℝ,
      ((cond μ (sourceDrawTag (Uniform07.cutoff row/2) (Early.bidCap row) ⁻¹' {0})).map
        (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0) :
    let zs := Uniform07.cutoff row/2
    let ν := cond (Measure.pi (fun _ : RivalIndex i => μ))
      (Hybrid.categoryFiber (sourceDrawTag zs (Early.bidCap row)) k)
    let μB := (cond μ (sourceDrawTag zs (Early.bidCap row) ⁻¹' {0})).map
      (fun u : UserDraw 2 => u.1.2.bid)
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    let C := fun d => observedContext R j (focalLocalList i A τ j d)
    (∫d, sourceCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) c α (C d)
      (sourceSeed μB zs (C d)) i q ∂ν) =
    ∫d, finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) c α (C d) i q ∂ν := by
  let zs := Uniform07.cutoff row/2
  let U := Early.bidCap row
  let ξ := Uniform07.xi row
  have hξ : 0 < ξ := Uniform07.xi_pos row
  have hξ1 : ξ < 1 := source_xi_lt_one row
  let α : ClassifiedContext m → unitInterval := sourceGuardAlpha ξ Λ (Early.nativeRadius row) (Early.demandRatio row)
    U (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c
  let ν := cond (Measure.pi (fun _ : RivalIndex i => μ))
    (Hybrid.categoryFiber (sourceDrawTag zs U) k)
  have hνmass : (Measure.pi (fun _ : RivalIndex i => μ))
      (Hybrid.categoryFiber (sourceDrawTag zs U) k) ≠ 0 := by
    rw [Hybrid.categoryFiber_mass]
    exact Finset.prod_ne_zero_iff.mpr (fun u _ => hmass u)
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hνmass
  letI (u : {u : RivalIndex i // k u ≠ 0}) : IsProbabilityMeasure
      (cond μ (sourceDrawTag zs U ⁻¹' {k u})) := cond_isProbabilityMeasure (hmass u)
  let rest := Measure.pi (fun u : {u : RivalIndex i // k u ≠ 0} => cond μ (sourceDrawTag zs U ⁻¹' {k u}))
  let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
  let C := fun d : RivalIndex i → UserDraw 2 => observedContext R j (focalLocalList i A τ j d)
  let Ce := erasedFocalContext R i A τ j k
  let drop := fun d : RivalIndex i → UserDraw 2 =>
    fun u : {u : RivalIndex i // k u ≠ 0} => d u
  have hC : Measurable C := (measurable_observedContext R j).comp (measurable_focalLocalList i A τ j)
  have hCe : Measurable Ce := measurable_erasedFocalContext R i A τ j k
  have hdrop : Measurable drop := measurable_pi_lambda _ (fun u => measurable_pi_apply u.val)
  have hΛ0 := source_guard_multiplier_positive row hΛ
  have hα : Measurable α :=
    measurable_sourceGuardAlpha (Uniform07.xi_pos row) (Early.native_sampling_margin_guards row).1
      (source_guard_root_positive row hΛ) (div_pos (Uniform07.cutoff_pos row) (by norm_num))
      (Early.demandRatio row) U zG (Uniform07.cutoff row) width ε c
  let Corr := sourceCountCorrection ξ hξ hξ1 Λ (Early.demandRatio row) U c α
  let PathCorr := finitePathCountCorrection ξ hξ hξ1 Λ (Early.demandRatio row) U c α
  have hCorr : Measurable (fun p : ClassifiedContext m × Option unitInterval => Corr p.1 p.2 i q) :=
    measurable_sourceCountCorrection ξ hξ hξ1 Λ (Early.demandRatio row) U hΛ0 c α hα i q
  have hPath : Measurable (fun X : ClassifiedContext m => PathCorr X i q) :=
    measurable_finitePathCountCorrection ξ hξ hξ1 Λ (Early.demandRatio row) U hΛ0 c α hα i q
  let F := fun p : Option unitInterval × ({u : RivalIndex i // k u ≠ 0} → UserDraw 2) =>
    Corr (Ce p.2) p.1 i q
  have hF : Measurable F := hCorr.comp ((hCe.comp measurable_snd).prodMk measurable_fst)
  have hFi : Integrable
      (fun p : unitInterval × ({u : RivalIndex i // k u ≠ 0} → UserDraw 2) => F (some p.1,p.2))
      ((volume : Measure unitInterval).prod rest) := by
    apply Integrable.of_bound (hF.comp (measurable_some.prodMap measurable_id)).aestronglyMeasurable
      (2*∑r : Fin 3, |q r|)
    exact ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs,F,Corr,Function.comp_apply,Prod.map,id_eq] using
        (abs_sourceCountCorrection_le ξ hξ hξ1 Λ (Early.demandRatio row) U c α (Ce p.2) (some p.1) i q))
  have hfull : ∀ᵐd ∂Measure.pi (fun _ : RivalIndex i => μ),
      ∀u, (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2 :=
    ae_all_iff.mpr (fun u =>
      (measurePreserving_eval (fun _ : RivalIndex i => μ) u).quasiMeasurePreserving.ae hroute)
  have hcell := Hybrid.measurableSet_categoryFiber (sourceDrawTag zs U) (measurable_sourceDrawTag zs U) k
  have hc : ∀ᵐd ∂ν, ∀u, sourceDrawTag zs U (d u) = k u := by
    filter_upwards [cond_ae_mem (Measure.pi (fun _ : RivalIndex i => μ)) hcell] with d hd
    exact fun u => hd u (mem_univ u)
  have hroutes := cond_ae_of_ae (Measure.pi (fun _ : RivalIndex i => μ)) hcell hfull
  have hgen := cond_ae_of_ae (Measure.pi (fun _ : RivalIndex i => μ)) hcell hgeneric
  have hz0 : 0 ≤ zs := (div_pos (Uniform07.cutoff_pos row) (by norm_num)).le
  have hzR : zs < R := (source_seed_cutoff_lt_bidCap row).trans hUR
  have herase : ∀ᵐd ∂ν, ∀seed, Corr (C d) seed i q = Corr (Ce (drop d)) seed i q := by
    filter_upwards [hc,hroutes,hgen] with d hdc hdr hdg
    intro seed
    exact literal_sourceCountCorrection_seed_change row hΛ hR hguard hzG hm hε c seed
      (C d) (Ce (drop d)) (focalContext_nonnegative R i A τ j d)
      (focalContext_nonnegative R i A τ j (restoreNonseedRivals i k (drop d)))
      (focalContext_le_floor hR.le i A τ j d)
      (focalContext_le_floor hR.le i A τ j (restoreNonseedRivals i k (drop d)))
      (erasedFocalContext_seed_equivalent i hz0 hzR A τ j d k hdc hdr)
      i q (fun P Q _ _ hh => hdg P Q hh)
  have hseed : Measurable (fun d => sourceSeed μB zs (C d)) := (measurable_sourceSeed μB zs).comp hC
  have hjoint := forced_focal_seed_joint_profile μ i hzR A hA τ j hroute k hmass n e hnoatoms
  letI : IsProbabilityMeasure ((volume : Measure unitInterval).map (some : unitInterval → Option unitInterval)) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hdropLaw : ν.map drop = rest := by
    have hh := congrArg (fun M => M.map Prod.snd) hjoint
    rw [Measure.map_map measurable_snd (hseed.prodMk hdrop),
      (measurePreserving_snd (μ := (volume : Measure unitInterval).map some) (ν := rest)).map_eq] at hh
    exact hh
  change (∫d, Corr (C d) (sourceSeed μB zs (C d)) i q ∂ν) = ∫d, PathCorr (C d) i q ∂ν
  calc
    _ = ∫d, F (sourceSeed μB zs (C d),drop d) ∂ν :=
      integral_congr_ae (herase.mono (fun d hd => hd _))
    _ = ∫p, F p ∂((volume : Measure unitInterval).map some).prod rest := by
      rw [←hjoint]
      exact (integral_map (hseed.prodMk hdrop).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫p : unitInterval × ({u : RivalIndex i // k u ≠ 0} → UserDraw 2),
        F (some p.1,p.2) ∂(volume : Measure unitInterval).prod rest := by
      have hprod : ((volume : Measure unitInterval).map some).prod rest =
          ((volume : Measure unitInterval).prod rest).map (Prod.map some id) := by
        simpa only [Measure.map_id] using Measure.map_prod_map
          (volume : Measure unitInterval) rest measurable_some measurable_id
      rw [hprod,integral_map (measurable_some.prodMap measurable_id).aemeasurable hF.aestronglyMeasurable]
      rfl
    _ = ∫d, ∫s : unitInterval, F (some s,d) ∂volume ∂rest := integral_prod_symm _ hFi
    _ = ∫d, PathCorr (Ce d) i q ∂rest := by
      apply integral_congr_ae
      exact ae_of_all _ (fun d => integral_sourceCountCorrection ξ hξ hξ1
        Λ (Early.demandRatio row) U c α (Ce d) i q)
    _ = ∫d, PathCorr (Ce (drop d)) i q ∂ν := by
      rw [←hdropLaw]
      exact integral_map hdrop.aemeasurable (hPath.comp hCe).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [herase] with d hd
      dsimp only [PathCorr]
      rw [←integral_sourceCountCorrection,←integral_sourceCountCorrection]
      exact integral_congr_ae (ae_of_all _ (fun s => (hd (some s)).symm))

def rivalHasSeed (zs : ℝ) (i : Fin m) (d : RivalIndex i → UserDraw 2) : Prop :=
  ∃u, (d u).1.2.bid ≤ zs

omit [Nonempty (Fin m)] in
theorem measurableSet_rivalHasSeed (zs : ℝ) (i : Fin m) :
    MeasurableSet {d : RivalIndex i → UserDraw 2 | rivalHasSeed zs i d} := by
  simp only [rivalHasSeed,setOf_exists]
  exact MeasurableSet.iUnion (fun u =>
    measurableSet_le (measurable_draw_bid.comp (measurable_pi_apply u)) measurable_const)

lemma integral_eq_of_finite_cond {X K : Type*} [MeasurableSpace X]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → K) (hT : Measurable T)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hcell : ∀k, μ (T ⁻¹' {k}) ≠ 0 →
      (∫x, f x ∂cond μ (T ⁻¹' {k})) = ∫x, g x ∂cond μ (T ⁻¹' {k})) :
    (∫x, f x ∂μ) = ∫x, g x ∂μ :=
  le_antisymm (integral_le_of_finite_cond μ T hT f g hf hg (fun k hk => (hcell k hk).le))
    (integral_le_of_finite_cond μ T hT g f hg hf (fun k hk => (hcell k hk).ge))

theorem source_correction_integral (row : Uniform07.Row)
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] (i : Fin m)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hUR : Early.bidCap row < R) (hzG : Uniform07.cutoff row/2 ≤ zG)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (A : JointAction 2) (hA : Uniform07.cutoff row/2 < A.bid)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (q : Fin 3 → ℝ)
    (hroute : ∀ᵐu ∂μ, u.1.2.bid ≤ Uniform07.cutoff row/2 → u.1.2.routeCount = 2)
    (hgeneric : ∀ᵐd ∂Measure.pi (fun _ : RivalIndex i => μ),
      contextCopyGeneric (1-Uniform07.xi row) i (observedContext R j (focalLocalList i A τ j d)))
    (hnoatoms : ∀b : ℝ,
      ((cond μ (sourceDrawTag (Uniform07.cutoff row/2) (Early.bidCap row) ⁻¹' {0})).map
        (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0) :
    let zs := Uniform07.cutoff row/2
    let μB := (cond μ (sourceDrawTag zs (Early.bidCap row) ⁻¹' {0})).map
      (fun u : UserDraw 2 => u.1.2.bid)
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    let C := fun d => observedContext R j (focalLocalList i A τ j d)
    (∫d, sourceCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) c α (C d)
      (sourceSeed μB zs (C d)) i q ∂Measure.pi (fun _ : RivalIndex i => μ)) =
    ∫d, (if rivalHasSeed zs i d then
      finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ (Early.demandRatio row) (Early.bidCap row) c α (C d) i q else 0)
      ∂Measure.pi (fun _ : RivalIndex i => μ) := by
  let zs := Uniform07.cutoff row/2
  let U := Early.bidCap row
  let ξ := Uniform07.xi row
  let ν := Measure.pi (fun _ : RivalIndex i => μ)
  let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
  let α : ClassifiedContext m → unitInterval := sourceGuardAlpha ξ Λ (Early.nativeRadius row) (Early.demandRatio row)
    U (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c
  let C := fun d : RivalIndex i → UserDraw 2 => observedContext R j (focalLocalList i A τ j d)
  let Corr := sourceCountCorrection ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
    Λ (Early.demandRatio row) U c α
  let PathCorr := finitePathCountCorrection ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
    Λ (Early.demandRatio row) U c α
  let f := fun d => Corr (C d) (sourceSeed μB zs (C d)) i q
  let g := fun d => if rivalHasSeed zs i d then PathCorr (C d) i q else 0
  let T := fun d : RivalIndex i → UserDraw 2 => fun u => sourceDrawTag zs U (d u)
  have hC : Measurable C := (measurable_observedContext R j).comp (measurable_focalLocalList i A τ j)
  have hT : Measurable T := measurable_pi_lambda _ (fun u =>
    (measurable_sourceDrawTag zs U).comp (measurable_pi_apply u))
  have hα : Measurable α := measurable_sourceGuardAlpha (Uniform07.xi_pos row)
    (Early.native_sampling_margin_guards row).1 (source_guard_root_positive row hΛ)
    (div_pos (Uniform07.cutoff_pos row) (by norm_num)) (Early.demandRatio row)
    U zG (Uniform07.cutoff row) width ε c
  have hCorr := measurable_sourceCountCorrection ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
    Λ (Early.demandRatio row) U (source_guard_multiplier_positive row hΛ) c α hα i q
  have hf : Measurable f := hCorr.comp (hC.prodMk ((measurable_sourceSeed μB zs).comp hC))
  have hg : Measurable g := Measurable.ite (measurableSet_rivalHasSeed zs i)
    ((measurable_finitePathCountCorrection ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) U (source_guard_multiplier_positive row hΛ) c α hα i q).comp hC)
    measurable_const
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable
    (2*∑r : Fin 3, |q r|) (ae_of_all _ (fun d => by
      simpa only [Real.norm_eq_abs] using
        (abs_sourceCountCorrection_le ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
          Λ (Early.demandRatio row) U c α (C d) (sourceSeed μB zs (C d)) i q)))
  have hgi : Integrable g ν := by
    apply Integrable.of_bound hg.aestronglyMeasurable (2*∑r : Fin 3, |q r|)
    apply ae_of_all
    intro d
    dsimp only [g]
    split_ifs
    · simpa only [Real.norm_eq_abs] using abs_finitePathCountCorrection_le ξ
        (Uniform07.xi_pos row) (source_xi_lt_one row) Λ (Early.demandRatio row) U c α (C d) i q
    · simp only [norm_zero]
      positivity
  change (∫d, f d ∂ν) = ∫d, g d ∂ν
  apply integral_eq_of_finite_cond ν T hT f g hfi hgi
  intro k hk
  have hfiber : T ⁻¹' {k} = Hybrid.categoryFiber (sourceDrawTag zs U) k := by
    ext d
    simp only [mem_preimage,mem_singleton_iff,T,funext_iff,Hybrid.categoryFiber,mem_univ_pi]
  rw [hfiber] at hk ⊢
  have hmass : ∀u, μ (sourceDrawTag zs U ⁻¹' {k u}) ≠ 0 := by
    rw [Hybrid.categoryFiber_mass] at hk
    exact fun u => (Finset.prod_ne_zero_iff.mp hk) u (Finset.mem_univ u)
  have hcell := Hybrid.measurableSet_categoryFiber (sourceDrawTag zs U) (measurable_sourceDrawTag zs U) k
  have hcat : ∀ᵐd ∂cond ν (Hybrid.categoryFiber (sourceDrawTag zs U) k),
      ∀u, sourceDrawTag zs U (d u) = k u := by
    filter_upwards [cond_ae_mem ν hcell] with d hd
    exact fun u => hd u (mem_univ u)
  by_cases hs : Nonempty {u : RivalIndex i // k u = 0}
  · letI := hs
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Fintype.card_pos (α := {u : RivalIndex i // k u = 0})))
    let e : Fin (n+1) ≃ {u : RivalIndex i // k u = 0} := (Fintype.equivFinOfCardEq hn).symm
    have hseed : ∀ᵐd ∂cond ν (Hybrid.categoryFiber (sourceDrawTag zs U) k), rivalHasSeed zs i d := by
      filter_upwards [hcat] with d hd
      let u : {u : RivalIndex i // k u = 0} := Classical.choice hs
      exact ⟨u,(sourceDrawTag_eq_zero_iff zs U (d u)).mp ((hd u).trans u.property)⟩
    calc
      _ = ∫d, PathCorr (C d) i q ∂cond ν (Hybrid.categoryFiber (sourceDrawTag zs U) k) :=
        conditional_source_correction_integral row μ i hΛ hR hguard hUR hzG hm hε c
          A hA τ j q hroute hgeneric k hmass n e hnoatoms
      _ = _ := integral_congr_ae (hseed.mono (fun d hd => (if_pos hd).symm))
  · have hnonseed : ∀ᵐd ∂cond ν (Hybrid.categoryFiber (sourceDrawTag zs U) k),
        ∀u, zs < (d u).1.2.bid := by
      filter_upwards [hcat] with d hd
      intro u
      by_contra hn
      have hu := (sourceDrawTag_eq_zero_iff zs U (d u)).mpr (le_of_not_gt hn)
      exact hs ⟨⟨u,(hd u).symm.trans hu⟩⟩
    apply integral_congr_ae
    filter_upwards [hnonseed] with d hd
    have hnone := focal_seed_none_of_all_nonseed (U := U) i
      ((source_seed_cutoff_lt_bidCap row).trans hUR) μB A hA τ j d hd
    have hns : ¬rivalHasSeed zs i d := by rintro ⟨u,hu⟩; exact not_le.mpr (hd u) hu
    dsimp only [f,g,Corr]
    rw [hnone,sourceCountCorrection_none,if_neg hns]

end FCAppendix.Affine.Uniform07Finishing
