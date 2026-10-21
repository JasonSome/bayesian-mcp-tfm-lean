import FCAppendix.Affine.Uniform07Finishing.Native.SourceSeedErasure
import FCAppendix.Affine.Uniform07Finishing.Native.WeightedTargetProbability

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Bayes Game Set Classical
open FCAppendix.Affine StrictNative ConditionalSuccess
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]
set_option maxHeartbeats 600000

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def sourceContextDeficit (c : ℕ) (X : ClassifiedContext m) : ℝ :=
  (max (Weighted.budget c 0 X) (Weighted.budget c 1 X)-Weighted.commonBudget c X : ℕ)

omit [Nonempty (Fin m)] in
lemma measurable_sourceContextDeficit (c : ℕ) : Measurable (sourceContextDeficit (m := m) c) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (((Weighted.measurable_budget c 0).max (Weighted.measurable_budget c 1)).sub
      ((Weighted.measurable_budget c 0).min (Weighted.measurable_budget c 1)))

omit [Nonempty (Fin m)] in
lemma sourceContextDeficit_bounds (c : ℕ) (X : ClassifiedContext m) :
    sourceContextDeficit c X ∈ Icc (0 : ℝ) m := by
  have hb (j : Fin 2) : Weighted.budget c j X ≤ m :=
    (min_le_right _ _).trans (by simpa using Finset.card_le_univ (Weighted.presentSet X.1))
  constructor
  · exact Nat.cast_nonneg _
  · change ((max (Weighted.budget c 0 X) (Weighted.budget c 1 X) -
      Weighted.commonBudget c X : ℕ) : ℝ) ≤ (m : ℝ)
    exact_mod_cast (Nat.sub_le (max (Weighted.budget c 0 X) (Weighted.budget c 1 X))
      (Weighted.commonBudget c X)).trans (max_le (hb 0) (hb 1))

omit [Nonempty (Fin m)] in
lemma integrable_sourceContextDeficit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (c : ℕ)
    (C : X → ClassifiedContext m) (hC : Measurable C) :
    Integrable (fun x => sourceContextDeficit c (C x)) μ := by
  apply (integrable_const (m : ℝ)).mono'
    ((measurable_sourceContextDeficit c).comp hC).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (sourceContextDeficit_bounds c (C x)).1]
    using (sourceContextDeficit_bounds c (C x)).2

omit [Nonempty (Fin m)] in
lemma seedEquivalent_sourceContextDeficit {zs : ℝ} {X Y : ClassifiedContext m}
    (h : Weighted.SeedEquivalentContext zs X Y) (c : ℕ) :
    sourceContextDeficit c X = sourceContextDeficit c Y := by
  simp only [sourceContextDeficit,Weighted.seedEquivalent_budget h,
    Weighted.seedEquivalent_commonBudget h]

omit [Nonempty (Fin m)] in
lemma planTargetIndicator_bounds (i : Fin m) (P : Option (Finset (Fin m))) :
    Weighted.planTargetIndicator i P ∈ Icc (0 : ℝ) 1 := by
  cases P with
  | none => norm_num [Weighted.planTargetIndicator]
  | some E => by_cases hi : i ∈ E <;>
      simp [Weighted.planTargetIndicator,FCAppendix.Affine.WeightedSampling.indicator,hi]

omit [Nonempty (Fin m)] in
lemma integrable_planTargetIndicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (i : Fin m)
    (P : X → Option (Finset (Fin m))) (hP : Measurable P) :
    Integrable (fun x => Weighted.planTargetIndicator i (P x)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_of_countable (Weighted.planTargetIndicator i)).comp hP).aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (planTargetIndicator_bounds i (P x)).1]
    using (planTargetIndicator_bounds i (P x)).2

theorem conditional_source_target_integral_le
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] (i : Fin m)
    {zs ξ Λ a r U d₀ z t width ε R : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hξ : 0 < ξ) (ha : 0 < a)
    (hlo : 0 < Λ-a) (hd₀ : 0 < d₀)
    (hz0 : 0 ≤ zs) (hzR : zs < R) (hr : 0 < r)
    (hzΛ : zs ≤ Λ-a) (hzz : zs ≤ z) (hzU : zs ≤ U) (c : ℕ)
    (A : JointAction 2) (hA : zs < A.bid) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hroute : ∀ᵐ u ∂μ, u.1.2.bid ≤ zs → u.1.2.routeCount = 2)
    (k : RivalIndex i → Fin 3)
    (hmass : ∀ u, μ (sourceDrawTag zs U ⁻¹' {k u}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {u : RivalIndex i // k u = 0})
    (hnoatoms : ∀ b : ℝ,
      ((cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0) :
    let ν := cond (Measure.pi (fun _ : RivalIndex i => μ))
      (Hybrid.categoryFiber (sourceDrawTag zs U) k)
    let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
    (∫ d, Weighted.planTargetIndicator i
      (Weighted.sourcePlan ξ Λ r U zs c μB
        (Weighted.sourceGuardAlpha ξ Λ a r U d₀ z t width ε c)
        (observedContext R j (focalLocalList i A τ j d))) ∂ν) ≤
      (∫ d, sourceContextDeficit c (observedContext R j (focalLocalList i A τ j d)) ∂ν)/(ε*m) := by
  let ν := cond (Measure.pi (fun _ : RivalIndex i => μ))
    (Hybrid.categoryFiber (sourceDrawTag zs U) k)
  have hνmass : (Measure.pi (fun _ : RivalIndex i => μ))
      (Hybrid.categoryFiber (sourceDrawTag zs U) k) ≠ 0 := by
    rw [Hybrid.categoryFiber_mass]
    exact Finset.prod_ne_zero_iff.mpr (fun u _ => hmass u)
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hνmass
  letI (u : {u : RivalIndex i // k u ≠ 0}) :
      IsProbabilityMeasure (cond μ (sourceDrawTag zs U ⁻¹' {k u})) :=
    cond_isProbabilityMeasure (hmass u)
  let rest := Measure.pi (fun u : {u : RivalIndex i // k u ≠ 0} =>
    cond μ (sourceDrawTag zs U ⁻¹' {k u}))
  let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
  let C := fun d : RivalIndex i → UserDraw 2 => observedContext R j (focalLocalList i A τ j d)
  let Ce := erasedFocalContext R i A τ j k
  let α := Weighted.sourceGuardAlpha (m := m) ξ Λ a r U d₀ z t width ε c
  let drop := fun d : RivalIndex i → UserDraw 2 =>
    fun u : {u : RivalIndex i // k u ≠ 0} => d u
  have hC : Measurable C := (measurable_observedContext R j).comp (measurable_focalLocalList i A τ j)
  have hCe : Measurable Ce := measurable_erasedFocalContext R i A τ j k
  have hdrop : Measurable drop := measurable_pi_lambda _ (fun u => measurable_pi_apply u.val)
  have hα : Measurable α := Weighted.measurable_sourceGuardAlpha hξ ha hlo hd₀ r U z t width ε c
  have hΛ : 0 < Λ := by linarith
  have hplan : Measurable (fun q : Option unitInterval ×
      ({u : RivalIndex i // k u ≠ 0} → UserDraw 2) =>
      Weighted.sourcePlanFromSeed ξ Λ r U c α (Ce q.2) q.1) := by
    have hpair : Measurable (fun q : Option unitInterval ×
        ({u : RivalIndex i // k u ≠ 0} → UserDraw 2) => (Ce q.2,q.1)) :=
      (hCe.comp measurable_snd).prodMk measurable_fst
    simpa only [Function.comp_def] using
      (Weighted.measurable_sourcePlanFromSeed ξ Λ r U hξ hΛ c α hα).comp hpair
  let F := fun q : Option unitInterval × ({u : RivalIndex i // k u ≠ 0} → UserDraw 2) =>
    Weighted.planTargetIndicator i (Weighted.sourcePlanFromSeed ξ Λ r U c α (Ce q.2) q.1)
  have hF : Measurable F := (measurable_of_countable (Weighted.planTargetIndicator i)).comp hplan
  have hFs : Measurable (fun q : unitInterval × ({u : RivalIndex i // k u ≠ 0} → UserDraw 2) =>
      F (some q.1,q.2)) := hF.comp (measurable_some.prodMap measurable_id)
  have hFi : Integrable (fun q : unitInterval × ({u : RivalIndex i // k u ≠ 0} → UserDraw 2) =>
      F (some q.1,q.2)) ((volume : Measure unitInterval).prod rest) :=
    integrable_planTargetIndicator _ i _ (hplan.comp (measurable_some.prodMap measurable_id))
  have hfull : ∀ᵐ d ∂Measure.pi (fun _ : RivalIndex i => μ),
      ∀ u, (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2 :=
    ae_all_iff.mpr (fun u =>
      (measurePreserving_eval (fun _ : RivalIndex i => μ) u).quasiMeasurePreserving.ae hroute)
  have hcell := Hybrid.measurableSet_categoryFiber (sourceDrawTag zs U)
    (measurable_sourceDrawTag zs U) k
  have hc : ∀ᵐ d ∂ν, ∀ u, sourceDrawTag zs U (d u) = k u := by
    filter_upwards [cond_ae_mem (Measure.pi (fun _ : RivalIndex i => μ)) hcell] with d hd
    exact fun u => hd u (mem_univ u)
  have hroutes : ∀ᵐ d ∂ν, ∀ u, (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2 :=
    cond_ae_of_ae (Measure.pi (fun _ : RivalIndex i => μ)) hcell hfull
  have hseed : Measurable (fun d => Weighted.sourceSeed μB zs (C d)) :=
    (Weighted.measurable_sourceSeed μB zs).comp hC
  have hjoint := forced_focal_seed_joint_profile μ i hzR A hA τ j hroute k hmass n e hnoatoms
  letI : IsProbabilityMeasure ((volume : Measure unitInterval).map (some : unitInterval → Option unitInterval)) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hdropLaw : ν.map drop = rest := by
    have hh := congrArg (fun M => M.map Prod.snd) hjoint
    rw [Measure.map_map measurable_snd (hseed.prodMk hdrop),
      (measurePreserving_snd (μ := (volume : Measure unitInterval).map some) (ν := rest)).map_eq] at hh
    exact hh
  have hΔeq : (fun d => sourceContextDeficit c (Ce (drop d))) =ᵐ[ν]
      (fun d => sourceContextDeficit c (C d)) := by
    filter_upwards [hc,hroutes] with d hdc hdr
    exact (seedEquivalent_sourceContextDeficit
      (erasedFocalContext_seed_equivalent i hz0 hzR A τ j d k hdc hdr) c).symm
  change (∫ d, Weighted.planTargetIndicator i (Weighted.sourcePlan ξ Λ r U zs c μB α (C d)) ∂ν) ≤
    (∫ d, sourceContextDeficit c (C d) ∂ν)/(ε*m)
  calc
    _ = ∫ d, F (Weighted.sourceSeed μB zs (C d),drop d) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hc,hroutes] with d hdc hdr
      exact congrArg (Weighted.planTargetIndicator i)
        (sourcePlan_erased_focal_factorization i hz0 hzR hr ha.le hzΛ hzz hzU c μB
          A τ j d k hdc hdr)
    _ = ∫ q, F q ∂((volume : Measure unitInterval).map some).prod rest := by
      rw [←hjoint]
      exact (integral_map (hseed.prodMk hdrop).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ q : unitInterval × ({u : RivalIndex i // k u ≠ 0} → UserDraw 2),
        F (some q.1,q.2) ∂(volume : Measure unitInterval).prod rest := by
      have hprod : ((volume : Measure unitInterval).map some).prod rest =
          ((volume : Measure unitInterval).prod rest).map (Prod.map some id) := by
        simpa only [Measure.map_id] using
          Measure.map_prod_map (volume : Measure unitInterval) rest measurable_some measurable_id
      rw [hprod,integral_map (measurable_some.prodMap measurable_id).aemeasurable
        hF.aestronglyMeasurable]
      rfl
    _ = ∫ d, ∫ s : unitInterval, F (some s,d) ∂volume ∂rest := integral_prod_symm _ hFi
    _ ≤ ∫ d, sourceContextDeficit c (Ce d)/(ε*m) ∂rest := by
      apply integral_mono_ae hFi.integral_prod_right
        ((integrable_sourceContextDeficit rest c Ce hCe).div_const _)
      filter_upwards [] with d
      exact Weighted.sourcePlanFromSeed_target_integral_le c hm hε (Ce d) i
    _ = (∫ d, sourceContextDeficit c (Ce d) ∂rest)/(ε*m) := integral_div _ _
    _ = (∫ d, sourceContextDeficit c (C d) ∂ν)/(ε*m) := by
      congr 1
      have hi : Measurable (fun d : {u : RivalIndex i // k u ≠ 0} → UserDraw 2 =>
          sourceContextDeficit c (Ce d)) := by
        simpa only [Function.comp_def] using (measurable_sourceContextDeficit c).comp hCe
      rw [←hdropLaw,integral_map hdrop.aemeasurable hi.aestronglyMeasurable]
      exact integral_congr_ae hΔeq

lemma integral_le_of_finite_cond {X K : Type*} [MeasurableSpace X]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → K) (hT : Measurable T)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hcell : ∀ k, μ (T ⁻¹' {k}) ≠ 0 →
      (∫ x, f x ∂cond μ (T ⁻¹' {k})) ≤ ∫ x, g x ∂cond μ (T ⁻¹' {k})) :
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  have hS (k : K) : MeasurableSet (T ⁻¹' {k}) := hT (measurableSet_singleton k)
  have hsum (q : X → ℝ) (hq : Integrable q μ) :
      (∫ x, q x ∂μ) = ∑ k, ∫ x, (T ⁻¹' {k}).indicator q x ∂μ := by
    calc
      _ = ∫ x, ∑ k, (T ⁻¹' {k}).indicator q x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [Set.indicator,eq_comm]
      _ = _ := integral_finsetSum _ (fun k _ => hq.indicator (hS k))
  rw [hsum f hf,hsum g hg]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : μ (T ⁻¹' {k}) = 0
  · have hz : μ.restrict (T ⁻¹' {k}) = 0 := by
      apply Measure.ext
      intro S hS'
      rw [Measure.restrict_apply hS']
      exact le_antisymm ((measure_mono inter_subset_right).trans_eq hk) bot_le
    simp only [integral_indicator (hS k),hz,integral_zero_measure,le_refl]
  · have hid (q : X → ℝ) :
        (∫ x, (T ⁻¹' {k}).indicator q x ∂μ) =
          μ.real (T ⁻¹' {k})*(∫ x, q x ∂cond μ (T ⁻¹' {k})) := by
      rw [integral_indicator (hS k),ProbabilityTheory.cond,integral_smul_measure,
        ENNReal.toReal_inv,smul_eq_mul]
      change (∫ x in T ⁻¹' {k}, q x ∂μ) =
        (μ (T ⁻¹' {k})).toReal*((μ (T ⁻¹' {k})).toReal⁻¹*
          (∫ x in T ⁻¹' {k}, q x ∂μ))
      rw [mul_inv_cancel_left₀ (ENNReal.toReal_ne_zero.mpr ⟨hk,measure_ne_top _ _⟩)]
    rw [hid f,hid g]
    exact mul_le_mul_of_nonneg_left (hcell k hk) ENNReal.toReal_nonneg

omit [Nonempty (Fin m)] in

lemma focal_seed_none_of_all_nonseed (i : Fin m) {zs U R : ℝ} (hzR : zs < R)
    (μB : Measure ℝ) (A : JointAction 2) (hA : zs < A.bid)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (d : RivalIndex i → UserDraw 2)
    (hd : ∀ u, zs < (d u).1.2.bid) :
    Weighted.sourceSeed μB zs (observedContext R j (focalLocalList i A τ j d)) = none := by
  rw [sourceSeed_observed (U := U) hzR]
  unfold Hybrid.observedLowSeed
  apply (seedOnList_none_iff μB _).mpr
  intro u
  by_cases hui : u = i
  · subst u
    by_cases hj : j ∈ firstK τ A.routeCount <;> by_cases hb : A.bid ≤ U <;>
      simp [TaggedLocal.lowList,TaggedLocal.tag,focalLocalList,observe,drawsRealization,
        insertFocalProfile,hj,hb,not_le.mpr hA]
  · by_cases hj : j ∈ firstK (d ⟨u,hui⟩).2 (d ⟨u,hui⟩).1.2.routeCount <;>
      by_cases hb : (d ⟨u,hui⟩).1.2.bid ≤ U <;>
      simp [TaggedLocal.lowList,TaggedLocal.tag,focalLocalList,observe,drawsRealization,
        insertFocalProfile,hui,hj,hb,not_le.mpr (hd ⟨u,hui⟩)]

theorem source_target_integral_le
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] (i : Fin m)
    {zs ξ Λ a r U d₀ z t width ε R : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hξ : 0 < ξ) (ha : 0 < a)
    (hlo : 0 < Λ-a) (hd₀ : 0 < d₀)
    (hz0 : 0 ≤ zs) (hzR : zs < R) (hr : 0 < r)
    (hzΛ : zs ≤ Λ-a) (hzz : zs ≤ z) (hzU : zs ≤ U) (c : ℕ)
    (A : JointAction 2) (hA : zs < A.bid) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hroute : ∀ᵐ u ∂μ, u.1.2.bid ≤ zs → u.1.2.routeCount = 2)
    (hnoatoms : ∀ b : ℝ,
      ((cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0) :
    let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
    (∫ d, Weighted.planTargetIndicator i
      (Weighted.sourcePlan ξ Λ r U zs c μB
        (Weighted.sourceGuardAlpha ξ Λ a r U d₀ z t width ε c)
        (observedContext R j (focalLocalList i A τ j d)))
        ∂Measure.pi (fun _ : RivalIndex i => μ)) ≤
      (∫ d, sourceContextDeficit c (observedContext R j (focalLocalList i A τ j d))
        ∂Measure.pi (fun _ : RivalIndex i => μ))/(ε*m) := by
  let ν := Measure.pi (fun _ : RivalIndex i => μ)
  let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
  let C := fun d : RivalIndex i → UserDraw 2 => observedContext R j (focalLocalList i A τ j d)
  let α := Weighted.sourceGuardAlpha (m := m) ξ Λ a r U d₀ z t width ε c
  let P := fun d : RivalIndex i → UserDraw 2 => Weighted.sourcePlan ξ Λ r U zs c μB α (C d)
  let T := fun d : RivalIndex i → UserDraw 2 => fun u => sourceDrawTag zs U (d u)
  have hT : Measurable T := measurable_pi_lambda _ (fun u =>
    (measurable_sourceDrawTag zs U).comp (measurable_pi_apply u))
  have hC : Measurable C := (measurable_observedContext R j).comp (measurable_focalLocalList i A τ j)
  have hα : Measurable α := Weighted.measurable_sourceGuardAlpha hξ ha hlo hd₀ r U z t width ε c
  have hΛ : 0 < Λ := by linarith
  have hP : Measurable P :=
    (Weighted.measurable_sourcePlan ξ Λ r U zs hξ hΛ c μB α hα).comp hC
  change (∫ d, Weighted.planTargetIndicator i (P d) ∂ν) ≤
    (∫ d, sourceContextDeficit c (C d) ∂ν)/(ε*m)
  rw [←integral_div]
  apply integral_le_of_finite_cond ν T hT _ _
    (integrable_planTargetIndicator ν i P hP)
    ((integrable_sourceContextDeficit ν c C hC).div_const _)
  intro k hk
  have hfiber : T ⁻¹' {k} = Hybrid.categoryFiber (sourceDrawTag zs U) k := by
    ext d
    simp only [Set.mem_preimage,Set.mem_singleton_iff,T,funext_iff,
      Hybrid.categoryFiber,Set.mem_univ_pi]
  rw [hfiber] at hk ⊢
  have hmass : ∀ u, μ (sourceDrawTag zs U ⁻¹' {k u}) ≠ 0 := by
    change (Measure.pi (fun _ : RivalIndex i => μ))
      (Hybrid.categoryFiber (sourceDrawTag zs U) k) ≠ 0 at hk
    rw [Hybrid.categoryFiber_mass] at hk
    exact fun u => (Finset.prod_ne_zero_iff.mp hk) u (Finset.mem_univ u)
  by_cases hseed : Nonempty {u : RivalIndex i // k u = 0}
  · letI := hseed
    have hcard : 0 < Fintype.card {u : RivalIndex i // k u = 0} := Fintype.card_pos
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard)
    let e : Fin (n+1) ≃ {u : RivalIndex i // k u = 0} :=
      (Fintype.equivFinOfCardEq hn).symm
    rw [integral_div]
    exact conditional_source_target_integral_le μ i hm hε hξ ha hlo hd₀
      hz0 hzR hr hzΛ hzz hzU c A hA τ j hroute k hmass n e hnoatoms
  · have hn : ∀ u, k u ≠ 0 := fun u hu => hseed ⟨⟨u,hu⟩⟩
    have hcell := Hybrid.measurableSet_categoryFiber (sourceDrawTag zs U)
      (measurable_sourceDrawTag zs U) k
    have hzero : (fun d => Weighted.planTargetIndicator i (P d)) =ᵐ[
        cond ν (Hybrid.categoryFiber (sourceDrawTag zs U) k)] (fun _ => 0) := by
      filter_upwards [cond_ae_mem ν hcell] with d hd
      have hb : ∀ u, zs < (d u).1.2.bid := by
        intro u
        by_contra hnot
        have hu : sourceDrawTag zs U (d u) = 0 :=
          (sourceDrawTag_eq_zero_iff zs U (d u)).mpr (le_of_not_gt hnot)
        exact hn u ((hd u (mem_univ u)).symm.trans hu)
      have hs := focal_seed_none_of_all_nonseed (U := U) i hzR μB A hA τ j d hb
      simp only [P,Weighted.sourcePlan_seedless ξ Λ r U zs c μB α (C d) hs,
        Weighted.planTargetIndicator]
    rw [integral_congr_ae hzero,integral_zero]
    exact integral_nonneg (fun d => div_nonneg (sourceContextDeficit_bounds c (C d)).1
      (mul_nonneg hε.le (Nat.cast_nonneg m)))

theorem source_target_integral_full_le
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] (i : Fin m)
    {zs ξ Λ a r U d₀ z t width ε R : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hξ : 0 < ξ) (ha : 0 < a)
    (hlo : 0 < Λ-a) (hd₀ : 0 < d₀)
    (hz0 : 0 ≤ zs) (hzR : zs < R) (hr : 0 < r)
    (hzΛ : zs ≤ Λ-a) (hzz : zs ≤ z) (hzU : zs ≤ U) (c : ℕ)
    (A : JointAction 2) (hA : zs < A.bid) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hroute : ∀ᵐ u ∂μ, u.1.2.bid ≤ zs → u.1.2.routeCount = 2)
    (hnoatoms : ∀ b : ℝ,
      ((cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0) :
    let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
    (∫ d, Weighted.planTargetIndicator i
      (Weighted.sourcePlan ξ Λ r U zs c μB
        (Weighted.sourceGuardAlpha ξ Λ a r U d₀ z t width ε c)
        (observedContext R j (deviationList i A d τ j)))
        ∂Measure.pi (fun _ : Fin m => μ)) ≤
      (∫ d, sourceContextDeficit c (observedContext R j (deviationList i A d τ j))
        ∂Measure.pi (fun _ : Fin m => μ))/(ε*m) := by
  let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
  let α := Weighted.sourceGuardAlpha (m := m) ξ Λ a r U d₀ z t width ε c
  have hC := (measurable_observedContext R j).comp (measurable_focalLocalList i A τ j)
  have hΛ : 0 < Λ := by linarith
  have hα : Measurable α := Weighted.measurable_sourceGuardAlpha hξ ha hlo hd₀ r U z t width ε c
  have hp : Measurable (fun d : RivalIndex i → UserDraw 2 =>
      Weighted.planTargetIndicator i (Weighted.sourcePlan ξ Λ r U zs c μB α
        (observedContext R j (focalLocalList i A τ j d)))) := by
    simpa only [Function.comp_def] using (measurable_of_countable (Weighted.planTargetIndicator i)).comp
      ((Weighted.measurable_sourcePlan ξ Λ r U zs hξ hΛ c μB α hα).comp hC)
  have hΔ : Measurable (fun d : RivalIndex i → UserDraw 2 =>
      sourceContextDeficit c (observedContext R j (focalLocalList i A τ j d))) := by
    simpa only [Function.comp_def] using (measurable_sourceContextDeficit c).comp hC
  have hh := source_target_integral_le (t := t) (width := width) μ i hm hε hξ ha hlo hd₀ hz0 hzR hr hzΛ hzz hzU
    c A hA τ j hroute hnoatoms
  dsimp only at hh
  rw [←(deleteFocal_preserves_iid i μ).map_eq,
    integral_map (measurable_deleteFocal i).aemeasurable hp.aestronglyMeasurable,
    integral_map (measurable_deleteFocal i).aemeasurable hΔ.aestronglyMeasurable] at hh
  simpa only [deviationList_eq_focalLocalList] using hh

end FCAppendix.Affine.Uniform07Finishing
