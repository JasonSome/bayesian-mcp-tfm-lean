import FCAppendix.Affine.Uniform07Finishing.Native.NativeSeedBounds
import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessCap

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine StrictNative ConditionalSuccess

abbrev RivalIndex {m : ℕ} (i : Fin m) := {u : Fin m // u ≠ i}

def deleteFocal {m : ℕ} (i : Fin m) (d : UserProfile m 2) : RivalIndex i → UserDraw 2 :=
  fun u => d u

lemma measurable_deleteFocal {m : ℕ} (i : Fin m) : Measurable (deleteFocal i) :=
  measurable_pi_lambda _ (fun u => measurable_pi_apply u.val)

theorem deleteFocal_preserves_iid {m : ℕ} (i : Fin m)
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] :
    MeasurePreserving (deleteFocal i) (Measure.pi (fun _ : Fin m => μ))
      (Measure.pi (fun _ : RivalIndex i => μ)) := by
  convert! (measurePreserving_snd.comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin m => μ) (fun u => u = i))) using 1

def insertFocalProfile {m : ℕ} (i : Fin m) (v : ℝ) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (d : RivalIndex i → UserDraw 2) : UserProfile m 2 :=
  fun u => if hu : u = i then ((v,a),τ) else d ⟨u,hu⟩

lemma measurable_insertFocalProfile {m : ℕ} (i : Fin m) (v : ℝ) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) : Measurable (insertFocalProfile i v a τ) := by
  apply measurable_pi_lambda
  intro u
  by_cases hu : u = i
  · simpa only [insertFocalProfile, dif_pos hu] using
      (measurable_const : Measurable (fun _ : RivalIndex i → UserDraw 2 => ((v,a),τ)))
  · simpa only [insertFocalProfile, dif_neg hu] using
      (measurable_pi_apply (⟨u,hu⟩ : RivalIndex i))

def focalLocalList {m : ℕ} (i : Fin m) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (d : RivalIndex i → UserDraw 2) : LocalList m :=
  observe (drawsRealization (insertFocalProfile i 0 a τ d)) j

lemma measurable_focalLocalList {m : ℕ} (i : Fin m) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) : Measurable (focalLocalList i a τ j) :=
  (measurable_observe_draws j).comp (measurable_insertFocalProfile i 0 a τ)

lemma deviationList_eq_focalLocalList {m : ℕ} (i : Fin m) (a : JointAction 2)
    (d : UserProfile m 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    deviationList i a d τ j = focalLocalList i a τ j (deleteFocal i d) := by
  funext u
  by_cases hu : u = i
  · subst u
    simp [deviationList, focalLocalList, observe, deviate, drawsRealization,
      insertFocalProfile, card_firstK _ _ a.routeCount_le]
  · simp [deviationList, focalLocalList, observe, deviate, drawsRealization,
      insertFocalProfile, deleteFocal, hu]

def focalSeedIndex {m : ℕ} (i : Fin m) (k : RivalIndex i → Fin 3) (u : Fin m) : Prop :=
  ∃ hu : u ≠ i, k ⟨u,hu⟩ = 0

def focalSeedIndexEquiv {m : ℕ} (i : Fin m) (k : RivalIndex i → Fin 3) :
    {u : RivalIndex i // k u = 0} ≃ {u : Fin m // focalSeedIndex i k u} where
  toFun u := ⟨u.val.val, u.val.property, u.property⟩
  invFun u := ⟨⟨u.val,u.property.choose⟩,u.property.choose_spec⟩
  left_inv u := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv u := by apply Subtype.ext; rfl

theorem forced_focal_seed_enumeration {m n : ℕ} (i : Fin m)
    {zs U R : ℝ} (hzR : zs < R) (μB : Measure ℝ)
    (a : JointAction 2) (ha : zs < a.bid) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (d : RivalIndex i → UserDraw 2) (k : RivalIndex i → Fin 3)
    (hcat : ∀ u, sourceDrawTag zs U (d u) = k u)
    (hroute : ∀ u, (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2)
    (e : Fin (n+1) ≃ {u : RivalIndex i // k u = 0}) :
    Weighted.sourceSeed μB zs (observedContext R j (focalLocalList i a τ j d)) =
      some (Hybrid.conditionalMinimumSeed μB n (fun l => (d (e l)).1.2.bid)) := by
  rw [sourceSeed_observed (U := U) hzR]
  unfold Hybrid.observedLowSeed
  let b : Fin m → ℝ := fun u => (insertFocalProfile i 0 a τ d u).1.2.bid
  have hL : ∀ u, TaggedLocal.lowList zs U (focalLocalList i a τ j d) u =
      if focalSeedIndex i k u then some (b u) else none := by
    intro u
    by_cases hu : u = i
    · subst u
      have hi : ¬focalSeedIndex i k i := by rintro ⟨hn,_⟩; exact hn rfl
      by_cases hj : j ∈ firstK τ a.routeCount <;> by_cases hbU : a.bid ≤ U <;>
        simp [TaggedLocal.lowList, TaggedLocal.tag, focalLocalList, observe,
          drawsRealization, insertFocalProfile, hi, hj, not_le.mpr ha, hbU]
    · let r : RivalIndex i := ⟨u,hu⟩
      have hp : focalSeedIndex i k u ↔ k r = 0 := by
        constructor
        · rintro ⟨hn,hk⟩
          simpa only [r] using hk
        · intro hk
          exact ⟨hu,hk⟩
      by_cases hs : (d r).1.2.bid ≤ zs
      · have hk : k r = 0 := by rw [←hcat r]; simp [sourceDrawTag,hs]
        have hr := hroute r hs
        simp [TaggedLocal.lowList, TaggedLocal.tag, focalLocalList, observe,
          drawsRealization, insertFocalProfile, b, hu, hp, hk, hr, firstK_full_two, r, hs]
      · have hk : k r ≠ 0 := by
          rw [←hcat r]
          by_cases hb : (d r).1.2.bid ≤ U <;> simp [sourceDrawTag,hs,hb]
        by_cases hj : j ∈ firstK (d r).2 (d r).1.2.routeCount <;>
          by_cases hbU : (d r).1.2.bid ≤ U <;>
          simp [TaggedLocal.lowList, TaggedLocal.tag, focalLocalList, observe,
            drawsRealization, insertFocalProfile, hu, hp, hk, hj, r, hs, hbU]
  have hh := Hybrid.seedOnList_enumeration μB (focalSeedIndex i k)
    (e.trans (focalSeedIndexEquiv i k)) b
      (TaggedLocal.lowList zs U (focalLocalList i a τ j d)) hL
  convert hh using 1
  congr 2
  funext l
  simp [b, insertFocalProfile, focalSeedIndexEquiv, (e l).val.property]

theorem forced_focal_seed_joint {m : ℕ} {Y : Type*} [MeasurableSpace Y]
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ]
    (ω : Measure Y) [IsProbabilityMeasure ω] (i : Fin m)
    {zs U R : ℝ} (hzR : zs < R)
    (a : JointAction 2) (ha : zs < a.bid) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hroute : ∀ᵐ u ∂μ, u.1.2.bid ≤ zs → u.1.2.routeCount = 2)
    (k : RivalIndex i → Fin 3)
    (hmass : ∀ u, μ (sourceDrawTag zs U ⁻¹' {k u}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {u : RivalIndex i // k u = 0})
    (hnoatoms : ∀ b : ℝ,
      ((cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0) :
    ((cond (Measure.pi (fun _ : RivalIndex i => μ))
      (Hybrid.categoryFiber (sourceDrawTag zs U) k)).prod ω).map
      (fun x =>
        (Weighted.sourceSeed
          ((cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid))
          zs (observedContext R j (focalLocalList i a τ j x.1)),
          ((fun u : {u : RivalIndex i // k u ≠ 0} => x.1 u),x.2))) =
      ((volume : Measure unitInterval).map some).prod
        ((Measure.pi (fun u : {u : RivalIndex i // k u ≠ 0} =>
          cond μ (sourceDrawTag zs U ⁻¹' {k u}))).prod ω) := by
  let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map
    (fun u : UserDraw 2 => u.1.2.bid)
  let ν := cond (Measure.pi (fun _ : RivalIndex i => μ))
    (Hybrid.categoryFiber (sourceDrawTag zs U) k)
  have hνmass : (Measure.pi (fun _ : RivalIndex i => μ))
      (Hybrid.categoryFiber (sourceDrawTag zs U) k) ≠ 0 := by
    rw [Hybrid.categoryFiber_mass]
    exact Finset.prod_ne_zero_iff.mpr (fun u _ => hmass u)
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hνmass
  let rest := (Measure.pi (fun u : {u : RivalIndex i // k u ≠ 0} =>
    cond μ (sourceDrawTag zs U ⁻¹' {k u}))).prod ω
  have hfull : ∀ᵐ d ∂Measure.pi (fun _ : RivalIndex i => μ),
      ∀ u, (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2 :=
    ae_all_iff.mpr (fun u =>
      (measurePreserving_eval (fun _ : RivalIndex i => μ) u).quasiMeasurePreserving.ae hroute)
  have hA := Hybrid.measurableSet_categoryFiber (sourceDrawTag zs U)
    (measurable_sourceDrawTag zs U) k
  have hc : ∀ᵐ d ∂ν, ∀ u, sourceDrawTag zs U (d u) = k u := by
    filter_upwards [cond_ae_mem (Measure.pi (fun _ : RivalIndex i => μ)) hA] with d hd
    intro u
    exact hd u (mem_univ u)
  have hr : ∀ᵐ d ∂ν, ∀ u, (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2 :=
    cond_ae_of_ae (Measure.pi (fun _ : RivalIndex i => μ)) hA hfull
  let f : (RivalIndex i → UserDraw 2) × Y →
      unitInterval × (({u : RivalIndex i // k u ≠ 0} → UserDraw 2) × Y) :=
    fun x => (Hybrid.conditionalMinimumSeed μB n (fun l => (x.1 (e l)).1.2.bid),
      ((fun u => x.1 u),x.2))
  have hf : Measurable f :=
    ((Hybrid.measurable_conditionalMinimumSeed μB n).comp
      (measurable_pi_lambda _ (fun l => measurable_draw_bid.comp
        ((measurable_pi_apply ((e l).val)).comp measurable_fst)))).prodMk
      ((measurable_pi_lambda _ (fun u : {u : RivalIndex i // k u ≠ 0} =>
        (measurable_pi_apply u.val).comp measurable_fst)).prodMk measurable_snd)
  have hlaw := Hybrid.conditional_low_seed_joint μ (sourceDrawTag zs U)
    (measurable_sourceDrawTag zs U) k 0 hmass n e
    (fun u : UserDraw 2 => u.1.2.bid) measurable_draw_bid hnoatoms ω
  change (ν.prod ω).map _ = ((volume : Measure unitInterval).map some).prod rest
  calc
    _ = (ν.prod ω).map ((Prod.map some id) ∘ f) := by
      apply Measure.map_congr
      filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hc,
        measurePreserving_fst.quasiMeasurePreserving.ae hr] with x hx hxr
      apply Prod.ext
      · exact forced_focal_seed_enumeration i hzR μB a ha τ j x.1 k hx hxr e
      · rfl
    _ = ((ν.prod ω).map f).map (Prod.map some id) :=
      (Measure.map_map (measurable_some.prodMap measurable_id) hf).symm
    _ = ((volume : Measure unitInterval).prod rest).map (Prod.map some id) := by rw [hlaw]
    _ = _ := by rw [←Measure.map_prod_map _ _ measurable_some measurable_id,Measure.map_id]

theorem forced_focal_seed_joint_profile {m : ℕ}
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ] (i : Fin m)
    {zs U R : ℝ} (hzR : zs < R)
    (a : JointAction 2) (ha : zs < a.bid) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hroute : ∀ᵐ u ∂μ, u.1.2.bid ≤ zs → u.1.2.routeCount = 2)
    (k : RivalIndex i → Fin 3)
    (hmass : ∀ u, μ (sourceDrawTag zs U ⁻¹' {k u}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {u : RivalIndex i // k u = 0})
    (hnoatoms : ∀ b : ℝ,
      ((cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0) :
    (cond (Measure.pi (fun _ : RivalIndex i => μ))
      (Hybrid.categoryFiber (sourceDrawTag zs U) k)).map
      (fun d =>
        (Weighted.sourceSeed
          ((cond μ (sourceDrawTag zs U ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid))
          zs (observedContext R j (focalLocalList i a τ j d)),
          (fun u : {u : RivalIndex i // k u ≠ 0} => d u))) =
      ((volume : Measure unitInterval).map some).prod
        (Measure.pi (fun u : {u : RivalIndex i // k u ≠ 0} =>
          cond μ (sourceDrawTag zs U ⁻¹' {k u}))) := by
  let ν := cond (Measure.pi (fun _ : RivalIndex i => μ))
    (Hybrid.categoryFiber (sourceDrawTag zs U) k)
  let μB := (cond μ (sourceDrawTag zs U ⁻¹' {0})).map
    (fun u : UserDraw 2 => u.1.2.bid)
  let rest := Measure.pi (fun u : {u : RivalIndex i // k u ≠ 0} =>
    cond μ (sourceDrawTag zs U ⁻¹' {k u}))
  let ω : Measure PUnit.{1} := Measure.dirac PUnit.unit
  let f := fun d : RivalIndex i → UserDraw 2 =>
    Weighted.sourceSeed μB zs (observedContext R j (focalLocalList i a τ j d))
  let g := fun d : RivalIndex i → UserDraw 2 =>
    fun u : {u : RivalIndex i // k u ≠ 0} => d u
  have hf : Measurable f := (Weighted.measurable_sourceSeed μB zs).comp
    ((measurable_observedContext R j).comp (measurable_focalLocalList i a τ j))
  have hg : Measurable g := measurable_pi_lambda _ (fun u => measurable_pi_apply u.val)
  let forget := fun x : Option unitInterval ×
    (({u : RivalIndex i // k u ≠ 0} → UserDraw 2) × PUnit.{1}) => (x.1,x.2.1)
  have hforget : Measurable forget := measurable_fst.prodMk measurable_snd.fst
  have hfull := forced_focal_seed_joint μ ω i hzR a ha τ j hroute k hmass n e hnoatoms
  change ν.map (fun d => (f d,g d)) = ((volume : Measure unitInterval).map some).prod rest
  calc
    _ = (((ν.prod ω).map (fun x => (f x.1,(g x.1,x.2))))).map forget := by
      rw [Measure.map_map (f:=fun x : (RivalIndex i → UserDraw 2) × PUnit.{1} =>
        (f x.1,(g x.1,x.2))) hforget
        (show Measurable (fun x : (RivalIndex i → UserDraw 2) × PUnit.{1} =>
          (f x.1,(g x.1,x.2))) from
          (hf.comp measurable_fst).prodMk ((hg.comp measurable_fst).prodMk measurable_snd))]
      change ν.map (fun d => (f d,g d)) =
        (ν.prod ω).map ((fun d => (f d,g d)) ∘ Prod.fst)
      rw [←Measure.map_map (hf.prodMk hg) measurable_fst,
        (measurePreserving_fst (μ := ν) (ν := ω)).map_eq]
    _ = ((((volume : Measure unitInterval).map some).prod (rest.prod ω))).map forget := by rw [hfull]
    _ = _ := by
      change Measure.map (Prod.map id Prod.fst)
        (((volume : Measure unitInterval).map some).prod (rest.prod ω)) = _
      rw [←Measure.map_prod_map _ _ measurable_id measurable_fst,Measure.map_id,
        (measurePreserving_fst (μ := rest) (ν := ω)).map_eq]

def focalRivalsNoSeed {m : ℕ} (zs : ℝ) (i : Fin m) : Set (UserProfile m 2) :=
  {d | ∀ u, u ≠ i → zs < (d u).1.2.bid}

lemma card_rivalIndex {m : ℕ} (i : Fin m) : Fintype.card (RivalIndex i) = m-1 := by
  have he : Finset.univ.filter (fun u : Fin m => u ≠ i) = Finset.univ.erase i := by
    ext u
    simp [and_comm]
  simp only [RivalIndex,Fintype.card_subtype,he,Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ,Fintype.card_fin]

lemma measurableSet_focalRivalsNoSeed {m : ℕ} (zs : ℝ) (i : Fin m) :
    MeasurableSet (focalRivalsNoSeed zs i) := by
  have he : focalRivalsNoSeed zs i = deleteFocal i ⁻¹'
      (univ.pi (fun _ : RivalIndex i => (sourceSeedCategory zs)ᶜ)) := by
    ext d
    simp only [focalRivalsNoSeed,mem_setOf_eq,mem_preimage,mem_univ_pi,
      mem_compl_iff,sourceSeedCategory,not_le,deleteFocal]
    exact ⟨fun h u => h u u.property,fun h u hu => h ⟨u,hu⟩⟩
  rw [he]
  exact (measurable_deleteFocal i)
    (MeasurableSet.univ_pi (fun _ => (measurableSet_sourceSeedCategory zs).compl))

theorem focal_rivals_no_seed_real {m : ℕ} (μ : Measure (UserDraw 2))
    [IsProbabilityMeasure μ] (i : Fin m) (zs : ℝ) :
    (Measure.pi (fun _ : Fin m => μ)).real (focalRivalsNoSeed zs i) =
      (1-μ.real (sourceSeedCategory zs))^(m-1) := by
  let E : Set (RivalIndex i → UserDraw 2) :=
    univ.pi (fun _ => (sourceSeedCategory zs)ᶜ)
  have hE : MeasurableSet E :=
    MeasurableSet.univ_pi (fun _ => (measurableSet_sourceSeedCategory zs).compl)
  have he : focalRivalsNoSeed zs i = deleteFocal i ⁻¹' E := by
    ext d
    simp only [focalRivalsNoSeed,mem_setOf_eq,mem_preimage,E,mem_univ_pi,
      mem_compl_iff,sourceSeedCategory,not_le,deleteFocal]
    exact ⟨fun h u => h u u.property,fun h u hu => h ⟨u,hu⟩⟩
  rw [Measure.real,he,←Measure.map_apply (measurable_deleteFocal i) hE,
    (deleteFocal_preserves_iid i μ).map_eq]
  change ((Measure.pi (fun _ : RivalIndex i => μ))
    (univ.pi (fun _ : RivalIndex i => (sourceSeedCategory zs)ᶜ))).toReal = _
  rw [Measure.pi_pi]
  simp only [Finset.prod_const,Finset.card_univ,card_rivalIndex,ENNReal.toReal_pow]
  rw [←Measure.real,probReal_compl_eq_one_sub (measurableSet_sourceSeedCategory zs)]

theorem focal_rivals_no_seed_real_le_exp {m : ℕ} (μ : Measure (UserDraw 2))
    [IsProbabilityMeasure μ] (i : Fin m) (zs p : ℝ)
    (hp : p ≤ μ.real (sourceSeedCategory zs)) :
    (Measure.pi (fun _ : Fin m => μ)).real (focalRivalsNoSeed zs i) ≤
      Real.exp (-((m-1 : ℕ) : ℝ)*p) := by
  rw [focal_rivals_no_seed_real]
  have hq : μ.real (sourceSeedCategory zs) ≤ 1 := measureReal_le_one
  have hb : 1-μ.real (sourceSeedCategory zs) ≤ Real.exp (-p) := by
    linarith [Real.add_one_le_exp (-p)]
  have hh := pow_le_pow_left₀ (sub_nonneg.mpr hq) hb (m-1)
  rw [←Real.exp_nat_mul] at hh
  convert hh using 1
  congr 1
  ring

theorem deviation_seed_none_imp_rivals_no_seed {m : ℕ} (i : Fin m)
    {zs U R : ℝ} (hzR : zs < R) (μB : Measure ℝ)
    (a : JointAction 2) (d : UserProfile m 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (hroute : ∀ u, u ≠ i → (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2)
    (hnone : Weighted.sourceSeed μB zs
      (observedContext R j (deviationList i a d τ j)) = none) :
    d ∈ focalRivalsNoSeed zs i := by
  rw [sourceSeed_observed (U := U) hzR] at hnone
  have hempty := (seedOnList_none_iff μB
    (TaggedLocal.lowList zs U (deviationList i a d τ j))).mp hnone
  intro u hui
  by_contra hn
  have hb : (d u).1.2.bid ≤ zs := le_of_not_gt hn
  have hr := hroute u hui hb
  have hh := hempty u
  simp [TaggedLocal.lowList,TaggedLocal.tag,deviationList,observe,deviate,
    drawsRealization,hui,hr,firstK_full_two,hb] at hh

end FCAppendix.Affine.Uniform07Finishing
