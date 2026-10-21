import FCAppendix.Affine.Uniform07Finishing.Native.SourceCanonicalAveraging

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative Weighted
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def sourceCanonicalSelected (ξ Λ r U zs : ℝ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m) : Prop :=
  budget c 0 X=budget c 1 X ∨ sourcePlan ξ Λ r U zs c μseed α X≠none

theorem measurableSet_sourceCanonicalSelected (ξ Λ r U zs : ℝ)
    (hξ : 0<ξ) (hΛ : 0<Λ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (hα : Measurable α) :
    MeasurableSet {X | sourceCanonicalSelected ξ Λ r U zs c μseed α X} :=
  (measurableSet_eq_fun (measurable_budget c 0) (measurable_budget c 1)).union
    (measurableSet_eq_fun (measurable_sourcePlan ξ Λ r U zs hξ hΛ c μseed α hα)
      measurable_const).compl

def sourceCanonicalSampleTest {c : ℕ}
    (Γ : FiniteGame m 2 c unitInterval) (R ξ Λ r U zs : ℝ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (i : Fin m) (a : JointAction 2)
    (q : Fin 3→ℝ) (ω : Sample m 2 unitInterval) : ℝ :=
  if sourceCanonicalSelected ξ Λ r U zs c μseed α
      (focalInputContext R i a (ω.1.1,ω.2)) then q (focalCount Γ i a ω) else 0

theorem measurable_sourceCanonicalSampleTest {c : ℕ}
    (Γ : FiniteGame m 2 c unitInterval) (R ξ Λ r U zs : ℝ)
    (hξ : 0<ξ) (hΛ : 0<Λ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (hα : Measurable α)
    (i : Fin m) (a : JointAction 2) (q : Fin 3→ℝ) :
    Measurable (sourceCanonicalSampleTest Γ R ξ Λ r U zs μseed α i a q) :=
  Measurable.ite ((measurableSet_sourceCanonicalSelected ξ Λ r U zs hξ hΛ c μseed α hα).preimage
    ((measurable_focalInputContext R i a).comp (measurable_fst.fst.prodMk measurable_snd)))
    ((measurable_of_countable q).comp (measurable_focalCount Γ i a)) measurable_const

theorem abs_sourceCanonicalSampleTest_le {c : ℕ}
    (Γ : FiniteGame m 2 c unitInterval) (R ξ Λ r U zs : ℝ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (i : Fin m) (a : JointAction 2)
    (q : Fin 3→ℝ) (ω : Sample m 2 unitInterval) :
    |sourceCanonicalSampleTest Γ R ξ Λ r U zs μseed α i a q ω|≤∑k : Fin 3,|q k| := by
  unfold sourceCanonicalSampleTest
  split_ifs
  · exact Finset.single_le_sum (f := fun k : Fin 3 => |q k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  · simpa only [abs_zero] using Finset.sum_nonneg (fun _ _=>abs_nonneg _)

omit [Nonempty (Fin m)] in
theorem integral_sample_test_eq_inputs {c : ℕ}
    (Γ : FiniteGame m 2 c unitInterval) (f : Sample m 2 unitInterval→ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ω,|f ω|≤ C) :
    (∫ω,f ω ∂sampleLaw Γ)=
      ∫x : UserProfile m 2×Equiv.Perm (Fin 2),
        (∫s,f ((x.1,s),x.2) ∂Measure.pi (fun _ : Fin 2=>Γ.seedLaw))
        ∂(userProfileLaw Γ).prod (permLaw 2) := by
  have hp := inputsToSample_measurePreserving Γ
  let ν := ((userProfileLaw Γ).prod (permLaw 2)).prod (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))
  have hi : Integrable (fun x => f (inputsToSample x)) ν :=
    Integrable.of_bound (hf.comp hp.measurable).aestronglyMeasurable C
      (ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs] using hC (inputsToSample x)))
  calc
    _ = ∫x, f (inputsToSample x) ∂ν := by
      have hmap := integral_map (μ := ν) hp.measurable.aemeasurable hf.aestronglyMeasurable
      have he : ν.map inputsToSample = sampleLaw Γ := by
        simpa only [ν,userProfileLaw] using hp.map_eq
      rw [he] at hmap
      exact hmap
    _ = _ := integral_prod _ hi

theorem source_canonical_private_moment (row : Uniform07.Row)
    (hc : 1≤ Uniform07.capacity m) (R Λ : ℝ) (hΛ : 0<Λ)
    (PL : ProbabilityMeasure (ℝ×JointAction 2))
    (α : ClassifiedContext m→ unitInterval) (hα : Measurable α)
    (hUR : Early.bidCap row< R) (d : UserProfile m 2)
    (hd : ∀k,sourceDrawShape (Early.bidCap row) R (d k))
    (i : Fin m) (a : JointAction 2) (haR : a.bid< R) (ha2 : a.routeCount=2)
    (τ : Equiv.Perm (Fin 2)) (q : Fin 3→ℝ) :
    let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
    let X := focalInputContext R i a (d,τ)
    (∫s : Fin 2→ unitInterval,sourceCanonicalSampleTest Γ R (Uniform07.xi row)
      Λ (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2)
      (sourceSeedMeasure row m hc R PL) α i a q ((d,s),τ)
      ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)))=
      (if budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X then
        privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
          (Uniform07.capacity m) X none i q else 0)+
      canonicalCountPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ (Early.demandRatio row) (Early.bidCap row) (Uniform07.capacity m) α X
        (sourceSeed (sourceSeedMeasure row m hc R PL) (Uniform07.cutoff row/2) X) i q := by
  let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
  let X := focalInputContext R i a (d,τ)
  let K := fun E => privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
    (source_xi_lt_one row) (Uniform07.capacity m) X E i q
  let P := sourcePlan (Uniform07.xi row) Λ (Early.demandRatio row)
    (Early.bidCap row) (Uniform07.cutoff row/2) (Uniform07.capacity m)
    (sourceSeedMeasure row m hc R PL) α X
  have h : (∫s : Fin 2 → unitInterval, q (focalCount Γ i a ((d,s),τ))
      ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) = K P := by
    convert! source_focal_private_moment row hc R Λ hΛ PL α hα hUR d hd i a haR ha2 τ q using 1
  have heplan := sourcePlan_eq_fromSeed (Uniform07.xi row) Λ (Early.demandRatio row)
    (Early.bidCap row) (Uniform07.cutoff row/2) (Uniform07.capacity m)
    (sourceSeedMeasure row m hc R PL) α X
  have heplan' := heplan
  dsimp only [X] at heplan'
  dsimp only
  by_cases he : budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X
  · have he' := he
    dsimp only [X] at he'
    simp only [sourceCanonicalSampleTest,sourceCanonicalSelected,he',true_or,if_true,
      canonicalCountPart,add_zero]
    convert! h.trans ((privateCountMoment_equal _ _ _ _ X P he i q).trans
      (privateCountMoment_equal _ _ _ _ X none he i q).symm) using 1
  · have he' := he
    dsimp only [X] at he'
    by_cases hp : P=none
    · have hp' := hp
      dsimp only [P,X] at hp'
      simp only [sourceCanonicalSampleTest,sourceCanonicalSelected,he',false_or,hp',
        ne_eq,not_true_eq_false,if_false,integral_zero,canonicalCountPart,←heplan',if_true,add_zero]
    · have hp' := hp
      dsimp only [P,X] at hp'
      simp only [sourceCanonicalSampleTest,sourceCanonicalSelected,he',false_or,hp',
        ne_eq,not_false_eq_true,if_true,canonicalCountPart,←heplan',if_false,zero_add]
      convert! h using 1

def sourceCanonicalPhysicalTestOfRow (row : Uniform07.Row) (R Λ zG width ε : ℝ)
    (i : Fin m) (a : JointAction 2) (q : Fin 3→ℝ)
    (x : UserProfile m 2×Equiv.Perm (Fin 2)) : ℝ :=
  let X := focalInputContext R i a x
  (if budget (Uniform07.capacity m) 0 X=budget (Uniform07.capacity m) 1 X then
    privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      (Uniform07.capacity m) X none i q else 0)+
  if rivalHasSeed (Uniform07.cutoff row/2) i (deleteFocal i x.1) then
    finiteCanonicalPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) (Uniform07.capacity m)
      (literalSourceAlpha row Λ zG width ε) X i q else 0

set_option maxHeartbeats 3000000 in
theorem sourceNativeGame_canonical_count_expect_physical
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
    (i : Fin m) (a : JointAction 2) (_ha0 : 0 < a.bid) (haR : a.bid < R)
    (ha2 : a.routeCount = 2) (q : Fin 3 → ℝ) (hq : q 0=0) :
    let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    (∫ω,sourceCanonicalSampleTest Γ R (Uniform07.xi row) Λ
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2)
      (sourceSeedMeasure row m hc R PL)
      (literalSourceAlpha row Λ zG width ε) i a q ω ∂sampleLaw Γ) =
      ∫x, sourceCanonicalPhysicalTestOfRow row R Λ zG width ε i a q x
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
    if budget c 0 (X x)=budget c 1 (X x) then
      privateCountMoment ξ (Uniform07.xi_pos row) (source_xi_lt_one row) c (X x) none i q else 0
  let F := fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
    canonicalCountPart ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ r U c α (X x) (sourceSeed μB zs (X x)) i q
  let H := fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
    if rivalHasSeed zs i (deleteFocal i x.1) then
      finiteCanonicalPart ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ r U c α (X x) i q else 0
  have hX : Measurable X := measurable_focalInputContext R i a
  have hB : Measurable B := by
    convert! Measurable.ite
      (measurableSet_eq_fun ((measurable_budget c 0).comp hX) ((measurable_budget c 1).comp hX))
      ((measurable_privateCountMoment ξ (Uniform07.xi_pos row)
        (source_xi_lt_one row) c i q).comp (hX.prodMk measurable_const)) measurable_const using 1
  have hF : Measurable F := by
    convert! (measurable_canonicalCountPart ξ (Uniform07.xi_pos row)
      (source_xi_lt_one row) Λ r U hΛ0 c α hα i q).comp
        (hX.prodMk ((measurable_sourceSeed μB zs).comp hX)) using 1
  have hH : Measurable H := Measurable.ite ((measurableSet_rivalHasSeed zs i).preimage
    ((measurable_deleteFocal i).comp measurable_fst))
    ((measurable_finiteCanonicalPart ξ (Uniform07.xi_pos row)
      (source_xi_lt_one row) Λ r U hΛ0 c α hα i q).comp hX) measurable_const
  have hBi : Integrable B V := Integrable.of_bound hB.aestronglyMeasurable
    (∑r : Fin 3, |q r|) (ae_of_all _ (fun x : UserProfile m 2 × Equiv.Perm (Fin 2) => by
      simpa only [Real.norm_eq_abs] using (show |B x|≤∑r : Fin 3,|q r| from by
        dsimp only [B]
        split_ifs
        · exact abs_privateCountMoment_le ξ (Uniform07.xi_pos row) (source_xi_lt_one row) c (X x) none i q
        · simpa only [abs_zero] using Finset.sum_nonneg (fun _ _=>abs_nonneg _))))
  have hFi : Integrable F V := Integrable.of_bound hF.aestronglyMeasurable
    (∑r : Fin 3, |q r|) (ae_of_all _ (fun x : UserProfile m 2 × Equiv.Perm (Fin 2) => by
      simpa only [Real.norm_eq_abs,F] using (abs_canonicalCountPart_le ξ
        (Uniform07.xi_pos row) (source_xi_lt_one row) Λ r U c α (X x)
        (sourceSeed μB zs (X x)) i q)))
  have hHi : Integrable H V := by
    apply Integrable.of_bound hH.aestronglyMeasurable (∑r : Fin 3, |q r|)
    apply ae_of_all
    intro x
    dsimp only [H]
    split_ifs
    · simpa only [Real.norm_eq_abs] using abs_finiteCanonicalPart_le ξ
        (Uniform07.xi_pos row) (source_xi_lt_one row) Λ r U c α (X x) i q
    · simp only [norm_zero]
      positivity
  have hshape := sourceNativeGame_profile_shape row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα
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
      canonicalCountPart ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ r U c α (Cr d) (sourceSeed μB zs (Cr d)) i q
    let Hr := fun d : RivalIndex i → UserDraw 2 =>
      if rivalHasSeed zs i d then finiteCanonicalPart ξ (Uniform07.xi_pos row)
        (source_xi_lt_one row) Λ r U c α (Cr d) i q else 0
    have hCr : Measurable Cr := (measurable_observedContext R 0).comp (measurable_focalLocalList i a τ 0)
    have hFr : Measurable Fr := (measurable_canonicalCountPart ξ (Uniform07.xi_pos row)
      (source_xi_lt_one row) Λ r U hΛ0 c α hα i q).comp
        (hCr.prodMk ((measurable_sourceSeed μB zs).comp hCr))
    have hHr : Measurable Hr := Measurable.ite (measurableSet_rivalHasSeed zs i)
      ((measurable_finiteCanonicalPart ξ (Uniform07.xi_pos row)
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
    calc
      _ = ∫d, Fr d ∂Measure.pi (fun _ : RivalIndex i => μ) := by
        rw [←hp.map_eq]
        exact (integral_map hp.measurable.aemeasurable hFr.aestronglyMeasurable).symm
      _ = ∫d, Hr d ∂Measure.pi (fun _ : RivalIndex i => μ) :=
        source_canonical_integral_broadcast row μ i hΛ hR hguard hUR hzG (by omega) hε c
          a haR ha2 τ q hq hroute hnoatoms
      _ = _ := by
        rw [←hp.map_eq]
        exact integral_map hp.measurable.aemeasurable hHr.aestronglyMeasurable
  dsimp only
  rw [integral_sample_test_eq_inputs Γ _
    (measurable_sourceCanonicalSampleTest Γ R ξ Λ r U zs (Uniform07.xi_pos row)
      hΛ0 (sourceSeedMeasure row m hc R PL) α hα i a q)
    (∑k : Fin 3,|q k|)
    (abs_sourceCanonicalSampleTest_le Γ R ξ Λ r U zs
      (sourceSeedMeasure row m hc R PL) α i a q)]
  change (∫x, (∫s : Fin 2 → unitInterval,
    sourceCanonicalSampleTest Γ R ξ Λ r U zs (sourceSeedMeasure row m hc R PL) α i a q ((x.1,s),x.2)
    ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) ∂V) = _
  calc
    _ = ∫x, B x+F x ∂V := by
      apply integral_congr_ae
      filter_upwards [(measurePreserving_fst (μ := ρ) (ν := permLaw 2)).quasiMeasurePreserving.ae hshape]
        with x hx
      rw [source_canonical_private_moment row hc R Λ hΛ0 PL α hα hUR x.1 hx i a haR ha2 x.2 q,hseed]
    _ = ∫x, B x+H x ∂V := by rw [integral_add hBi hFi,integral_add hBi hHi,hFH]
    _ = _ := rfl

end FCAppendix.Affine.Uniform07Finishing
