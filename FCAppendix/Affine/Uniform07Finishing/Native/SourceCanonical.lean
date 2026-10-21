import FCAppendix.Affine.Uniform07Finishing.Native.SourcePhysicalCounts
import FCAppendix.Affine.Uniform07Finishing.Native.SourceBalancedExperiment

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

def canonicalCountPart (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (Λ r U : ℝ)
    (c : ℕ) (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (seed : Option unitInterval) (i : Fin m) (q : Fin 3→ℝ) : ℝ :=
  if budget c 0 X=budget c 1 X then 0 else
    if sourcePlanFromSeed ξ Λ r U c α X seed=none then 0 else
      privateCountMoment ξ hξ hξ1 c X (sourcePlanFromSeed ξ Λ r U c α X seed) i q

def finiteCanonicalPart (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (Λ r U : ℝ)
    (c : ℕ) (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (i : Fin m) (q : Fin 3→ℝ) : ℝ :=
  ∫s : unitInterval,canonicalCountPart ξ hξ hξ1 Λ r U c α X (some s) i q ∂volume

theorem measurable_canonicalCountPart (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (Λ r U : ℝ) (hΛ : 0<Λ) (c : ℕ) (α : ClassifiedContext m→ unitInterval)
    (hα : Measurable α) (i : Fin m) (q : Fin 3→ℝ) :
    Measurable (fun p : ClassifiedContext m×Option unitInterval=>
      canonicalCountPart ξ hξ hξ1 Λ r U c α p.1 p.2 i q) := by
  have hp := Weighted.measurable_sourcePlanFromSeed ξ Λ r U hξ hΛ c α hα
  have hinput : Measurable (fun p : ClassifiedContext m × Option unitInterval =>
      (p.1,sourcePlanFromSeed ξ Λ r U c α p.1 p.2)) := measurable_fst.prodMk hp
  have hvalue := (measurable_privateCountMoment ξ hξ hξ1 c i q).comp hinput
  change Measurable (fun p : ClassifiedContext m × Option unitInterval =>
    if budget c 0 p.1 = budget c 1 p.1 then 0 else
      if sourcePlanFromSeed ξ Λ r U c α p.1 p.2 = none then 0 else
        privateCountMoment ξ hξ hξ1 c p.1 (sourcePlanFromSeed ξ Λ r U c α p.1 p.2) i q)
  exact Measurable.ite
    (measurableSet_eq_fun ((Weighted.measurable_budget c 0).comp measurable_fst)
      ((Weighted.measurable_budget c 1).comp measurable_fst)) measurable_const
    (Measurable.ite (measurableSet_eq_fun hp measurable_const) measurable_const
      hvalue)

theorem abs_canonicalCountPart_le (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (Λ r U : ℝ)
    (c : ℕ) (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (seed : Option unitInterval) (i : Fin m) (q : Fin 3→ℝ) :
    |canonicalCountPart ξ hξ hξ1 Λ r U c α X seed i q|≤∑k : Fin 3,|q k| := by
  unfold canonicalCountPart
  split_ifs
  · simpa only [abs_zero] using Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  · simpa only [abs_zero] using Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  · exact abs_privateCountMoment_le _ _ _ _ _ _ _ _

theorem measurable_finiteCanonicalPart (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (Λ r U : ℝ) (hΛ : 0<Λ) (c : ℕ) (α : ClassifiedContext m→ unitInterval)
    (hα : Measurable α) (i : Fin m) (q : Fin 3→ℝ) :
    Measurable (fun X=>finiteCanonicalPart ξ hξ hξ1 Λ r U c α X i q) := by
  have hh := (measurable_canonicalCountPart ξ hξ hξ1 Λ r U hΛ c α hα i q).comp
    (measurable_fst.prodMk (measurable_some.comp measurable_snd))
  have hi := (hh.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure unitInterval))).measurable
  simpa only [finiteCanonicalPart,Function.comp_def] using hi

theorem abs_finiteCanonicalPart_le (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (Λ r U : ℝ)
    (c : ℕ) (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (i : Fin m) (q : Fin 3→ℝ) :
    |finiteCanonicalPart ξ hξ hξ1 Λ r U c α X i q|≤∑k : Fin 3,|q k| := by
  have hb : ∀ᵐ s : unitInterval ∂volume,
      ‖canonicalCountPart ξ hξ hξ1 Λ r U c α X (some s) i q‖ ≤ ∑ k : Fin 3, |q k| :=
    ae_of_all _ (fun s => by
      simpa only [Real.norm_eq_abs] using
        (abs_canonicalCountPart_le ξ hξ hξ1 Λ r U c α X (some s) i q))
  simpa only [finiteCanonicalPart,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const hb

@[simp] theorem canonicalCountPart_none (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (Λ r U : ℝ)
    (c : ℕ) (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (i : Fin m) (q : Fin 3→ℝ) :
    canonicalCountPart ξ hξ hξ1 Λ r U c α X none i q=0 := by
  have he : sourcePlanFromSeed ξ Λ r U c α X none = none := by
    dsimp only [sourcePlanFromSeed]
    split_ifs <;> rfl
  simp [canonicalCountPart,he]

theorem finiteCanonicalPart_formula (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (Λ r U : ℝ) (c : ℕ) (α : ClassifiedContext m→ unitInterval)
    (X : ClassifiedContext m) (i : Fin m) (q : Fin 3→ℝ) :
    finiteCanonicalPart ξ hξ hξ1 Λ r U c α X i q=
      if budget c 0 X=budget c 1 X then 0 else
      let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
      let w := sourceWeights ξ Λ r U X.1
      if (exceptionalSet U X.1).card≤ 1 ∧ (Δ:ℝ)< WeightedSampling.totalWeight w then
        (α X:ℝ)*(WeightedSampling.pathLaw w Δ ∅).expect
          (fun path=>privateCountMoment ξ hξ hξ1 c X
            (some (WeightedSampling.finalSet Δ ∅ path)) i q)
      else 0 := by
  dsimp only
  by_cases he : budget c 0 X=budget c 1 X
  · simp only [finiteCanonicalPart,canonicalCountPart,he,if_true,integral_zero]
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let w := sourceWeights ξ Λ r U X.1
  let f : Option (Finset (Fin m))→ℝ := fun E=>
    if E=none then 0 else privateCountMoment ξ hξ hξ1 c X E i q
  by_cases hg : (exceptionalSet U X.1).card≤ 1 ∧ (Δ:ℝ)< WeightedSampling.totalWeight w
  · dsimp only [Δ,w] at hg
    have hp (s : unitInterval) : sourcePlanFromSeed ξ Λ r U c α X (some s)=
        planSampler Δ (α X,w) s := by
      simp only [sourcePlanFromSeed,Δ,w,if_pos hg,sampleSeedOption]
    have hm : Measurable (planSampler Δ (α X,w)) :=
      (measurable_planSampler Δ).comp (measurable_const.prodMk measurable_id)
    have hmap : (∫s : unitInterval,f (planSampler Δ (α X,w) s))=
        (planLaw Δ (α X) w).expect f := by
      rw [←LowBody.integral_probabilityMeasure,←planSampler_law Δ (α X,w)]
      exact (integral_map_of_stronglyMeasurable hm
        (measurable_of_countable f).stronglyMeasurable).symm
    simp only [finiteCanonicalPart,canonicalCountPart,if_neg he,hp,if_pos hg]
    change (∫s : unitInterval,f (planSampler Δ (α X,w) s))=_
    rw [hmap,planLaw_expect]
    simp [f,Δ,w]
  · dsimp only [Δ,w] at hg
    have hp (s : unitInterval) : sourcePlanFromSeed ξ Λ r U c α X (some s)=none := by
      simp only [sourcePlanFromSeed,if_neg hg]
    simp only [finiteCanonicalPart,canonicalCountPart,if_neg he,hp,if_true,
      integral_zero,if_neg hg]

theorem literal_canonicalCountPart_seed_change (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100:ℝ)*Uniform07.cutoff row<Λ) (hR : 0< R)
    (hguard : Uniform07.kappa row*R<Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2≤ zG) (hm : 0< m) (hε : 0<ε) (c : ℕ)
    (seed : Option unitInterval) (X Y : ClassifiedContext m)
    (hX : NonnegativeList X.1) (hY : NonnegativeList Y.1)
    (hbid : ∀k,entryBid (X.1 k)≤ R) (hbid' : ∀k,entryBid (Y.1 k)≤ R)
    (hchange : SeedEquivalentContext (Uniform07.cutoff row/2) X Y)
    (i : Fin m) (q : Fin 3→ℝ) :
    let α := (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c)
    canonicalCountPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) c α X seed i q=
    canonicalCountPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) c α Y seed i q := by
  let ξ := Uniform07.xi row
  let α : ClassifiedContext m → unitInterval := (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c)
  have hzΛ : Uniform07.cutoff row/2≤Λ-Early.nativeRadius row := by
    have hh := (le_max_right _ _).trans_lt (((Early.native_sampling_margin_guards row).2 Λ hΛ).1)
    have ht := Uniform07.cutoff_pos row
    linarith
  have hplan := seedEquivalent_sourcePlanFromSeed (ξ := ξ) (d₀ := Uniform07.cutoff row/1000)
    (t := Uniform07.cutoff row) (width := width) (ε := ε) hchange (Early.demandRatio_pos row)
    (Early.native_sampling_margin_guards row).1.le hzΛ hzG
    (source_seed_cutoff_lt_bidCap row).le c seed
  have hb0 := seedEquivalent_budget hchange c 0
  have hb1 := seedEquivalent_budget hchange c 1
  change canonicalCountPart ξ _ _ Λ _ _ c α X seed i q=
    canonicalCountPart ξ _ _ Λ _ _ c α Y seed i q
  by_cases he : budget c 0 X=budget c 1 X
  · simp only [canonicalCountPart,he,←hb0,←hb1,if_true]
  · have he' : budget c 0 Y≠budget c 1 Y := by rwa [←hb0,←hb1]
    cases hE : sourcePlanFromSeed ξ Λ (Early.demandRatio row) (Early.bidCap row) c α X seed with
    | none =>
      have hE' : sourcePlanFromSeed ξ Λ (Early.demandRatio row) (Early.bidCap row) c α Y seed=none :=
        hplan.symm.trans hE
      simp only [canonicalCountPart,if_neg he,if_neg he',hE,hE',if_true]
    | some E =>
      have hE' : sourcePlanFromSeed ξ Λ (Early.demandRatio row) (Early.bidCap row) c α Y seed=some E :=
        hplan.symm.trans hE
      have hv := (literal_sourcePlanFromSeed_certificate row hΛ hR hguard hm hε c seed X hX hbid E hE).1
      have hv' := (literal_sourcePlanFromSeed_certificate row hΛ hR hguard hm hε c seed Y hY hbid' E hE').1
      have hp := literal_sourcePlanFromSeed_clipped_seed_change row hΛ hR hguard hm hε
        c seed X Y hX hbid hbid' hchange E hE
      simp [canonicalCountPart,he,he',hE,hE']
      rw [privateCountMoment_weighted _ _ _ _ _ _ he hv,
        privateCountMoment_weighted _ _ _ _ _ _ he' hv']
      dsimp only
      rw [hp,seedEquivalent_larger hchange c]

theorem literal_canonicalCountPart_seed_focal_zero (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100:ℝ)*Uniform07.cutoff row<Λ) (hR : 0< R)
    (hguard : Uniform07.kappa row*R<Λ-Early.nativeRadius row)
    (hm : 0< m) (hε : 0<ε) (c : ℕ) (seed : Option unitInterval)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀k,entryBid (X.1 k)≤ R) (i : Fin m)
    (hi : entryBid (X.1 i)≤ Uniform07.cutoff row/2) (q : Fin 3→ℝ) (hq : q 0=0) :
    canonicalCountPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) c ((sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c))
      X seed i q=0 := by
  let α : ClassifiedContext m → unitInterval := (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c)
  change canonicalCountPart (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
    Λ (Early.demandRatio row) (Early.bidCap row) c α X seed i q = 0
  by_cases he : budget c 0 X=budget c 1 X
  · simp only [canonicalCountPart,he,if_true]
  cases hE : sourcePlanFromSeed (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) c α X seed with
  | none => simp [canonicalCountPart,he,hE]
  | some E =>
    obtain ⟨hv,y,hy,hr,hp⟩ := literal_sourcePlanFromSeed_certificate row
      hΛ hR hguard hm hε c seed X hX hbid E hE
    have hmarg := (sourcePlanFromSeed_exclusive_margin row hΛ c seed α X E hE).2
    have hlo := (le_max_right _ _).trans_lt (((Early.native_sampling_margin_guards row).2 Λ hΛ).1)
    have ht := Uniform07.cutoff_pos row
    have ha := (Early.native_sampling_margin_guards row).1
    have hiy : entryBid (X.1 i)≤ y := by linarith [hy.1]
    have hin : i∉E := by
      intro hie
      have hh := hmarg i hie
      linarith
    have hp0 : EqualCapacity.positiveMarginal (Uniform07.xi row) (commonBudget c X)
        (Existence.PayOnceBounded.listBids (remainder X.1 E)) i=0 := by
      rw [hp]
      simp only [ClippedResidual.smallMarginal,if_neg hin]
      exact ClippedResidual.exposure_zero hiy
    simp [canonicalCountPart,he,hE]
    rw [privateCountMoment_weighted _ _ _ _ _ _ he hv]
    simp only [hp0,hin,and_false,if_false,twoCountPolynomial,hq]
    ring

end FCAppendix.Affine.Uniform07Finishing
