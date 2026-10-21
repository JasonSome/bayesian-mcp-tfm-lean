import FCAppendix.Affine.Uniform07Finishing.Native.PrivateCountMoment
import FCAppendix.Affine.Uniform07Finishing.Native.SeedValueInvariance

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative
open Existence.PayOnceBounded (listBids)
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

lemma sourcePlanFromSeed_some_alpha_pos (ξ Λ r U : ℝ) (c : ℕ) (seed : Option unitInterval)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (E : Finset (Fin m)) (hE:sourcePlanFromSeed ξ Λ r U c α X seed=some E) : 0<(α X:ℝ) := by
  dsimp only [sourcePlanFromSeed] at hE
  split_ifs at hE with hg
  · cases hs:seed with
    | none=>simp [hs,sampleSeedOption] at hE
    | some s=>
      have he:planSampler (max (budget c 0 X) (budget c 1 X)-commonBudget c X)
          (α X,sourceWeights ξ Λ r U X.1) s=some E := by
        simpa only [hs,sampleSeedOption] using hE
      exact planSampler_some_alpha_pos _ _ s E he

theorem sourcePlanFromSeed_exclusive_margin (i : Uniform07.Row) {Λ : ℝ}
    (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ) (c : ℕ) (seed : Option unitInterval)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (E : Finset (Fin m))
    (hE:sourcePlanFromSeed (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i)
      c α X seed=some E) :
    E.card=max (budget c 0 X) (budget c 1 X)-commonBudget c X ∧
    ∀k∈E,Λ+3*Early.nativeRadius i< entryBid (X.1 k) := by
  dsimp only [sourcePlanFromSeed] at hE
  split_ifs at hE with hg
  · cases hs:seed with
    | none=>simp [hs,sampleSeedOption] at hE
    | some s=>
      have he:planSampler (max (budget c 0 X) (budget c 1 X)-commonBudget c X)
          (α X,sourceWeights (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i) X.1) s=some E :=
        by simpa only [hs,sampleSeedOption] using hE
      obtain ⟨p,hp,rfl⟩:=planSampler_some_support _ _ s E he
      have hW:((∅:Finset (Fin m)).card:ℝ)+
          (max (budget c 0 X) (budget c 1 X)-commonBudget c X:ℕ)<
          WeightedSampling.totalWeight
            (sourceWeights (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i) X.1) := by
        simpa using hg.2
      refine ⟨by simpa using WeightedSampling.finalSet_card _ _ ∅ hW p hp,?_⟩
      intro k hk
      have hw:=WeightedSampling.finalSet_weight_pos _ _ ∅ hW (by simp) p hp k hk
      cases hb:X.1 k with
      | none=>simp [sourceWeights,eligibleWeight,hb] at hw
      | some b=>
        by_cases hbU:b≤ Early.bidCap i
        · simp only [sourceWeights,eligibleWeight,hb,if_pos hbU] at hw
          simpa only [hb,entryBid] using source_weight_positive_margin i hΛ hw
        · simp [sourceWeights,eligibleWeight,hb,hbU] at hw

theorem literal_sourcePlanFromSeed_certificate (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ) (seed : Option unitInterval)
    (X : StrictNative.ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀ k, entryBid (X.1 k) ≤ R) (E : Finset (Fin m))
    (hE : sourcePlanFromSeed (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row)
      c
      (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        zG (Uniform07.cutoff row) width ε c) X seed = some E) :
    ValidExclusive (Uniform07.xi row) X.1 (budget c 0 X) (budget c 1 X) E ∧
    ∃ y ∈ Icc (Λ-Early.nativeRadius row) (Λ+Early.nativeRadius row),
      ClippedResidual.remainingDemand (Uniform07.xi row) (fun k => entryBid (X.1 k)) E y =
        (commonBudget c X : ℝ) ∧
      EqualCapacity.positiveMarginal (Uniform07.xi row) (commonBudget c X)
        (listBids (remainder X.1 E)) =
          ClippedResidual.smallMarginal (Uniform07.xi row) y (fun k => entryBid (X.1 k)) E := by
  let α : ClassifiedContext m → unitInterval := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
    (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
    zG (Uniform07.cutoff row) width ε c
  have hα : 0 < (α X : ℝ) := sourcePlanFromSeed_some_alpha_pos _ _ _ _ c seed α X E hE
  have ho := sourceGuardAlpha_outer c hm hε X hα
  have hlo := ho 0
  have hhi := ho 1
  simp only [sourceSlacks, Matrix.cons_val_zero, Matrix.cons_val_one] at hlo hhi
  have hs : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
  have ha : 0 < Early.nativeRadius row := (Early.native_sampling_margin_guards row).1
  have hκ : Uniform07.kappa row = 1-Uniform07.xi row := by
    cases row <;> norm_num [Uniform07.kappa, Uniform07.kappaQ, Uniform07.xi, Uniform07.xiQ]
  have hξ1 : Uniform07.xi row < 1 := by
    cases row <;> norm_num [Uniform07.xi, Uniform07.xiQ, Uniform07.etaQ]
  have hl0 : 0 < Λ-Early.nativeRadius row :=
    (mul_pos (by rw [hκ]; linarith) hR).trans hguard
  have hdn : 0 < commonBudget c X := by
    have hn : 0 ≤ sourceDemand (Uniform07.xi row) (Λ+Early.nativeRadius row) X.1 :=
      Finset.sum_nonneg (fun k _ => ClippedResidual.exposure_nonneg
        (Uniform07.xi_pos row) (by linarith))
    have hh : (0 : ℝ) < commonBudget c X := by linarith
    exact_mod_cast hh
  obtain ⟨hcard,hmarg⟩ := sourcePlanFromSeed_exclusive_margin row hΛ c seed α X E hE
  have hl : (commonBudget c X : ℝ)+(E.card : ℝ)+ε*m <
      ∑k,ClippedResidual.exposure (Uniform07.xi row) (Λ-Early.nativeRadius row)
        (entryBid (X.1 k)) := by
    rw [hcard]
    change _ < sourceDemand (Uniform07.xi row) (Λ-Early.nativeRadius row) X.1
    linarith
  have hh : (∑k,ClippedResidual.exposure (Uniform07.xi row) (Λ+Early.nativeRadius row)
      (entryBid (X.1 k))) < (commonBudget c X : ℝ)-ε*m := by
    change sourceDemand (Uniform07.xi row) (Λ+Early.nativeRadius row) X.1 < _
    linarith
  exact (source_U4_passes_native_test X.1 hX (budget c 0 X) (budget c 1 X) E
    (Uniform07.xi_pos row) hξ1 hR hl0 (by linarith) (by rwa [← hκ]) hbid hdn hs
    hcard hl hh (fun k hk => by linarith [hmarg k hk]))

omit [Nonempty (Fin m)] in
theorem SeedEquivalentContext.entry_change {zs : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (i : Fin m) :
    (entryBid (X.1 i) ≤ zs ∧ entryBid (Y.1 i) ≤ zs) ∨ X.1 i = Y.1 i := by
  rcases h.2 i with he | ⟨b,b',hb,hb',hz,hz'⟩
  · exact Or.inr he
  · exact Or.inl ⟨by simpa only [hb,entryBid] using hz,
      by simpa only [hb',entryBid] using hz'⟩

omit [Nonempty (Fin m)] in
theorem SeedEquivalentContext.present {zs : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (i : Fin m) : X.1 i ≠ none ↔ Y.1 i ≠ none := by
  rcases h.2 i with he | ⟨b,b',hb,hb',_,_⟩
  · rw [he]
  · simp [hb,hb']

omit [Nonempty (Fin m)] in
theorem seedEquivalent_larger {zs : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (c : ℕ) : larger c X = larger c Y := by
  simp only [larger,seedEquivalent_budget h]

def sourceCountCorrection (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (X : ClassifiedContext m) (seed : Option unitInterval) (i : Fin m) (q : Fin 3 → ℝ) : ℝ :=
  privateCountMoment ξ hξ hξ1 c X (sourcePlanFromSeed ξ Λ r U c α X seed) i q -
    privateCountMoment ξ hξ hξ1 c X none i q

@[simp] theorem sourceCountCorrection_none (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ) :
    sourceCountCorrection ξ hξ hξ1 Λ r U c α X none i q = 0 := by
  have he : sourcePlanFromSeed ξ Λ r U c α X none = none := by
    dsimp only [sourcePlanFromSeed]
    split_ifs <;> rfl
  simp only [sourceCountCorrection,he,sub_self]

theorem sourceCountCorrection_equal (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (X : ClassifiedContext m) (seed : Option unitInterval)
    (he : budget c 0 X = budget c 1 X) (i : Fin m) (q : Fin 3 → ℝ) :
    sourceCountCorrection ξ hξ hξ1 Λ r U c α X seed i q = 0 := by
  rw [sourceCountCorrection,privateCountMoment_equal _ _ _ _ _ _ he,
    privateCountMoment_equal _ _ _ _ _ _ he,sub_self]

theorem actual_privateCount_baseline_add_correction
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (Λ r U zs : ℝ) (c : ℕ)
    (μseed : Measure ℝ) (α : ClassifiedContext m → unitInterval)
    (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ) :
    privateCountMoment ξ hξ hξ1 c X (sourcePlan ξ Λ r U zs c μseed α X) i q =
      privateCountMoment ξ hξ hξ1 c X none i q +
        sourceCountCorrection ξ hξ hξ1 Λ r U c α X (sourceSeed μseed zs X) i q := by
  rw [sourcePlan_eq_fromSeed,sourceCountCorrection]
  ring

def finitePathCountCorrection (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ) : ℝ :=
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let w := sourceWeights ξ Λ r U X.1
  if (exceptionalSet U X.1).card ≤ 1 ∧ (Δ : ℝ) < WeightedSampling.totalWeight w then
    (α X : ℝ)*((WeightedSampling.pathLaw w Δ ∅).expect
      (fun path => privateCountMoment ξ hξ hξ1 c X
        (some (WeightedSampling.finalSet Δ ∅ path)) i q)-
      privateCountMoment ξ hξ hξ1 c X none i q)
  else 0

theorem integral_sourceCountCorrection (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (c : ℕ) (α : ClassifiedContext m → unitInterval)
    (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ) :
    (∫s : unitInterval, sourceCountCorrection ξ hξ hξ1 Λ r U c α X (some s) i q) =
      finitePathCountCorrection ξ hξ hξ1 Λ r U c α X i q := by
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let w := sourceWeights ξ Λ r U X.1
  let f := fun E : Option (Finset (Fin m)) => privateCountMoment ξ hξ hξ1 c X E i q
  by_cases hg : (exceptionalSet U X.1).card ≤ 1 ∧ (Δ : ℝ) < WeightedSampling.totalWeight w
  · dsimp only [Δ,w] at hg
    have he (s : unitInterval) : sourcePlanFromSeed ξ Λ r U c α X (some s) =
        planSampler Δ (α X,w) s := by simp only [sourcePlanFromSeed,Δ,w,if_pos hg,sampleSeedOption]
    have hm : Measurable (planSampler Δ (α X,w)) :=
      (measurable_planSampler Δ).comp (measurable_const.prodMk measurable_id)
    have hi : Integrable (fun s => f (planSampler Δ (α X,w) s)) volume := by
      apply Integrable.of_bound ((measurable_of_countable f).comp hm).aestronglyMeasurable
        (∑E : Option (Finset (Fin m)), |f E|)
      exact ae_of_all _ (fun s => by
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (fun E _ => abs_nonneg (f E)) (Finset.mem_univ _))
    have hmap : (∫s : unitInterval, f (planSampler Δ (α X,w) s)) =
        (planLaw Δ (α X) w).expect f := by
      rw [←LowBody.integral_probabilityMeasure]
      rw [←planSampler_law Δ (α X,w)]
      exact (integral_map_of_stronglyMeasurable hm
        (measurable_of_countable f).stronglyMeasurable).symm
    simp only [sourceCountCorrection,he,finitePathCountCorrection,if_pos hg]
    rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,
      smul_eq_mul,one_mul,hmap,planLaw_expect]
    dsimp only [f,Δ,w]
    ring
  · dsimp only [Δ,w] at hg
    have he (s : unitInterval) : sourcePlanFromSeed ξ Λ r U c α X (some s) = none := by
      simp only [sourcePlanFromSeed,if_neg hg]
    simp only [sourceCountCorrection,he,sub_self,integral_zero,
      finitePathCountCorrection,if_neg hg]

theorem literal_sourcePlanFromSeed_clipped_seed_change (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ) (seed : Option unitInterval)
    (X Y : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀ k, entryBid (X.1 k) ≤ R) (hbid' : ∀ k, entryBid (Y.1 k) ≤ R)
    (hchange : SeedEquivalentContext (Uniform07.cutoff row/2) X Y)
    (E : Finset (Fin m))
    (hE : sourcePlanFromSeed (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) c
      (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        zG (Uniform07.cutoff row) width ε c) X seed = some E) :
    EqualCapacity.positiveMarginal (Uniform07.xi row) (commonBudget c X)
      (listBids (remainder X.1 E)) =
        EqualCapacity.positiveMarginal (Uniform07.xi row) (commonBudget c Y)
          (listBids (remainder Y.1 E)) := by
  obtain ⟨_,y,hy,hr,he⟩ := literal_sourcePlanFromSeed_certificate row
    hΛ hR hguard hm hε c seed X hX hbid E hE
  have hlow := ((Early.native_sampling_margin_guards row).2 Λ hΛ).1
  have h52 : (52/100 : ℝ)*Uniform07.cutoff row < Λ-Early.nativeRadius row :=
    (le_max_right _ _).trans_lt hlow
  have ht := Uniform07.cutoff_pos row
  have hy0 : 0 < y := by linarith [hy.1]
  have hseed : Uniform07.cutoff row/2 ≤ y := by linarith [hy.1]
  have hκ : Uniform07.kappa row = 1-Uniform07.xi row := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xi,Uniform07.xiQ]
  have hξ1 : Uniform07.xi row < 1 := by
    cases row <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  have hroot : (∑k,ClippedResidual.exposure (Uniform07.xi row) y
      (listBids (remainder X.1 E) k)) = (commonBudget c X : ℝ) := by
    calc
      _ = ClippedResidual.remainingDemand (Uniform07.xi row) (fun k => entryBid (X.1 k)) E y := by
        unfold ClippedResidual.remainingDemand
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ E
        · simp [remainder_bid,hk,ClippedResidual.exposure_zero hy0.le]
        · simp only [listBids_eq_entry,remainder_entry,if_neg hk]
      _ = _ := hr
  rw [←seedEquivalent_commonBudget hchange c]
  exact clipped_marginal_seed_change (Uniform07.xi_pos row) hξ1 hy0
    (by rw [←hκ]; exact hguard.le.trans hy.1) hseed X.1 Y.1 E (commonBudget c X)
    hbid hbid' hR.le hchange.entry_change hroot

theorem literal_sourceCountCorrection_seed_change (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2 ≤ zG)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ) (seed : Option unitInterval)
    (X Y : ClassifiedContext m) (hX : NonnegativeList X.1) (hY : NonnegativeList Y.1)
    (hbid : ∀ k, entryBid (X.1 k) ≤ R) (hbid' : ∀ k, entryBid (Y.1 k) ≤ R)
    (hchange : SeedEquivalentContext (Uniform07.cutoff row/2) X Y)
    (i : Fin m) (q : Fin 3 → ℝ)
    (hgeneric : ∀ P Q : ResidualPotential.Pair m,
      ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) P →
      ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) Q →
      CompleteInformation.potential (1-Uniform07.xi row) (ResidualPotential.bid X.1) P.1 P.2 =
        CompleteInformation.potential (1-Uniform07.xi row) (ResidualPotential.bid X.1) Q.1 Q.2 →
      focalCopy P i = focalCopy Q i) :
    sourceCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
      (by cases row <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ])
      Λ (Early.demandRatio row) (Early.bidCap row) c
      (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        zG (Uniform07.cutoff row) width ε c) X seed i q =
    sourceCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
      (by cases row <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ])
      Λ (Early.demandRatio row) (Early.bidCap row) c
      (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        zG (Uniform07.cutoff row) width ε c) Y seed i q := by
  let ξ := Uniform07.xi row
  have hξ : 0 < ξ := Uniform07.xi_pos row
  have hξ1 : ξ < 1 := by cases row <;> norm_num [ξ,Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  let α : ClassifiedContext m → unitInterval := sourceGuardAlpha ξ Λ (Early.nativeRadius row) (Early.demandRatio row)
    (Early.bidCap row) (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c
  have ha := (Early.native_sampling_margin_guards row).1
  have hlow := ((Early.native_sampling_margin_guards row).2 Λ hΛ).1
  have h52 : (52/100 : ℝ)*Uniform07.cutoff row < Λ-Early.nativeRadius row :=
    (le_max_right _ _).trans_lt hlow
  have ht := Uniform07.cutoff_pos row
  have hzΛ : Uniform07.cutoff row/2 ≤ Λ-Early.nativeRadius row := by linarith
  have hzU : Uniform07.cutoff row/2 ≤ Early.bidCap row := by
    rcases Early.scalar_floor_cap_guards row with
      ⟨hχ,hhalf,hχeta,hfloor,hκ,hcap,hrest⟩
    have hh : Uniform07.cutoff row/2 < Early.chi*Uniform07.cutoff row := by nlinarith
    exact hh.le.trans hcap.le
  have hplan := seedEquivalent_sourcePlanFromSeed (ξ := ξ)
    (d₀ := Uniform07.cutoff row/1000) (t := Uniform07.cutoff row)
    (width := width) (ε := ε) hchange (Early.demandRatio_pos row)
    ha.le hzΛ hzG hzU c seed
  change sourceCountCorrection ξ hξ hξ1 Λ (Early.demandRatio row) (Early.bidCap row)
      c α X seed i q = sourceCountCorrection ξ hξ hξ1 Λ (Early.demandRatio row)
        (Early.bidCap row) c α Y seed i q
  by_cases hEq : budget c 0 X = budget c 1 X
  · have hEq' : budget c 0 Y = budget c 1 Y := by
      rwa [←seedEquivalent_budget hchange c 0,←seedEquivalent_budget hchange c 1]
    rw [sourceCountCorrection_equal _ _ _ _ _ _ _ _ _ _ hEq,
      sourceCountCorrection_equal _ _ _ _ _ _ _ _ _ _ hEq']
  have hEq' : budget c 0 Y ≠ budget c 1 Y := by
    rwa [←seedEquivalent_budget hchange c 0,←seedEquivalent_budget hchange c 1]
  cases hE : sourcePlanFromSeed ξ Λ (Early.demandRatio row) (Early.bidCap row) c α X seed with
  | none =>
      have hE' : sourcePlanFromSeed ξ Λ (Early.demandRatio row) (Early.bidCap row) c α Y seed = none :=
        hplan.symm.trans hE
      simp only [sourceCountCorrection,hE,hE',sub_self]
  | some E =>
      have hE' : sourcePlanFromSeed ξ Λ (Early.demandRatio row) (Early.bidCap row) c α Y seed = some E :=
        hplan.symm.trans hE
      have hv := (literal_sourcePlanFromSeed_certificate row hΛ hR hguard hm hε
        c seed X hX hbid E hE).1
      have hv' := (literal_sourcePlanFromSeed_certificate row hΛ hR hguard hm hε
        c seed Y hY hbid' E hE').1
      have hp := literal_sourcePlanFromSeed_clipped_seed_change row hΛ hR hguard hm hε
        c seed X Y hX hbid hbid' hchange E hE
      have hα : 0 < (α X : ℝ) := sourcePlanFromSeed_some_alpha_pos _ _ _ _ c seed α X E hE
      have hg := sourceGuardAlpha_outer c hm hε X hα 3
      change ε*(m : ℝ) < sourceRejectionDemand (Uniform07.cutoff row/1000) zG X.1 -
        (budget c 0 X : ℝ) - (budget c 1 X : ℝ) at hg
      have hd : 0 < Uniform07.cutoff row/1000 := div_pos ht (by norm_num)
      have hs : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
      have hb := sourceRejectionDemand_le_high_card hd zG X.1
      have hhigh : budget c 0 X+budget c 1 X < (highBidSet zG X.1).card := by
        have hh : ((budget c 0 X+budget c 1 X : ℕ) : ℝ) <
            ((highBidSet zG X.1).card : ℝ) := by push_cast; linarith
        exact_mod_cast hh
      have hcopy := residual_selection_focalCopy_seed_change
        (by linarith : 0 ≤ 1-ξ) (by linarith : 1-ξ ≤ 1) (by linarith : 0 ≤ zG)
        hzG X.1 Y.1 (budget c 0 X) (budget c 1 X)
        hchange.present hchange.entry_change hhigh i hgeneric
      have hbase : privateCountMoment ξ hξ hξ1 c X none i q =
          privateCountMoment ξ hξ hξ1 c Y none i q := by
        rw [privateCountMoment_none _ _ _ _ _ hEq,
          privateCountMoment_none _ _ _ _ _ hEq']
        apply congrArg q
        simpa only [purePair,seedEquivalent_budget hchange] using hcopy
      have hweighted : privateCountMoment ξ hξ hξ1 c X (some E) i q =
          privateCountMoment ξ hξ hξ1 c Y (some E) i q := by
        rw [privateCountMoment_weighted _ _ _ _ _ _ hEq hv,
          privateCountMoment_weighted _ _ _ _ _ _ hEq' hv']
        dsimp only
        rw [hp,seedEquivalent_larger hchange c]
      simp only [sourceCountCorrection,hE,hE',hweighted,hbase]

theorem literal_sourceCountCorrection_seed_focal_zero (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2 ≤ zG)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ) (seed : Option unitInterval)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀ k, entryBid (X.1 k) ≤ R) (i : Fin m)
    (hi : entryBid (X.1 i) ≤ Uniform07.cutoff row/2) (q : Fin 3 → ℝ) :
    sourceCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
      (by cases row <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ])
      Λ (Early.demandRatio row) (Early.bidCap row) c
      (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        zG (Uniform07.cutoff row) width ε c) X seed i q = 0 := by
  let ξ := Uniform07.xi row
  have hξ : 0 < ξ := Uniform07.xi_pos row
  have hξ1 : ξ < 1 := by cases row <;> norm_num [ξ,Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  let α : ClassifiedContext m → unitInterval := sourceGuardAlpha ξ Λ (Early.nativeRadius row) (Early.demandRatio row)
    (Early.bidCap row) (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c
  change sourceCountCorrection ξ hξ hξ1 Λ (Early.demandRatio row) (Early.bidCap row)
    c α X seed i q = 0
  by_cases heq : budget c 0 X = budget c 1 X
  · exact sourceCountCorrection_equal _ _ _ _ _ _ _ _ _ _ heq i q
  cases hE : sourcePlanFromSeed ξ Λ (Early.demandRatio row) (Early.bidCap row) c α X seed with
  | none => simp only [sourceCountCorrection,hE,sub_self]
  | some E =>
      obtain ⟨hv,y,hy,hr,hp⟩ := literal_sourcePlanFromSeed_certificate row
        hΛ hR hguard hm hε c seed X hX hbid E hE
      have hmargin := (sourcePlanFromSeed_exclusive_margin row hΛ c seed α X E hE).2
      have ha := (Early.native_sampling_margin_guards row).1
      have ht := Uniform07.cutoff_pos row
      have hlow := ((Early.native_sampling_margin_guards row).2 Λ hΛ).1
      have h52 : (52/100 : ℝ)*Uniform07.cutoff row < Λ-Early.nativeRadius row :=
        (le_max_right _ _).trans_lt hlow
      have hiy : entryBid (X.1 i) ≤ y := by linarith [hy.1]
      have hiE : i ∉ E := by
        intro hie
        have hh := hmargin i hie
        linarith
      have hp0 : EqualCapacity.positiveMarginal ξ (commonBudget c X)
          (listBids (remainder X.1 E)) i = 0 := by
        rw [hp]
        simp only [ClippedResidual.smallMarginal,if_neg hiE]
        exact ClippedResidual.exposure_zero hiy
      have hα : 0 < (α X : ℝ) := sourcePlanFromSeed_some_alpha_pos _ _ _ _ c seed α X E hE
      have hre := sourceGuardAlpha_pure_rejects_seed hξ hξ1
        (div_pos ht (by norm_num : (0 : ℝ) < 1000)) (by linarith : 0 ≤ zG)
        hzG c hm hε X hα i hi
      have hcopy : focalCopy (purePair ξ c X) i = 0 := by simp [focalCopy,hre.1,hre.2]
      rw [sourceCountCorrection,hE,privateCountMoment_weighted _ _ _ _ _ _ heq hv,
        privateCountMoment_none _ _ _ _ _ heq,hcopy]
      dsimp only [ξ] at hp0
      simp [hp0,hiE,twoCountPolynomial]

end FCAppendix.Affine.Uniform07Finishing.Weighted
