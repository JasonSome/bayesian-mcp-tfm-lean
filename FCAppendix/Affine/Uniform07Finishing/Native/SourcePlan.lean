import FCAppendix.Affine.Uniform07Finishing.Native.GuardedCorrespondence
import FCAppendix.Affine.Hybrid.ObservedSeed
import FCAppendix.Affine.Uniform07Finishing.Native.MultipleFallback

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open StrictNative
open scoped BigOperators
variable {m : ℕ}

def guardWeight (r p : ℝ) : ℝ := min 1 (max 0 ((4*p-r)/r))

lemma guardWeight_bounds (r p : ℝ) : guardWeight r p∈Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩

lemma guardWeight_zero {r p : ℝ} (hr:0< r) (hp:p≤ r/4) : guardWeight r p=0 := by
  have h:(4*p-r)/r≤ 0:=div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  simp only [guardWeight,max_eq_left h,min_eq_right zero_le_one]

lemma guardWeight_positive {r p : ℝ} (hr:0< r) (hp:0< guardWeight r p) : r/4< p := by
  by_contra hn
  rw [guardWeight_zero hr (le_of_not_gt hn)] at hp
  exact (lt_irrefl 0) hp

lemma continuous_guardWeight (r : ℝ) : Continuous (guardWeight r) := by
  unfold guardWeight
  fun_prop

def eligibleWeight (ξ Λ r U : ℝ) : Option ℝ→ℝ
  | none=>0
  | some b=>if b≤ U then guardWeight r (ClippedResidual.exposure ξ Λ b) else 0

lemma measurable_eligibleWeight (ξ Λ r U : ℝ) (hξ:0<ξ) (hΛ:0<Λ) :
    Measurable (eligibleWeight ξ Λ r U) := by
  intro S hS
  change MeasurableSet ((fun b : ℝ=>if b≤ U then
    guardWeight r (ClippedResidual.exposure ξ Λ b) else 0) ⁻¹' S)
  exact (Measurable.ite measurableSet_Iic
    (((continuous_guardWeight r).comp (ClippedResidual.continuous_exposure hξ hΛ)).measurable)
    measurable_const) hS

lemma eligibleWeight_bounds (ξ Λ r U : ℝ) (b : Option ℝ) :
    eligibleWeight ξ Λ r U b∈Icc (0:ℝ) 1 := by
  cases b with
  | none=>simp [eligibleWeight]
  | some b=>
    by_cases hb:b≤ U
    · simpa only [eligibleWeight,if_pos hb] using guardWeight_bounds r (ClippedResidual.exposure ξ Λ b)
    · simp only [eligibleWeight,if_neg hb,mem_Icc]
      exact ⟨le_rfl,zero_le_one⟩

def sourceWeights (ξ Λ r U : ℝ) (L : LocalList m) : WeightedSampling.Weights (Fin m) :=
  ⟨fun i=>eligibleWeight ξ Λ r U (L i),fun _=>eligibleWeight_bounds ξ Λ r U _⟩

lemma measurable_sourceWeights (ξ Λ r U : ℝ) (hξ:0<ξ) (hΛ:0<Λ) :
    Measurable (sourceWeights (m:=m) ξ Λ r U) := by
  apply Measurable.subtype_mk
  exact measurable_pi_lambda _ (fun i=>
    (measurable_eligibleWeight ξ Λ r U hξ hΛ).comp (measurable_pi_apply i))

lemma sourceWeights_absent (ξ Λ r U : ℝ) (L : LocalList m) (i : Fin m) (hi:L i=none) :
    (sourceWeights ξ Λ r U L).1 i=0 := by simp [sourceWeights,eligibleWeight,hi]

lemma sourceWeights_outside (ξ Λ r U b : ℝ) (L : LocalList m) (i : Fin m)
    (hi:L i=some b) (hb:U< b) : (sourceWeights ξ Λ r U L).1 i=0 := by
  simp [sourceWeights,eligibleWeight,hi,not_le.mpr hb]

lemma sourceWeights_seed (ξ Λ r U zs b : ℝ) (hr:0< r) (hseed:zs≤Λ)
    (L : LocalList m) (i : Fin m) (hi:L i=some b) (hb:b≤ zs) :
    (sourceWeights ξ Λ r U L).1 i=0 := by
  have he:ClippedResidual.exposure ξ Λ b=0:=ClippedResidual.exposure_zero (hb.trans hseed)
  by_cases hbU:b≤ U
  · simp only [sourceWeights,eligibleWeight,hi,if_pos hbU,he]
    exact guardWeight_zero hr (by positivity)
  · simp [sourceWeights,eligibleWeight,hi,hbU]

variable [Nonempty (Fin m)]

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def planLaw (Δ : ℕ) (α : unitInterval) (w : WeightedSampling.Weights (Fin m)) :
    FiniteLaw (Option (Finset (Fin m))) :=
  FiniteLaw.mixture ((WeightedSampling.pathLaw w Δ ∅).map
      (fun p=>some (WeightedSampling.finalSet Δ ∅ p)))
    (FiniteLaw.dirac none) α.1 α.2.1 α.2.2

lemma planLaw_expect (Δ : ℕ) (α : unitInterval) (w : WeightedSampling.Weights (Fin m))
    (f : Option (Finset (Fin m))→ℝ) :
    (planLaw Δ α w).expect f=α.1*(WeightedSampling.pathLaw w Δ ∅).expect
      (fun p=>f (some (WeightedSampling.finalSet Δ ∅ p)))+(1-α.1)*f none := by
  rw [planLaw,FiniteLaw.expect_mixture,FiniteLaw.expect_map,FiniteLaw.expect_dirac]

lemma measurable_planLaw_mass (Δ : ℕ) (E : Option (Finset (Fin m))) :
    Measurable (fun q : unitInterval×WeightedSampling.Weights (Fin m)=>(planLaw Δ q.1 q.2).mass E) := by
  unfold planLaw FiniteLaw.mixture FiniteLaw.map
  apply Measurable.add
  · apply Measurable.mul (measurable_subtype_coe.comp measurable_fst)
    apply Finset.measurable_sum
    intro p _
    by_cases hp:some (WeightedSampling.finalSet Δ ∅ p)=E
    · simp only [if_pos hp]
      exact (WeightedSampling.measurable_pathLaw_mass Δ ∅ p).comp measurable_snd
    · simp only [if_neg hp]
      exact measurable_const
  · exact (measurable_const.sub (measurable_subtype_coe.comp measurable_fst)).mul measurable_const

private theorem exists_planSampler (Δ : ℕ) :
    ∃f : (unitInterval×WeightedSampling.Weights (Fin m))→ unitInterval→ Option (Finset (Fin m)),
      Measurable (Function.uncurry f) ∧
      (∀q s,0<(planLaw Δ q.1 q.2).mass (f q s)) ∧
      ∀q,volume.map (f q)=FiniteLaw.probabilityMeasure (planLaw Δ q.1 q.2) :=
  Hybrid.exists_support_sampler (fun q : unitInterval×WeightedSampling.Weights (Fin m)=>planLaw Δ q.1 q.2) (measurable_planLaw_mass Δ)

def planSampler (Δ : ℕ) := (exists_planSampler (m:=m) Δ).choose

lemma measurable_planSampler (Δ : ℕ) : Measurable (Function.uncurry (planSampler (m:=m) Δ)) :=
  (exists_planSampler Δ).choose_spec.1

lemma planSampler_support (Δ : ℕ) (q : unitInterval×WeightedSampling.Weights (Fin m))
    (s : unitInterval) : 0<(planLaw Δ q.1 q.2).mass (planSampler Δ q s) :=
  (exists_planSampler Δ).choose_spec.2.1 q s

lemma planSampler_law (Δ : ℕ) (q : unitInterval×WeightedSampling.Weights (Fin m)) :
    volume.map (planSampler Δ q)=FiniteLaw.probabilityMeasure (planLaw Δ q.1 q.2) :=
  (exists_planSampler Δ).choose_spec.2.2 q

lemma planSampler_some_support (Δ : ℕ) (q : unitInterval×WeightedSampling.Weights (Fin m))
    (s : unitInterval) (E : Finset (Fin m)) (hE:planSampler Δ q s=some E) :
    ∃p : WeightedSampling.Path (Fin m) Δ,
      0<(WeightedSampling.pathLaw q.2 Δ ∅).mass p ∧ WeightedSampling.finalSet Δ ∅ p=E := by
  have hp:=planSampler_support Δ q s
  rw [hE] at hp
  simp only [planLaw,FiniteLaw.mixture,FiniteLaw.dirac,Option.some_ne_none,if_false,
    mul_zero,add_zero,FiniteLaw.map] at hp
  by_contra hn
  push Not at hn
  have hsum:(∑p : WeightedSampling.Path (Fin m) Δ,
      if some (WeightedSampling.finalSet Δ ∅ p)=some E then
        (WeightedSampling.pathLaw q.2 Δ ∅).mass p else 0)=0 := by
    apply Finset.sum_eq_zero
    intro p _
    by_cases he:WeightedSampling.finalSet Δ ∅ p=E
    · have hz:(WeightedSampling.pathLaw q.2 Δ ∅).mass p=0 := by
        apply le_antisymm _ ((WeightedSampling.pathLaw q.2 Δ ∅).nonneg p)
        by_contra hh
        exact hn p (lt_of_not_ge hh) he
      simp [he,hz]
    · simp [he]
  have hp0 : (0 : ℝ) < q.1.1 * 0 := by
    convert! hp using 1
    convert! congrArg (fun x : ℝ => q.1.1*x) hsum.symm using 1
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  simp only [mul_zero,lt_self_iff_false] at hp0

theorem planSampler_omits_zero_weight (Δ : ℕ) (q : unitInterval×WeightedSampling.Weights (Fin m))
    (hW:(Δ:ℝ)< WeightedSampling.totalWeight q.2) (s : unitInterval)
    (E : Finset (Fin m)) (hE:planSampler Δ q s=some E)
    (i : Fin m) (hi:q.2.1 i=0) : i∉E := by
  obtain ⟨p,hp,rfl⟩:=planSampler_some_support Δ q s E hE
  have hW':((∅:Finset (Fin m)).card:ℝ)+Δ< WeightedSampling.totalWeight q.2 := by simpa using hW
  intro him
  have hh:=WeightedSampling.finalSet_weight_pos q.2 Δ ∅ hW' (by simp) p hp i him
  rw [hi] at hh
  exact (lt_irrefl 0) hh

def exceptionalSet (U : ℝ) (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i=>L i≠none ∧ U< entryBid (L i))

omit [Nonempty (Fin m)] in
lemma measurable_exceptionalSet (U : ℝ) : Measurable (exceptionalSet (m:=m) U) := by
  apply measurable_to_countable'
  intro S
  have he : exceptionalSet U ⁻¹' {S}=⋂i : Fin m,
      {L : LocalList m | i∈S ↔ L i≠none ∧ U< entryBid (L i)} := by
    ext L
    simp only [mem_preimage,mem_singleton_iff,mem_iInter,mem_setOf_eq]
    exact ⟨fun h i=>by rw [←h];simp [exceptionalSet],
      fun h=>Finset.ext (fun i=>by simpa only [exceptionalSet,Finset.mem_filter,
        Finset.mem_univ,true_and] using (h i).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro i
  have hh:MeasurableSet {L : LocalList m | L i≠none ∧ U< entryBid (L i)} :=
    (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).compl.inter
      (measurableSet_lt measurable_const (measurable_entryBid.comp (measurable_pi_apply i)))
  by_cases hi:i∈S
  · simpa only [hi,true_iff] using hh
  · simpa only [hi,false_iff,Set.compl_setOf] using hh.compl

def sourceSeed (μseed : Measure ℝ) (zs : ℝ) (X : ClassifiedContext m) : Option unitInterval :=
  Hybrid.seedOnList μseed (TaggedLocal.lowList zs zs X.1)

omit [Nonempty (Fin m)] in
lemma measurable_sourceSeed (μseed : Measure ℝ) (zs : ℝ) :
    Measurable (sourceSeed (m:=m) μseed zs) :=
  (Hybrid.measurable_seedOnList μseed).comp
    ((TaggedLocal.measurable_lowList zs zs).comp measurable_fst)

def sampleSeedOption (Δ : ℕ) (q : unitInterval×WeightedSampling.Weights (Fin m)) :
    Option unitInterval→ Option (Finset (Fin m))
  | none=>none
  | some s=>planSampler Δ q s

lemma measurable_sampleSeedOption (Δ : ℕ) :
    Measurable (fun q : (unitInterval×WeightedSampling.Weights (Fin m))×Option unitInterval=>
      sampleSeedOption Δ q.1 q.2) := by
  let zeroSeed : unitInterval:=⟨0,by constructor <;> norm_num⟩
  have hg : Measurable (fun s : Option unitInterval=>s.getD zeroSeed) := by
    intro S hS
    change MeasurableSet S
    exact hS
  have hh : Measurable (fun s : Option unitInterval=>s.isSome) := by
    intro S hS
    change MeasurableSet ((fun _ : unitInterval=>true) ⁻¹' S)
    exact measurable_const hS
  have he : (fun q : (unitInterval×WeightedSampling.Weights (Fin m))×Option unitInterval=>
      sampleSeedOption Δ q.1 q.2)=fun q=>
        if q.2.isSome=true then planSampler Δ q.1 (q.2.getD zeroSeed) else none := by
    funext q
    rcases q with ⟨q,s⟩
    cases s <;> simp [sampleSeedOption]
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun (hh.comp measurable_snd) measurable_const)
    ((measurable_planSampler Δ).comp (measurable_fst.prodMk (hg.comp measurable_snd)))
    measurable_const

def sourcePlan (ξ Λ r U zs : ℝ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m) : Option (Finset (Fin m)) :=
  let Δ:=max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let w:=sourceWeights ξ Λ r U X.1
  if (exceptionalSet U X.1).card≤ 1 ∧ (Δ:ℝ)< WeightedSampling.totalWeight w then
    sampleSeedOption Δ (α X,w) (sourceSeed μseed zs X)
  else none

lemma measurable_sourcePlan (ξ Λ r U zs : ℝ) (hξ:0<ξ) (hΛ:0<Λ)
    (c : ℕ) (μseed : Measure ℝ) (α : ClassifiedContext m→ unitInterval) (hα:Measurable α) :
    Measurable (sourcePlan ξ Λ r U zs c μseed α) := by
  have hΔ : Measurable (fun X : ClassifiedContext m=>
      max (budget c 0 X) (budget c 1 X)-commonBudget c X) :=
    ((measurable_budget c 0).max (measurable_budget c 1)).sub
      ((measurable_budget c 0).min (measurable_budget c 1))
  have hw : Measurable (fun X : ClassifiedContext m => sourceWeights ξ Λ r U X.1) :=
    (measurable_sourceWeights ξ Λ r U hξ hΛ).comp measurable_fst
  have hc : Measurable (fun X : ClassifiedContext m => (exceptionalSet U X.1).card) :=
    (measurable_of_countable Finset.card).comp
    ((measurable_exceptionalSet U).comp measurable_fst)
  have hW : Measurable (fun X : ClassifiedContext m => WeightedSampling.totalWeight (sourceWeights ξ Λ r U X.1)) :=
    WeightedSampling.continuous_totalWeight.measurable.comp hw
  have hΔR : Measurable (fun X : ClassifiedContext m=>
      ((max (budget c 0 X) (budget c 1 X)-commonBudget c X:ℕ):ℝ)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp hΔ
  have hs : Measurable (fun q : ℕ×((unitInterval×WeightedSampling.Weights (Fin m))×Option unitInterval)=>
      sampleSeedOption q.1 q.2.1 q.2.2) :=
    measurable_from_prod_countable_right (fun Δ=>measurable_sampleSeedOption Δ)
  apply Measurable.ite ((measurableSet_le hc measurable_const).inter (measurableSet_lt hΔR hW))
    (hs.comp (hΔ.prodMk ((hα.prodMk hw).prodMk (measurable_sourceSeed (m:=m) μseed zs)))) measurable_const

theorem sourcePlan_omits_outside (ξ Λ r U zs : ℝ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (E : Finset (Fin m)) (hE:sourcePlan ξ Λ r U zs c μseed α X=some E)
    (i : Fin m) (b : ℝ) (hi:X.1 i=some b) (hb:U< b) :
    i∉E ∧ remainder X.1 E i=some b := by
  dsimp only [sourcePlan] at hE
  split_ifs at hE with hg
  · cases hs:sourceSeed μseed zs X with
    | none=>simp [hs,sampleSeedOption] at hE
    | some s=>
      have he:planSampler (max (budget c 0 X) (budget c 1 X)-commonBudget c X)
          (α X,sourceWeights ξ Λ r U X.1) s=some E := by simpa only [hs,sampleSeedOption] using hE
      have hn:=planSampler_omits_zero_weight _ _ hg.2 s E he i
        (sourceWeights_outside ξ Λ r U b X.1 i hi hb)
      exact ⟨hn,by simp only [remainder,if_neg hn,hi]⟩

lemma sourcePlan_multiple_exceptional (ξ Λ r U zs : ℝ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (h:1<(exceptionalSet U X.1).card) : sourcePlan ξ Λ r U zs c μseed α X=none := by
  simp only [sourcePlan,not_le.mpr h,false_and,if_false]

lemma sourcePlan_seedless (ξ Λ r U zs : ℝ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (h:sourceSeed μseed zs X=none) : sourcePlan ξ Λ r U zs c μseed α X=none := by
  dsimp only [sourcePlan]
  split_ifs <;> simp [h,sampleSeedOption]

def sourceContextPolicy (ξ Λ r U zs : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (hΛ:0<Λ)
    (c : ℕ) (μseed : Measure ℝ) (α : ClassifiedContext m→ unitInterval) (hα:Measurable α) :
    ContextPolicy m c unitInterval :=
  completedContextPolicy ξ hξ hξ1 c (sourcePlan ξ Λ r U zs c μseed α)
    (measurable_sourcePlan ξ Λ r U zs hξ hΛ c μseed α hα)
    (fun X=>1<(exceptionalSet U X.1).card)
    (measurableSet_lt measurable_const ((measurable_of_countable Finset.card).comp
      ((measurable_exceptionalSet U).comp measurable_fst)))

end FCAppendix.Affine.Uniform07Finishing.Weighted
