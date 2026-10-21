import FCAppendix.Affine.Uniform07Finishing.Early.NativeRadius
import FCAppendix.Affine.Uniform07Finishing.Native.SourcePlan
import FCAppendix.Affine.Uniform07Finishing.Early.PrimitiveGuards

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open StrictNative
open scoped BigOperators
variable {m : ℕ}

def sourceRamp (margin x : ℝ) : ℝ := min 1 (max 0 ((x-margin)/margin))

lemma sourceRamp_bounds (margin x : ℝ) : sourceRamp margin x∈Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩

lemma continuous_sourceRamp (margin : ℝ) : Continuous (sourceRamp margin) := by
  unfold sourceRamp
  fun_prop

lemma sourceRamp_positive {margin x : ℝ} (hm:0< margin) (hx:0< sourceRamp margin x) : margin< x := by
  by_contra hn
  have hq:(x-margin)/margin≤ 0:=div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (le_of_not_gt hn)) hm.le
  simp only [sourceRamp,max_eq_left hq,min_eq_right zero_le_one] at hx
  exact (lt_irrefl 0) hx

lemma sourceRamp_one {margin x : ℝ} (hm:0< margin) (hx:2*margin≤ x) : sourceRamp margin x=1 := by
  have hq:1≤(x-margin)/margin:=(le_div_iff₀ hm).mpr (by linarith)
  exact min_eq_left (hq.trans (le_max_right _ _))

lemma monotone_sourceRamp {margin : ℝ} (hm:0< margin) : Monotone (sourceRamp margin) := by
  intro x y hxy
  exact min_le_min le_rfl (max_le_max le_rfl
    (div_le_div_of_nonneg_right (sub_le_sub_right hxy margin) hm.le))

def sourceDemand (ξ z : ℝ) (L : LocalList m) : ℝ :=
  ∑k,ClippedResidual.exposure ξ z (entryBid (L k))

lemma measurable_sourceDemand {ξ z : ℝ} (hξ:0<ξ) (hz:0< z) :
    Measurable (sourceDemand (m:=m) ξ z) := by
  apply Finset.measurable_sum
  intro k _
  exact (ClippedResidual.continuous_exposure hξ hz).measurable.comp
    (measurable_entryBid.comp (measurable_pi_apply k))

def sourcePsi (d₀ z b : ℝ) : ℝ := max 0 (b-z)/(d₀+max 0 (b-z))

def sourceRejectionDemand (d₀ z : ℝ) (L : LocalList m) : ℝ := ∑k,sourcePsi d₀ z (entryBid (L k))

lemma continuous_sourcePsi {d₀ : ℝ} (hd:0< d₀) (z : ℝ) : Continuous (sourcePsi d₀ z) := by
  unfold sourcePsi
  apply (continuous_const.max (continuous_id.sub continuous_const)).div
    (continuous_const.add (continuous_const.max (continuous_id.sub continuous_const)))
  intro b
  exact ne_of_gt (hd.trans_le (le_add_of_nonneg_right (le_max_left _ _)))

lemma measurable_sourceRejectionDemand {d₀ : ℝ} (hd:0< d₀) (z : ℝ) :
    Measurable (sourceRejectionDemand (m:=m) d₀ z) := by
  apply Finset.measurable_sum
  intro k _
  exact (continuous_sourcePsi hd z).measurable.comp
    (measurable_entryBid.comp (measurable_pi_apply k))

def sourceCountMargin (t width : ℝ) (X : ClassifiedContext m) : ℝ :=
  width*m-max (abs (((presentSet X.1).card:ℝ)-t*m))
    (max (abs ((X.2.1:ℝ)-(1-t)*m/2)) (abs ((X.2.2:ℝ)-(1-t)*m/2)))

def sourceCountSlacks (t width : ℝ) (X : ClassifiedContext m) : Fin 3 → ℝ :=
  ![width*m-abs (((presentSet X.1).card:ℝ)-t*m),
    width*m-abs ((X.2.1:ℝ)-(1-t)*m/2),
    width*m-abs ((X.2.2:ℝ)-(1-t)*m/2)]

lemma sourceCountMargin_le (t width : ℝ) (X : ClassifiedContext m) (k : Fin 3) :
    sourceCountMargin t width X ≤ sourceCountSlacks t width X k := by
  fin_cases k
  · exact sub_le_sub_left (le_max_left _ _) _
  · exact sub_le_sub_left ((le_max_left _ _).trans (le_max_right _ _)) _
  · exact sub_le_sub_left ((le_max_right _ _).trans (le_max_right _ _)) _

lemma lt_sourceCountMargin_iff (t width z : ℝ) (X : ClassifiedContext m) :
    z < sourceCountMargin t width X ↔ ∀ k : Fin 3, z < sourceCountSlacks t width X k := by
  constructor
  · intro h k
    exact h.trans_le (sourceCountMargin_le t width X k)
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    change z < width*m-abs (((presentSet X.1).card:ℝ)-t*m) at h0
    change z < width*m-abs ((X.2.1:ℝ)-(1-t)*m/2) at h1
    change z < width*m-abs ((X.2.2:ℝ)-(1-t)*m/2) at h2
    unfold sourceCountMargin
    have hm : max (abs (((presentSet X.1).card:ℝ)-t*m))
        (max (abs ((X.2.1:ℝ)-(1-t)*m/2)) (abs ((X.2.2:ℝ)-(1-t)*m/2))) < width*m-z :=
      max_lt (by linarith) (max_lt (by linarith) (by linarith))
    linarith

lemma measurable_sourceCountMargin (t width : ℝ) :
    Measurable (sourceCountMargin (m:=m) t width) := by
  have hn:Measurable (fun X : ClassifiedContext m=>((presentSet X.1).card:ℝ)) :=
    (measurable_of_countable (fun s : Finset (Fin m)=>(s.card:ℝ))).comp
      (measurable_presentSet.comp measurable_fst)
  have h0:Measurable (fun X : ClassifiedContext m=>(X.2.1:ℝ)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp measurable_snd.fst
  have h1:Measurable (fun X : ClassifiedContext m=>(X.2.2:ℝ)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp measurable_snd.snd
  exact measurable_const.sub ((hn.sub measurable_const).abs.max
    ((h0.sub measurable_const).abs.max (h1.sub measurable_const).abs))

lemma measurable_sourceCountSlacks (t width : ℝ) (k : Fin 3) :
    Measurable (fun X : ClassifiedContext m => sourceCountSlacks t width X k) := by
  have hn : Measurable (fun X : ClassifiedContext m => ((presentSet X.1).card:ℝ)) :=
    (measurable_of_countable (fun s : Finset (Fin m) => (s.card:ℝ))).comp
      (measurable_presentSet.comp measurable_fst)
  have h0 : Measurable (fun X : ClassifiedContext m => (X.2.1:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp measurable_snd.fst
  have h1 : Measurable (fun X : ClassifiedContext m => (X.2.2:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp measurable_snd.snd
  fin_cases k
  · exact measurable_const.sub (hn.sub measurable_const).abs
  · exact measurable_const.sub (h0.sub measurable_const).abs
  · exact measurable_const.sub (h1.sub measurable_const).abs

def sourceSlacks (ξ Λ a r U d₀ z t width : ℝ) (c : ℕ)
    (X : ClassifiedContext m) : Fin 5→ℝ :=
  let d:=commonBudget c X
  let Δ:=max (budget c 0 X) (budget c 1 X)-d
  ![sourceDemand ξ (Λ-a) X.1-d-Δ,
    (d:ℝ)-sourceDemand ξ (Λ+a) X.1,
    WeightedSampling.totalWeight (sourceWeights ξ Λ r U X.1)-Δ,
    sourceRejectionDemand d₀ z X.1-budget c 0 X-budget c 1 X,
    sourceCountMargin t width X]

lemma measurable_sourceSlacks {ξ Λ a d₀ : ℝ} (hξ:0<ξ) (ha:0< a)
    (hlo:0<Λ-a) (hd:0< d₀) (r U z t width : ℝ) (c : ℕ) (k : Fin 5) :
    Measurable (fun X : ClassifiedContext m=>sourceSlacks ξ Λ a r U d₀ z t width c X k) := by
  have hΛ:0<Λ:=by linarith
  have hhi:0<Λ+a:=by linarith
  have hc0:Measurable (fun X : ClassifiedContext m=>(budget c 0 X:ℝ)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp (measurable_budget c 0)
  have hc1:Measurable (fun X : ClassifiedContext m=>(budget c 1 X:ℝ)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp (measurable_budget c 1)
  have hdm:Measurable (commonBudget (m:=m) c):=(measurable_budget c 0).min (measurable_budget c 1)
  have hdR:Measurable (fun X : ClassifiedContext m=>(commonBudget c X:ℝ)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp hdm
  have hΔ:Measurable (fun X : ClassifiedContext m=>
      ((max (budget c 0 X) (budget c 1 X)-commonBudget c X:ℕ):ℝ)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp
      (((measurable_budget c 0).max (measurable_budget c 1)).sub hdm)
  fin_cases k
  · exact (((measurable_sourceDemand hξ hlo).comp measurable_fst).sub hdR).sub hΔ
  · exact hdR.sub ((measurable_sourceDemand hξ hhi).comp measurable_fst)
  · exact (WeightedSampling.continuous_totalWeight.measurable.comp
      ((measurable_sourceWeights ξ Λ r U hξ hΛ).comp measurable_fst)).sub hΔ
  · exact (((measurable_sourceRejectionDemand hd z).comp measurable_fst).sub hc0).sub hc1
  · exact measurable_sourceCountMargin t width

def sourcePolicySlacks (ξ Λ a r U d₀ z t width : ℝ) (c : ℕ)
    (X : ClassifiedContext m) : Fin 7 → ℝ :=
  let s := sourceSlacks ξ Λ a r U d₀ z t width c X
  let q := sourceCountSlacks t width X
  ![s 0,s 1,s 2,s 3,q 0,q 1,q 2]

lemma measurable_sourcePolicySlacks {ξ Λ a d₀ : ℝ} (hξ : 0<ξ) (ha : 0< a)
    (hlo : 0<Λ-a) (hd : 0< d₀) (r U z t width : ℝ) (c : ℕ) (k : Fin 7) :
    Measurable (fun X : ClassifiedContext m =>
      sourcePolicySlacks ξ Λ a r U d₀ z t width c X k) := by
  fin_cases k
  · exact measurable_sourceSlacks hξ ha hlo hd r U z t width c 0
  · exact measurable_sourceSlacks hξ ha hlo hd r U z t width c 1
  · exact measurable_sourceSlacks hξ ha hlo hd r U z t width c 2
  · exact measurable_sourceSlacks hξ ha hlo hd r U z t width c 3
  · exact measurable_sourceCountSlacks t width 0
  · exact measurable_sourceCountSlacks t width 1
  · exact measurable_sourceCountSlacks t width 2

def sourceGuardAlpha (ξ Λ a r U d₀ z t width ε : ℝ) (c : ℕ)
    (X : ClassifiedContext m) : unitInterval :=
  ⟨∏k:Fin 7,sourceRamp (ε*m) (sourcePolicySlacks ξ Λ a r U d₀ z t width c X k),
    Finset.prod_nonneg (fun _ _=>(sourceRamp_bounds _ _).1),
    Finset.prod_le_one (fun _ _=>(sourceRamp_bounds _ _).1)
      (fun _ _=>(sourceRamp_bounds _ _).2)⟩

lemma measurable_sourceGuardAlpha {ξ Λ a d₀ : ℝ} (hξ:0<ξ) (ha:0< a)
    (hlo:0<Λ-a) (hd:0< d₀) (r U z t width ε : ℝ) (c : ℕ) :
    Measurable (sourceGuardAlpha (m:=m) ξ Λ a r U d₀ z t width ε c) := by
  apply Measurable.subtype_mk
  exact Finset.measurable_prod _ (fun k _=>
    (continuous_sourceRamp (ε*m)).measurable.comp
      (measurable_sourcePolicySlacks hξ ha hlo hd r U z t width c k))

lemma sourceGuardAlpha_policy_outer {ξ Λ a r U d₀ z t width ε : ℝ} (c : ℕ)
    (hm : 0< m) (hε : 0<ε) (X : ClassifiedContext m)
    (hα : 0<(sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X:ℝ)) :
    ∀ k : Fin 7, ε*m< sourcePolicySlacks ξ Λ a r U d₀ z t width c X k := by
  intro k
  apply sourceRamp_positive (mul_pos hε (by exact_mod_cast hm))
  by_contra hn
  have hz : sourceRamp (ε*m) (sourcePolicySlacks ξ Λ a r U d₀ z t width c X k)=0 :=
    le_antisymm (le_of_not_gt hn) (sourceRamp_bounds _ _).1
  have hprod : (∏j:Fin 7,sourceRamp (ε*m)
      (sourcePolicySlacks ξ Λ a r U d₀ z t width c X j))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) hz
  change 0<(∏j:Fin 7,sourceRamp (ε*m)
    (sourcePolicySlacks ξ Λ a r U d₀ z t width c X j)) at hα
  rw [hprod] at hα
  exact (lt_irrefl 0) hα

lemma sourceGuardAlpha_outer {ξ Λ a r U d₀ z t width ε : ℝ} (c : ℕ)
    (hm:0< m) (hε:0<ε) (X : ClassifiedContext m)
    (hα:0<(sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X:ℝ)) :
    ∀k:Fin 5,ε*m< sourceSlacks ξ Λ a r U d₀ z t width c X k := by
  intro k
  have h := sourceGuardAlpha_policy_outer c hm hε X hα
  fin_cases k
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · apply (lt_sourceCountMargin_iff t width (ε*m) X).mpr
    intro j
    fin_cases j
    · exact h 4
    · exact h 5
    · exact h 6

lemma sourceGuardAlpha_inner {ξ Λ a r U d₀ z t width ε : ℝ} (c : ℕ)
    (hm:0< m) (hε:0<ε) (X : ClassifiedContext m)
    (hinner:∀k:Fin 5,2*(ε*m)≤ sourceSlacks ξ Λ a r U d₀ z t width c X k) :
    sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X=1 := by
  apply Subtype.ext
  change (∏k:Fin 7,sourceRamp (ε*m) (sourcePolicySlacks ξ Λ a r U d₀ z t width c X k))=1
  apply Finset.prod_eq_one
  intro k _
  apply sourceRamp_one (mul_pos hε (by exact_mod_cast hm))
  fin_cases k
  · exact hinner 0
  · exact hinner 1
  · exact hinner 2
  · exact hinner 3
  · exact (hinner 4).trans (sourceCountMargin_le t width X 0)
  · exact (hinner 4).trans (sourceCountMargin_le t width X 1)
  · exact (hinner 4).trans (sourceCountMargin_le t width X 2)

lemma source_weight_positive_margin (i : Uniform07.Row) {Λ b : ℝ}
    (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ)
    (hp:0< guardWeight (Early.demandRatio i)
      (ClippedResidual.exposure (Uniform07.xi i) Λ b)) :
    Λ+3*Early.nativeRadius i< b := by
  have hr:=Early.demandRatio_pos i
  have hξ:=Uniform07.xi_pos i
  have hΛ0:0<Λ:=lt_trans
    (mul_pos (by norm_num : (0:ℝ)<54/100) (Uniform07.cutoff_pos i)) hΛ
  have hp':Early.demandRatio i/4< ClippedResidual.exposure (Uniform07.xi i) Λ b :=
    guardWeight_positive hr hp
  have hb:Λ< b := by
    by_contra hn
    rw [ClippedResidual.exposure_zero (le_of_not_gt hn)] at hp'
    linarith
  have hb0:0< b:=hΛ0.trans hb
  have hf:(b-Λ)/(Uniform07.xi i*b)=(1-Λ/b)/Uniform07.xi i := by
    field_simp [hξ.ne',hb0.ne']
  have hraw:0≤(1-Λ/b)/Uniform07.xi i := by
    rw [←hf]
    exact div_nonneg (sub_pos.mpr hb).le (mul_pos hξ hb0).le
  have he:ClippedResidual.exposure (Uniform07.xi i) Λ b=
      Early.clip01 ((1-Λ/b)/Uniform07.xi i) := by
    rw [ClippedResidual.exposure,max_eq_left hb.le,max_eq_right (sub_pos.mpr hb).le,hf]
    exact (max_eq_right (le_min zero_le_one hraw)).symm
  apply ((Early.native_sampling_margin_guards i).2 Λ hΛ).2 b hb0
  rwa [←he]

variable [Nonempty (Fin m)]

theorem sourcePlan_exclusive_margin (i : Uniform07.Row) {Λ : ℝ}
    (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (E : Finset (Fin m))
    (hE:sourcePlan (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i)
      (Uniform07.cutoff i/2) c μseed α X=some E) :
    E.card=max (budget c 0 X) (budget c 1 X)-commonBudget c X ∧
    ∀k∈E,Λ+3*Early.nativeRadius i< entryBid (X.1 k) := by
  dsimp only [sourcePlan] at hE
  split_ifs at hE with hg
  · cases hs:sourceSeed μseed (Uniform07.cutoff i/2) X with
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

lemma planSampler_some_alpha_pos (Δ : ℕ)
    (q : unitInterval×WeightedSampling.Weights (Fin m)) (s : unitInterval)
    (E : Finset (Fin m)) (hE:planSampler Δ q s=some E) : 0<(q.1:ℝ) := by
  have hp:=planSampler_support Δ q s
  rw [hE] at hp
  by_contra hn
  have hz:(q.1:ℝ)=0:=le_antisymm (le_of_not_gt hn) q.1.2.1
  simp only [planLaw,FiniteLaw.mixture,hz,zero_mul,zero_add,FiniteLaw.dirac,
    Option.some_ne_none,if_false,mul_zero] at hp
  exact (lt_irrefl 0) hp

lemma sourcePlan_some_alpha_pos (ξ Λ r U zs : ℝ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m→ unitInterval) (X : ClassifiedContext m)
    (E : Finset (Fin m)) (hE:sourcePlan ξ Λ r U zs c μseed α X=some E) : 0<(α X:ℝ) := by
  dsimp only [sourcePlan] at hE
  split_ifs at hE with hg
  · cases hs:sourceSeed μseed zs X with
    | none=>simp [hs,sampleSeedOption] at hE
    | some s=>
      have he:planSampler (max (budget c 0 X) (budget c 1 X)-commonBudget c X)
          (α X,sourceWeights ξ Λ r U X.1) s=some E := by
        simpa only [hs,sampleSeedOption] using hE
      exact planSampler_some_alpha_pos _ _ s E he

theorem sourcePlan_U4_valid (i : Uniform07.Row) {Λ R slack : ℝ}
    (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ)
    (hR:0< R) (hroot:Uniform07.kappa i*R<Λ-Early.nativeRadius i)
    (c : ℕ) (μseed : Measure ℝ) (α : ClassifiedContext m→ unitInterval)
    (X : ClassifiedContext m) (hX:NonnegativeList X.1)
    (hbid:∀k,entryBid (X.1 k)≤ R) (hslack:0< slack)
    (hlo:((commonBudget c X:ℕ):ℝ)+
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X:ℕ)+slack<
        sourceDemand (Uniform07.xi i) (Λ-Early.nativeRadius i) X.1)
    (hhi:sourceDemand (Uniform07.xi i) (Λ+Early.nativeRadius i) X.1<
      (commonBudget c X:ℝ)-slack)
    (E : Finset (Fin m))
    (hE:sourcePlan (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i)
      (Uniform07.cutoff i/2) c μseed α X=some E) :
    ValidExclusive (Uniform07.xi i) X.1 (budget c 0 X) (budget c 1 X) E := by
  have ha:0< Early.nativeRadius i:=(Early.native_sampling_margin_guards i).1
  have hκ:Uniform07.kappa i=1-Uniform07.xi i := by
    cases i <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xi,Uniform07.xiQ]
  have hξ1:Uniform07.xi i<1:=by
    cases i <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  have hlo0:0<Λ-Early.nativeRadius i :=
    lt_trans (mul_pos (by rw [hκ];linarith) hR) hroot
  have hdn:0< commonBudget c X := by
    have hh:0≤ sourceDemand (Uniform07.xi i) (Λ+Early.nativeRadius i) X.1 :=
      Finset.sum_nonneg (fun k _=>ClippedResidual.exposure_nonneg (Uniform07.xi_pos i) (by linarith))
    have hdR:(0:ℝ)< commonBudget c X:=by linarith
    exact_mod_cast hdR
  obtain ⟨hcE,hmarg⟩:=sourcePlan_exclusive_margin i hΛ c μseed α X E hE
  have hl:((commonBudget c X:ℕ):ℝ)+(E.card:ℝ)+slack<
      ∑k,ClippedResidual.exposure (Uniform07.xi i) (Λ-Early.nativeRadius i) (entryBid (X.1 k)) := by
    rw [hcE]
    exact hlo
  exact (source_U4_passes_native_test X.1 hX (budget c 0 X) (budget c 1 X) E
    (Uniform07.xi_pos i) hξ1 hR hlo0 (by linarith) (by rwa [←hκ]) hbid hdn hslack
    hcE hl hhi (fun k hk=>(by linarith [hmarg k hk]))).1

theorem literal_sourcePlan_valid (i : Uniform07.Row) {Λ R z width ε : ℝ}
    (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ) (hR:0< R)
    (hroot:Uniform07.kappa i*R<Λ-Early.nativeRadius i)
    (hm:0< m) (hε:0<ε) (c : ℕ) (μseed : Measure ℝ)
    (X : ClassifiedContext m) (hX:NonnegativeList X.1)
    (hbid:∀k,entryBid (X.1 k)≤ R) (E : Finset (Fin m))
    (hE:sourcePlan (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i)
      (Uniform07.cutoff i/2) c μseed
      (sourceGuardAlpha (Uniform07.xi i) Λ (Early.nativeRadius i) (Early.demandRatio i)
        (Early.bidCap i) (Uniform07.cutoff i/1000) z (Uniform07.cutoff i) width ε c) X=some E) :
    ValidExclusive (Uniform07.xi i) X.1 (budget c 0 X) (budget c 1 X) E := by
  let α : ClassifiedContext m → unitInterval := sourceGuardAlpha (Uniform07.xi i) Λ (Early.nativeRadius i) (Early.demandRatio i)
    (Early.bidCap i) (Uniform07.cutoff i/1000) z (Uniform07.cutoff i) width ε c
  have hα:0<(α X:ℝ):=sourcePlan_some_alpha_pos _ _ _ _ _ c μseed α X E hE
  have hg:=sourceGuardAlpha_outer c hm hε X hα
  have hlo:=hg 0
  have hhi:=hg 1
  simp only [sourceSlacks,Matrix.cons_val_zero,Matrix.cons_val_one] at hlo hhi
  apply sourcePlan_U4_valid i hΛ hR hroot c μseed α X hX hbid
    (mul_pos hε (show (0:ℝ)<(m:ℝ) by exact_mod_cast hm)) _ _ E hE
  · linarith
  · linarith

end FCAppendix.Affine.Uniform07Finishing.Weighted
