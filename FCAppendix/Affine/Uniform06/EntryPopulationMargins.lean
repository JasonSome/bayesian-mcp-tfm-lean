import FCAppendix.Affine.Uniform06.EntryEarlySourceLimits
import FCAppendix.Affine.Uniform06.EntryRawTiltedFiber
import FCAppendix.Affine.Uniform06.ActualEntryGoodGeometry
import FCAppendix.Affine.Uniform06.SourcePrefixConstructor
import FCAppendix.Affine.Uniform06.EarlyRankCeiling

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryPopulationMargins

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open LiteralExperiment ActualEntryGoodGeometry EntryEarlySourceLimits
open SourcePrefixConstructor RivalGood

def demandSlack (i : Row) (a U : ℝ) : ℝ :=
  cutoff i*(PrefixRoot.requiredDemand i*a/(xi i*U+a))

def stripMass (i : Row) : ℝ :=
  cutoff i*(PrefixRoot.requiredDemand i/(2-PrefixRoot.requiredDemand i))

def weightMean (i : Row) (G : Measure (ℝ × ℝ)) (L : ℝ) : ℝ :=
  cutoff i*(∫ p, FiniteGuards.eligibility (xi i) L (PrefixRoot.requiredDemand i) p.2 ∂G)

theorem residual_density (i : Row) :
    cutoff i*PrefixRoot.requiredDemand i=rho-(1-cutoff i)/2 := by
  unfold PrefixRoot.requiredDemand rho delta
  field_simp [(cutoff_pos i).ne']
  ring

theorem demandSlack_pos (i : Row) {a U : ℝ} (ha : 0< a) (hU : 0< U) :
    0< demandSlack i a U := by
  have hr := (requiredDemand_bounds i).1
  have ht := cutoff_pos i
  have hξ := xi_pos i
  unfold demandSlack
  positivity

theorem stripMass_pos (i : Row) : 0< stripMass i := by
  have hr := requiredDemand_bounds i
  exact mul_pos (cutoff_pos i) (div_pos hr.1 (by linarith [hr.2]))

lemma integrable_exposure (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {ξ z : ℝ} (hξ : 0<ξ) (hz : 0< z) :
    Integrable (fun p => exposure ξ z p.2) G :=
  Integrable.of_mem_Icc 0 1
    ((continuous_exposure hξ hz).measurable.comp measurable_snd).aemeasurable
    (ae_of_all _ fun _ => ⟨exposure_nonneg hξ hz,exposure_le_one _ _ _⟩)

lemma integrable_weight (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (L : ℝ) : Integrable (fun p => FiniteGuards.eligibility (xi i) L
      (PrefixRoot.requiredDemand i) p.2) G := by
  apply Integrable.of_mem_Icc 0 1
  · unfold FiniteGuards.eligibility FiniteGuards.clip01 exposure
    fun_prop
  · exact ae_of_all _ fun p => FiniteGuards.eligibility_bounds _ _ _ _

theorem integral_exposure_drop (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {ξ U z₁ z₂ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hU : 0< U)
    (hz : 0< z₁) (hguard : (1-ξ)*U≤ z₁) (h12 : z₁≤ z₂)
    (hcap : ∀ᵐ p ∂G,p.2≤ U) :
    (z₂-z₁)/(ξ*U)*(∫ p,exposure ξ z₂ p.2 ∂G) ≤
      (∫ p,exposure ξ z₁ p.2 ∂G)-(∫ p,exposure ξ z₂ p.2 ∂G) := by
  have hI := integrable_exposure G hξ hz
  have hJ := integrable_exposure G hξ (hz.trans_le h12)
  have hh := integral_mono_ae (hJ.const_mul ((z₂-z₁)/(ξ*U))) (hI.sub hJ)
    (hcap.mono fun p hp => exposure_drop hξ hξ1 hU hz hguard h12 hp)
  simpa only [Pi.sub_apply,integral_const_mul,integral_sub hI hJ] using hh

theorem shifted_means (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {L a U : ℝ} (ha : 0< a) (hU : 0< U) (hlo : 0< L-a)
    (hreceipt : (1-xi i)*U≤ L-a) (hcap : ∀ᵐ p ∂G,p.2≤ U)
    (hroot : (∫ p,exposure (xi i) L p.2 ∂G)=PrefixRoot.requiredDemand i) :
    PrefixRoot.requiredDemand i+PrefixRoot.requiredDemand i*a/(xi i*U+a) ≤
      ∫ p,exposure (xi i) (L-a) p.2 ∂G ∧
    (∫ p,exposure (xi i) (L+a) p.2 ∂G) ≤
      PrefixRoot.requiredDemand i-PrefixRoot.requiredDemand i*a/(xi i*U+a) := by
  have hξ := xi_pos i
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hr := (requiredDemand_bounds i).1
  have hL : 0< L := by linarith
  have hbase : 0< xi i*U := mul_pos hξ hU
  have hden : 0< xi i*U+a := by positivity
  have hm := integral_exposure_drop G hξ hξ1 hU hlo hreceipt
    (show L-a≤ L by linarith) hcap
  have hp := integral_exposure_drop G hξ hξ1 hU hL
    (show (1-xi i)*U≤ L by linarith) (show L≤ L+a by linarith) hcap
  rw [hroot] at hm hp
  have hsmall : PrefixRoot.requiredDemand i*a/(xi i*U+a)≤
      a/(xi i*U)*PrefixRoot.requiredDemand i := by
    calc
      _ ≤ PrefixRoot.requiredDemand i*a/(xi i*U) :=
        div_le_div_of_nonneg_left (mul_nonneg hr.le ha.le) hbase (by linarith)
      _ = _ := by ring
  constructor
  · have he : (L-(L-a))/(xi i*U)=a/(xi i*U) := by ring
    rw [he] at hm
    linarith
  · have he : ((L+a)-L)/(xi i*U)=a/(xi i*U) := by ring
    rw [he] at hp
    have hh := (div_le_iff₀ hbase).mp
      (show a*(∫ p,exposure (xi i) (L+a) p.2 ∂G)/(xi i*U)≤
        PrefixRoot.requiredDemand i-(∫ p,exposure (xi i) (L+a) p.2 ∂G) by
        convert! hp using 1
        ring)
    have hgap : PrefixRoot.requiredDemand i*a/(xi i*U+a)≤
        PrefixRoot.requiredDemand i-(∫ p,exposure (xi i) (L+a) p.2 ∂G) := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    linarith

theorem original_weight_lower (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {L : ℝ} (hL : 0< L)
    (hroot : (∫ p,exposure (xi i) L p.2 ∂G)=PrefixRoot.requiredDemand i) :
    stripMass i≤ weightMean i G L := by
  have hr := requiredDemand_bounds i
  have hh := EntryActiveLimit.eligible_mass_lower G
    ((continuous_exposure (xi_pos i) hL).measurable.comp measurable_snd)
    (ae_of_all _ fun _ => ⟨exposure_nonneg (xi_pos i) hL,exposure_le_one _ _ _⟩)
    hr.1 (by linarith [hr.2]) hroot
  have he : (fun p : ℝ×ℝ => FiniteGuards.eligibility (xi i) L
      (PrefixRoot.requiredDemand i) p.2)=
      fun p => EntryActiveLimit.eligibility (PrefixRoot.requiredDemand i) (exposure (xi i) L p.2) := by
    funext p
    exact eligibility_eq hr.1
  unfold stripMass weightMean
  rw [he]
  exact mul_le_mul_of_nonneg_left hh (cutoff_pos i).le

theorem original_strip_lower (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {L a U : ℝ} (hL : 0< L) (ha : 0≤ a)
    (hsmall : 2*a≤ xi i*PrefixRoot.requiredDemand i*L/4)
    (hcap : ∀ᵐ p ∂G,p.2≤ U)
    (hroot : (∫ p,exposure (xi i) L p.2 ∂G)=PrefixRoot.requiredDemand i) :
    stripMass i≤ cutoff i*(∫ p,if p.2∈Icc (L+2*a) U then (1:ℝ) else 0 ∂G) := by
  have hr := (requiredDemand_bounds i).1
  have hI := integrable_weight i G L
  have hJ : Integrable (fun p : ℝ×ℝ => if p.2∈Icc (L+2*a) U then (1:ℝ) else 0) G := by
    apply Integrable.of_mem_Icc 0 1 (Measurable.ite
      (measurableSet_Icc.preimage measurable_snd) measurable_const measurable_const).aemeasurable
    exact ae_of_all _ fun p => by split_ifs <;> norm_num
  have hpoint : ∀ᵐ p ∂G,FiniteGuards.eligibility (xi i) L (PrefixRoot.requiredDemand i) p.2≤
      if p.2∈Icc (L+2*a) U then (1:ℝ) else 0 := by
    filter_upwards [hcap] with p hp
    by_cases hs : p.2∈Icc (L+2*a) U
    · rw [if_pos hs]
      exact (FiniteGuards.eligibility_bounds _ _ _ _).2
    · have hb : p.2≤ L+2*a := by
        by_contra hh
        exact hs ⟨(lt_of_not_ge hh).le,hp⟩
      rw [if_neg hs,GuardPrefix.eligibility_zero_on_small_prefix (xi_pos i) hL hr
        (show 0≤2*a by positivity) hsmall le_rfl p.2 hb]
  exact (original_weight_lower i G hL hroot).trans
    (mul_le_mul_of_nonneg_left (integral_mono_ae hI hJ hpoint) (cutoff_pos i).le)

theorem original_seed_lower (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G,p.2≤ p.1) :
    cutoff i/2≤ cutoff i*(∫ p,if p.2≤ cutoff i/2 then (1:ℝ) else 0 ∂G) := by
  have ht := cutoff_pos i
  let f : ℝ→ℝ := (Iic (cutoff i/2)).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator measurableSet_Iic
  have hIf : Integrable (fun p : ℝ×ℝ => f p.1) G :=
    Integrable.of_mem_Icc 0 1 (hf.comp measurable_fst).aemeasurable
      (ae_of_all _ fun p => by simp only [f,indicator_apply]; split_ifs <;> norm_num)
  have hIg : Integrable (fun p : ℝ×ℝ => if p.2≤ cutoff i/2 then (1:ℝ) else 0) G :=
    Integrable.of_mem_Icc 0 1 (Measurable.ite
      (measurableSet_le measurable_snd measurable_const) measurable_const measurable_const).aemeasurable
      (ae_of_all _ fun p => by split_ifs <;> norm_num)
  have hcmp := integral_mono_ae hIf hIg (hbid.mono fun p hp => by
    by_cases hv : p.1≤ cutoff i/2
    · simp only [f,indicator_apply,mem_Iic,if_pos hv,if_pos (hp.trans hv),le_refl]
    · simp only [f,indicator_apply,mem_Iic,if_neg hv]
      split_ifs <;> norm_num)
  have he : cutoff i*(∫ p,f p.1 ∂G)=cutoff i/2 := by
    rw [← integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,hvalue,
      show f=(Iic (cutoff i/2)).indicator (fun _ => (1:ℝ)) from rfl]
    change cutoff i*(∫ y,(Iic (cutoff i/2)).indicator (1 : ℝ→ℝ) y
      ∂LowChernoff.conditionalValueLaw i)=cutoff i/2
    rw [integral_indicator_one measurableSet_Iic]
    exact EarlyRankCeiling.conditional_value_scaled_cdf i
      ⟨by positivity,by linarith [cutoff_pos i]⟩
  calc
    _ = cutoff i*(∫ p,f p.1 ∂G) := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hcmp (cutoff_pos i).le

theorem original_tags (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] :
    (∫ r,tag 0 r ∂ RawMixedSource.source i G)=cutoff i ∧
    (∫ r,tag 2 r ∂ RawMixedSource.source i G)=(1-cutoff i)/2 ∧
    (∫ r,tag 3 r ∂ RawMixedSource.source i G)=(1-cutoff i)/2 := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have he (j : Fin 4) := EntryRawTiltedFiber.integral_rivalLaw (cutoff i)
    (cutoff_pos i).le (cutoff_lt_one i).le (G.map Prod.snd) (tag j) (measurable_tag j)
    (show Integrable (fun b => tag j ((0:Fin 4),b)) (G.map Prod.snd) by
      by_cases hj : j=0 <;> simp [tag,hj,eq_comm])
  refine ⟨?_,?_,?_⟩
  · simpa only [RawMixedSource.source,tag,show (0:Fin 4)=0 from rfl,if_true,
      show (2:Fin 4)≠0 by decide,show (3:Fin 4)≠0 by decide,if_false,
      integral_const,probReal_univ,one_smul,mul_one,mul_zero,add_zero] using he 0
  · simpa [RawMixedSource.source,tag] using he 2
  · simpa [RawMixedSource.source,tag] using he 3

theorem original_meanMargins (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) (hf : LiteralFields i g) {U : ℝ} (hU : 0< U)
    (hlo : 0< g.multiplier-g.radius)
    (hreceipt : (1-xi i)*U≤ g.multiplier-g.radius)
    (hsmall : 2*g.radius≤ xi i*g.requiredDemand*g.multiplier/4)
    (hcap : ∀ᵐ p ∂G,p.2≤ U)
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G,p.2≤ p.1)
    (hroot : (∫ p,exposure (xi i) g.multiplier p.2 ∂G)=PrefixRoot.requiredDemand i)
    (hpsi : (∫ p,PrefixRoot.sourcePsi i g.rejectionRoot p.2 ∂G)=
      3*PrefixRoot.requiredDemand i) :
    MeanMargins (RawMixedSource.source i G) (xi i) g (g.multiplier+2*g.radius) U
      (cutoff i) ((1-cutoff i)/2) rho (demandSlack i g.radius U)
      (weightMean i G g.multiplier) (cutoff i/2) (stripMass i) := by
  have ht := cutoff_pos i
  have ha : 0< g.radius := by rw [hf.radius_eq]; unfold radius; positivity
  have hL : 0< g.multiplier := by linarith
  have hm := shifted_means i G ha hU hlo hreceipt hcap hroot
  have ht := original_tags i G
  have hd : 0< g.rejectionScale := by rw [hf.scale_eq]; positivity
  have hψM : Measurable (PrefixRoot.psi g.rejectionScale g.rejectionRoot) := by
    unfold PrefixRoot.psi
    fun_prop
  have hψI : Integrable (fun p : ℝ×ℝ => PrefixRoot.psi g.rejectionScale g.rejectionRoot p.2) G :=
    Integrable.of_mem_Icc 0 1 (hψM.comp measurable_snd).aemeasurable
      (ae_of_all _ fun _ => PrefixRoot.psi_bounds hd)
  have hseedM : Measurable (fun b : ℝ => if b≤ g.seedCutoff then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const
  have hseedI : Integrable (fun p : ℝ×ℝ => if p.2≤ g.seedCutoff then (1:ℝ) else 0) G :=
    Integrable.of_mem_Icc 0 1 (hseedM.comp measurable_snd).aemeasurable
      (ae_of_all _ fun p => by split_ifs <;> norm_num)
  have hstripM : Measurable (fun b : ℝ => if b∈Icc (g.multiplier+2*g.radius) U then (1:ℝ) else 0) :=
    Measurable.ite measurableSet_Icc measurable_const measurable_const
  have hstripI : Integrable (fun p : ℝ×ℝ => if p.2∈Icc (g.multiplier+2*g.radius) U then (1:ℝ) else 0) G :=
    Integrable.of_mem_Icc 0 1 (hstripM.comp measurable_snd).aemeasurable
      (ae_of_all _ fun p => by split_ifs <;> norm_num)
  constructor
  · change (∫ r,tag 0 r ∂ RawMixedSource.source i G)=cutoff i
    exact ht.1
  · change (∫ r,tag 2 r ∂ RawMixedSource.source i G)=(1-cutoff i)/2
    exact ht.2.1
  · change (∫ r,tag 3 r ∂ RawMixedSource.source i G)=(1-cutoff i)/2
    exact ht.2.2
  · change rho-(1-cutoff i)/2+demandSlack i g.radius U≤
      ∫ r,lowerTest (exposure (xi i) (g.multiplier-g.radius)) r ∂ RawMixedSource.source i G
    rw [RawMixedSource.integral_lower_statistic i G _
      (continuous_exposure (xi_pos i) hlo).measurable (integrable_exposure G (xi_pos i) hlo),
      ← residual_density i]
    simpa only [demandSlack,mul_add] using mul_le_mul_of_nonneg_left hm.1 (cutoff_pos i).le
  · change (∫ r,lowerTest (exposure (xi i) (g.multiplier+g.radius)) r ∂ RawMixedSource.source i G)≤ _
    have hhi : 0< g.multiplier+g.radius := by positivity
    rw [RawMixedSource.integral_lower_statistic i G _
      (continuous_exposure (xi_pos i) hhi).measurable (integrable_exposure G (xi_pos i) hhi),
      ← residual_density i]
    simpa only [demandSlack,mul_sub] using mul_le_mul_of_nonneg_left hm.2 (cutoff_pos i).le
  · change weightMean i G g.multiplier≤∫ r,lowerTest
      (FiniteGuards.eligibility (xi i) g.multiplier g.requiredDemand) r ∂ RawMixedSource.source i G
    rw [hf.demand_eq,RawMixedSource.integral_lower_statistic i G _ (by
      unfold FiniteGuards.eligibility FiniteGuards.clip01 exposure; fun_prop)
      (integrable_weight i G g.multiplier)]
    exact le_rfl
  · change 3*(rho-(1-cutoff i)/2)≤∫ r,
      lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) r ∂ RawMixedSource.source i G
    rw [RawMixedSource.integral_lower_statistic i G _ hψM hψI,hf.scale_eq]
    change 3*(rho-(1-cutoff i)/2)≤ cutoff i*(∫ p,PrefixRoot.sourcePsi i g.rejectionRoot p.2 ∂G)
    rw [hpsi,← residual_density i]
    ring_nf
    exact le_rfl
  · change cutoff i/2≤∫ r,lowerTest (fun b => if b≤ g.seedCutoff then (1:ℝ) else 0) r ∂ RawMixedSource.source i G
    rw [RawMixedSource.integral_lower_statistic i G _ hseedM hseedI,hf.seed_eq]
    exact original_seed_lower i G hvalue hbid
  · change stripMass i≤∫ r,lowerTest (fun b => if b∈Icc (g.multiplier+2*g.radius) U then (1:ℝ) else 0) r ∂ RawMixedSource.source i G
    rw [RawMixedSource.integral_lower_statistic i G _ hstripM hstripI]
    exact original_strip_lower i G hL ha.le (by simpa only [hf.demand_eq] using hsmall) hcap hroot

end FCAppendix.Affine.Uniform06.EntryPopulationMargins
