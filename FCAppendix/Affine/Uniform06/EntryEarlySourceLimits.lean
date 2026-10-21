import FCAppendix.Affine.Uniform06.EntryActiveMoments
import FCAppendix.Affine.Uniform06.RawMixedSource
import FCAppendix.Affine.Uniform06.FiniteGuards

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryEarlySourceLimits

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open EntryActiveLimit

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def joint (V B : Ω → ℝ) : Measure (ℝ × ℝ) := μ.map (fun ω => (V ω,B ω))

omit [IsProbabilityMeasure μ] in
theorem joint_first (V B : Ω → ℝ) (hV : Measurable V) (hB : Measurable B) :
    (joint μ V B).map Prod.fst=μ.map V := by
  rw [joint,Measure.map_map measurable_fst (hV.prodMk hB)]
  rfl

omit [IsProbabilityMeasure μ] in
theorem joint_bid_le_value (V B : Ω → ℝ) (hV : Measurable V) (hB : Measurable B)
    (hbid : ∀ᵐ ω ∂μ, B ω ≤ V ω) :
    ∀ᵐ p ∂joint μ V B, p.2 ≤ p.1 :=
  (ae_map_iff (hV.prodMk hB).aemeasurable
    (measurableSet_le measurable_snd measurable_fst)).mpr hbid

omit [IsProbabilityMeasure μ] in
theorem value_support (i : Row) (V : Ω → ℝ) (hV : Measurable V)
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i) :
    ∀ᵐ ω ∂μ, V ω ∈ Icc (0:ℝ) (cutoff i) := by
  apply (ae_map_iff hV.aemeasurable measurableSet_Icc).mp
  rw [hvalue,LowChernoff.conditionalValueLaw]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

omit [IsProbabilityMeasure μ] in

theorem fixed_value_null (i : Row) (V : Ω → ℝ) (hV : Measurable V)
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i) (a : ℝ) :
    ∀ᵐ ω ∂μ, V ω ≠ a := by
  have ha : ∀ᵐ v ∂LowChernoff.conditionalValueLaw i, v ≠ a := by
    rw [LowChernoff.conditionalValueLaw]
    exact Measure.ae_smul_measure (ae_restrict_of_ae (volume.ae_ne a)) _
  apply (ae_map_iff hV.aemeasurable (measurableSet_singleton a).compl).mp
  simpa only [hvalue,Set.mem_compl_iff,Set.mem_singleton_iff] using ha

def entryExposure (i : Row) (V : Ω → ℝ) (ω : Ω) : ℝ :=
  activeExposure (xi i) (entry i) (ActiveGraphComponent.activeBid i) (V ω)

lemma measurable_entryExposure (i : Row) {V : Ω → ℝ} (hV : Measurable V) :
    Measurable (entryExposure i V) := by
  have hB0 : Measurable (ActiveGraphComponent.activeBid i) := by
    unfold ActiveGraphComponent.activeBid
    fun_prop
  exact (measurable_activeExposure (xi_pos i) (EarlyMean.entry_pos i) hB0).comp hV

lemma entryExposure_eq_activeOnly (i : Row) {v : ℝ} (hv : v ∈ Icc (0:ℝ) (cutoff i)) :
    activeExposure (xi i) (entry i) (ActiveGraphComponent.activeBid i) v=EarlyMean.activeOnly i v := by
  by_cases ha : entry i < v
  · have hm : v ∈ Ioc (entry i) (cutoff i) := ⟨ha,hv.2⟩
    simp only [activeExposure,if_pos ha,EarlyMean.activeOnly,indicator_of_mem hm]
    exact EarlyMean.exposure_entry_active i ⟨ha,hv.2⟩
  · have hn : v ∉ Ioc (entry i) (cutoff i) := fun h => ha h.1
    simp only [activeExposure,if_neg ha,EarlyMean.activeOnly,indicator_of_notMem hn]

theorem entryExposure_bounds (i : Row) {v : ℝ} (hv : v ∈ Icc (0:ℝ) (cutoff i)) :
    activeExposure (xi i) (entry i) (ActiveGraphComponent.activeBid i) v ∈ Icc (0:ℝ) (1-x i) := by
  have hx : x i < 1 := by cases i <;> norm_num [x,xQ]
  by_cases ha : entry i < v
  · have hv0 := (EarlyMean.entry_pos i).trans ha
    have he := EarlyMean.exposure_entry_active i ⟨ha,hv.2⟩
    simp only [activeExposure,if_pos ha]
    refine ⟨exposure_nonneg (xi_pos i) (EarlyMean.entry_pos i),?_⟩
    rw [he,activeMarginal]
    have hh := div_le_div_of_nonneg_left (EarlyMean.entry_pos i).le hv0 hv.2
    have ht : entry i/cutoff i=x i := by
      unfold entry
      exact mul_div_cancel_right₀ _ (cutoff_pos i).ne'
    rw [ht] at hh
    linarith
  · simp only [activeExposure,if_neg ha]
    exact ⟨le_rfl,by linarith⟩

omit [IsProbabilityMeasure μ] in
theorem entryExposure_mean (i : Row) (V : Ω → ℝ) (hV : Measurable V)
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i) :
    (∫ ω, entryExposure i V ω ∂μ)=PrefixRoot.requiredDemand i := by
  have he : ∀ᵐ ω ∂μ, entryExposure i V ω=EarlyMean.activeOnly i (V ω) :=
    (value_support μ i V hV hvalue).mono fun _ hv => entryExposure_eq_activeOnly i hv
  rw [integral_congr_ae he,← integral_map hV.aemeasurable
    (EarlyMean.activeOnly_measurable i).aestronglyMeasurable,hvalue,
    LowChernoff.conditionalValueLaw,integral_smul_measure,
    ENNReal.toReal_ofReal (one_div_pos.mpr (cutoff_pos i)).le]
  have hsubset : Ioc (entry i) (cutoff i) ⊆ Icc (0:ℝ) (cutoff i) :=
    fun _ hv => ⟨(EarlyMean.entry_pos i).le.trans hv.1.le,hv.2⟩
  simp only [EarlyMean.activeOnly]
  rw [integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_self_of_subset_left hsubset,
    ← intervalIntegral.integral_of_le (EarlyMean.entry_lt_cutoff i).le]
  have hid := (source_profile_integrals i).2
  simp only [smul_eq_mul]
  unfold PrefixRoot.requiredDemand
  field_simp [(cutoff_pos i).ne']
  linarith

theorem requiredDemand_bounds (i : Row) : PrefixRoot.requiredDemand i ∈ Ioo (0:ℝ) (1/2) := by
  have ht := cutoff_pos i
  have hd : 0 < delta := by norm_num [delta]
  have htd : delta < cutoff i := by
    have hbox := (LowChernoff.sourceTBox_ok i).1
    cases i <;> norm_num [LowChernoff.sourceTBox,delta] at hbox ⊢ <;> linarith
  unfold PrefixRoot.requiredDemand
  constructor
  · exact div_pos (sub_pos.mpr htd) (by positivity)
  · apply (div_lt_iff₀ (show 0 < 2*cutoff i by positivity)).mpr
    linarith

def eligible (i : Row) (V : Ω → ℝ) (ω : Ω) : ℝ :=
  eligibility (PrefixRoot.requiredDemand i) (entryExposure i V ω)

def eligibleMass (i : Row) (V : Ω → ℝ) : ℝ := cutoff i*(∫ ω, eligible i V ω ∂μ)

def eligibleHMass (i : Row) (V : Ω → ℝ) : ℝ :=
  cutoff i*(∫ ω, eligible i V ω*(1/2-entryExposure i V ω) ∂μ)

def eligibleHMean (i : Row) (V : Ω → ℝ) : ℝ := eligibleHMass μ i V/eligibleMass μ i V

theorem eligibleMass_positive (i : Row) (V : Ω → ℝ) (hV : Measurable V)
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i) : 0 < eligibleMass μ i V := by
  have hr := requiredDemand_bounds i
  have hXb : ∀ᵐ ω ∂μ, entryExposure i V ω ∈ Icc (0:ℝ) 1 :=
    Eventually.of_forall fun _ => activeExposure_bounds (xi_pos i) (EarlyMean.entry_pos i) _ _
  have he := eligible_mass_lower μ (measurable_entryExposure i hV) hXb hr.1
    (by linarith [hr.2]) (entryExposure_mean μ i V hV hvalue)
  have hpos : 0 < PrefixRoot.requiredDemand i/(2-PrefixRoot.requiredDemand i) :=
    div_pos hr.1 (by linarith [hr.2])
  exact mul_pos (cutoff_pos i) (hpos.trans_le he)

theorem eligibleHMean_bounds (i : Row) (V : Ω → ℝ) (hV : Measurable V)
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i) :
    eligibleHMean μ i V ∈ Icc (x i-1/2) (1/2) := by
  have hX := measurable_entryExposure i hV
  have hw : Measurable (eligible i V) := (continuous_eligibility _).measurable.comp hX
  have hwI : Integrable (eligible i V) μ := Integrable.of_mem_Icc 0 1 hw.aemeasurable
    (Eventually.of_forall fun _ => eligibility_bounds _ _)
  have hgI : Integrable (fun ω => eligible i V ω*(1/2-entryExposure i V ω)) μ := by
    apply Integrable.of_bound (hw.mul (measurable_const.sub hX)).aestronglyMeasurable (1/2)
    filter_upwards [] with ω
    have hx := activeExposure_bounds (xi_pos i) (EarlyMean.entry_pos i)
      (ActiveGraphComponent.activeBid i) (V ω)
    have hh : |1/2-entryExposure i V ω| ≤ (1/2:ℝ) := by
      rw [abs_le]
      dsimp [entryExposure]
      constructor <;> linarith [hx.1,hx.2]
    dsimp only [Pi.mul_apply,Pi.sub_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0 ≤ eligible i V ω from
      (eligibility_bounds (PrefixRoot.requiredDemand i) (entryExposure i V ω)).1)]
    exact (mul_le_mul_of_nonneg_left hh (eligibility_bounds _ _).1).trans (by
      nlinarith [(eligibility_bounds (PrefixRoot.requiredDemand i) (entryExposure i V ω)).2])
  have hlow := integral_mono_ae (hwI.const_mul (x i-1/2)) hgI (by
    filter_upwards [value_support μ i V hV hvalue] with ω hv
    have hx := entryExposure_bounds i hv
    have hw0 := (eligibility_bounds (PrefixRoot.requiredDemand i) (entryExposure i V ω)).1
    dsimp [entryExposure,eligible] at *
    have hm := mul_le_mul_of_nonneg_left (show x i-1/2 ≤
      1/2-activeExposure (xi i) (entry i) (ActiveGraphComponent.activeBid i) (V ω) by
        linarith [hx.2]) hw0
    nlinarith only [hm])
  have hhigh := integral_mono_ae hgI (hwI.const_mul (1/2)) (by
    filter_upwards [] with ω
    have hx := (activeExposure_bounds (xi_pos i) (EarlyMean.entry_pos i)
      (ActiveGraphComponent.activeBid i) (V ω)).1
    have hw0 := (eligibility_bounds (PrefixRoot.requiredDemand i) (entryExposure i V ω)).1
    dsimp [entryExposure,eligible] at *
    nlinarith)
  rw [integral_const_mul] at hlow hhigh
  have hd := eligibleMass_positive μ i V hV hvalue
  have ht := cutoff_pos i
  constructor
  · apply (le_div_iff₀ hd).mpr
    change (x i-1/2)*(cutoff i*(∫ ω, eligible i V ω ∂μ)) ≤
      cutoff i*(∫ ω, eligible i V ω*(1/2-entryExposure i V ω) ∂μ)
    nlinarith [mul_le_mul_of_nonneg_left hlow ht.le]
  · apply (div_le_iff₀ hd).mpr
    change cutoff i*(∫ ω, eligible i V ω*(1/2-entryExposure i V ω) ∂μ) ≤
      (1/2)*(cutoff i*(∫ ω, eligible i V ω ∂μ))
    nlinarith [mul_le_mul_of_nonneg_left hhigh ht.le]

theorem eligibleHMean_positive (i : Row) (V : Ω → ℝ) (hV : Measurable V)
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i) : 0 < eligibleHMean μ i V := by
  have h := (eligibleHMean_bounds μ i V hV hvalue).1
  have hx : 1/2 < x i := by cases i <;> norm_num [x,xQ]
  linarith

theorem eligibility_eq {ξ l r B : ℝ} (hr : 0 < r) :
    FiniteGuards.eligibility ξ l r B=eligibility r (exposure ξ l B) := by
  have he : (4*exposure ξ l B-r)/r=4*exposure ξ l B/r-1 := by
    field_simp [hr.ne']
  rw [FiniteGuards.eligibility,FiniteGuards.clip01,he,eligibility,max_min_distrib_left]
  norm_num

def clippedH (ξ b B : ℝ) : ℝ := max (1/2-exposure ξ b B) 0

lemma clippedH_bounds {ξ b : ℝ} (hξ : 0 < ξ) (hb : 0 < b) (B : ℝ) :
    clippedH ξ b B ∈ Icc (0:ℝ) (1/2) := by
  refine ⟨le_max_right _ _,max_le ?_ (by norm_num)⟩
  have hp := exposure_nonneg (b := B) hξ hb
  linarith

lemma clippedH_eq {ξ b B : ℝ} (hp : exposure ξ b B ≤ 1/2) :
    clippedH ξ b B=1/2-exposure ξ b B := max_eq_left (sub_nonneg.mpr hp)

theorem source_profile_limits (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hlp : ∀ m, 0 < l m)
    (hb : Tendsto b atTop (𝓝 (entry i))) (hl : Tendsto l atTop (𝓝 (entry i))) :
    Tendsto (fun m => cutoff i*(∫ ω, FiniteGuards.eligibility (xi i) (l m)
      (PrefixRoot.requiredDemand i) (B m ω) ∂μ)) atTop (𝓝 (eligibleMass μ i V)) ∧
    Tendsto (fun m => cutoff i*(∫ ω, FiniteGuards.eligibility (xi i) (l m)
      (PrefixRoot.requiredDemand i) (B m ω)*clippedH (xi i) (b m) (B m ω) ∂μ))
      atTop (𝓝 (eligibleHMass μ i V)) := by
  have hB0 : Measurable (ActiveGraphComponent.activeBid i) := by
    unfold ActiveGraphComponent.activeBid
    fun_prop
  have hne := fixed_value_null μ i V hV hvalue (entry i)
  have hr := (requiredDemand_bounds i).1
  have hweight := (EntryActiveMoments.actual_eligibility_moment_limits μ (r := PrefixRoot.requiredDemand i) V B
    (ActiveGraphComponent.activeBid i) hV hB hB0 (xi_pos i) (EarlyMean.entry_pos i)
    b l hbp hlp hb hl hadmissible hne hactive).1
  have hn := integral_entry_test_tendsto μ V B (ActiveGraphComponent.activeBid i)
    hV hB hB0 (xi_pos i) (EarlyMean.entry_pos i) b l hbp hlp hb hl hadmissible hne hactive
      (fun p => eligibility (PrefixRoot.requiredDemand i) p.2*max (1/2-p.1) 0)
      (by
        exact ((continuous_eligibility _).comp continuous_snd).mul
          ((continuous_const.sub continuous_fst).max continuous_const)) (1/2) (by
        intro x hx y hy
        have hm : max (1/2-x) 0 ∈ Icc (0:ℝ) (1/2) :=
          ⟨le_max_right _ _,max_le (by linarith [hx.1]) (by norm_num)⟩
        rw [abs_of_nonneg (mul_nonneg (eligibility_bounds _ _).1 hm.1)]
        nlinarith [(eligibility_bounds (PrefixRoot.requiredDemand i) y).1,
          (eligibility_bounds (PrefixRoot.requiredDemand i) y).2,hm.1,hm.2])
  have he : (∫ ω, eligibility (PrefixRoot.requiredDemand i) (entryExposure i V ω)*
      max (1/2-entryExposure i V ω) 0 ∂μ)=
      ∫ ω, eligible i V ω*(1/2-entryExposure i V ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [value_support μ i V hV hvalue] with ω hv
    have hx := (entryExposure_bounds i hv).2
    change entryExposure i V ω ≤ 1-x i at hx
    have hs : 1/2 < x i := by cases i <;> norm_num [x,xQ]
    rw [max_eq_left (show 0 ≤ 1/2-entryExposure i V ω by linarith)]
    rfl
  constructor
  · simpa only [eligibility_eq hr,eligibleMass,eligible,entryExposure] using hweight.const_mul (cutoff i)
  · have hn' := hn.const_mul (cutoff i)
    change Tendsto (fun m => cutoff i * (∫ ω, eligibility (PrefixRoot.requiredDemand i)
        (exposure (xi i) (l m) (B m ω))*clippedH (xi i) (b m) (B m ω) ∂μ))
      atTop (𝓝 (cutoff i * (∫ ω, eligibility (PrefixRoot.requiredDemand i) (entryExposure i V ω)*
        max (1/2-entryExposure i V ω) 0 ∂μ))) at hn'
    rw [he] at hn'
    simpa only [eligibility_eq hr,eligibleHMass] using hn'

theorem raw_variance_eq (i : Row) (G : Measure (ℝ × ℝ)) {b : ℝ} (hb : 0 < b) :
    variance (RawMixedSource.demand (xi i) b) (RawMixedSource.source i G)=
      variance Prod.fst (MixedLaw.law i (MixedLaw.physicalLowerLaw i b G)) := by
  have hh := (RawMixedSource.point_preserving i G hb).variance_fun_comp measurable_fst.aemeasurable
  exact hh

theorem raw_variance_lower (i : Row) (V B : Ω → ℝ) (hV : Measurable V)
    (hB : Measurable B) (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ᵐ ω ∂μ, B ω ≤ V ω) {b : ℝ} (hb : 0 < b) (hbt : b ≤ cutoff i) :
    b*((1-cutoff i)/2)^2 ≤ variance (RawMixedSource.demand (xi i) b)
      (RawMixedSource.source i (joint μ V B)) := by
  let G := joint μ V B
  letI : IsProbabilityMeasure G := Measure.isProbabilityMeasure_map (hV.prodMk hB).aemeasurable
  letI := MixedLaw.physicalLowerLaw_probability i hb G
  have hvalueG : G.map Prod.fst=LowChernoff.conditionalValueLaw i := by
    change (joint μ V B).map Prod.fst = _
    rw [joint_first μ V B hV hB,hvalue]
  have hbidG := joint_bid_le_value μ V B hV hB hbid
  have hzero := EarlyMean.original_balanced_zero_mass i hb hbt G hvalueG hbidG
  have hr : 0 ≤ (1-cutoff i)/2 := by linarith [cutoff_lt_one i]
  have hmean : (1-cutoff i)/2 ≤ ∫ p, p.1 ∂MixedLaw.law i (MixedLaw.physicalLowerLaw i b G) := by
    rw [EarlyMean.physical_mean_formula i hb G]
    have hnon : 0 ≤ ∫ p, exposure (xi i) b p.2 ∂G :=
      integral_nonneg fun _ => exposure_nonneg (xi_pos i) hb
    nlinarith [mul_nonneg (cutoff_pos i).le hnon]
  rw [raw_variance_eq i G hb]
  exact (TiltStability.variance_bounds_from_zero_mass _ measurable_fst
    (MixedLaw.demand_bounds i _ (MixedLaw.physicalLowerLaw_bounds i hb G)) hb.le hr hzero hmean).1

def limitingVariance (i : Row) (V : Ω → ℝ) : ℝ :=
  variance Prod.fst (MixedLaw.law i (μ.map (entryExposure i V)))

theorem raw_variance_tendsto (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hb : Tendsto b atTop (𝓝 (entry i))) :
    Tendsto (fun m => variance (RawMixedSource.demand (xi i) (b m))
      (RawMixedSource.source i (joint μ V (B m)))) atTop (𝓝 (limitingVariance μ i V)) := by
  simp_rw [raw_variance_eq i _ (hbp _)]
  exact EntryActiveMoments.actual_entry_variance_tendsto μ i V B hV hB b hbp hb
    hadmissible (fixed_value_null μ i V hV hvalue (entry i)) hactive

theorem limitingVariance_positive (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hbt : ∀ m, b m ≤ cutoff i)
    (hb : Tendsto b atTop (𝓝 (entry i))) : 0 < limitingVariance μ i V := by
  have hv := raw_variance_tendsto μ i V B hV hB hvalue hadmissible hactive b hbp hb
  have hl := le_of_tendsto_of_tendsto (hb.mul_const (((1-cutoff i)/2)^2)) hv
    (Eventually.of_forall fun m => raw_variance_lower μ i V (B m) hV (hB m)
      hvalue (hadmissible m) (hbp m) (hbt m))
  have hp : 0 < (1-cutoff i)/2 := by linarith [cutoff_lt_one i]
  exact (mul_pos (EarlyMean.entry_pos i) (sq_pos_of_pos hp)).trans_le hl

def rawWeight (i : Row) (l : ℝ) : LowBody.RowRival → ℝ :=
  RivalGood.lowerTest (FiniteGuards.eligibility (xi i) l (PrefixRoot.requiredDemand i))

def rawH (i : Row) (b : ℝ) (r : LowBody.RowRival) : ℝ :=
  if r.1=0 then clippedH (xi i) b r.2 else 1/2

lemma measurable_rawWeight (i : Row) (l : ℝ) : Measurable (rawWeight i l) := by
  apply RivalGood.measurable_lowerTest
  unfold FiniteGuards.eligibility FiniteGuards.clip01 exposure
  fun_prop

lemma measurable_rawH (i : Row) (b : ℝ) : Measurable (rawH i b) := by
  unfold rawH
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · unfold clippedH exposure
    fun_prop
  · exact measurable_const

lemma rawWeight_bounds (i : Row) (l : ℝ) (r : LowBody.RowRival) :
    rawWeight i l r ∈ Icc (0:ℝ) 1 := by
  unfold rawWeight RivalGood.lowerTest
  split_ifs
  · exact FiniteGuards.eligibility_bounds _ _ _ _
  · norm_num

lemma rawH_bounds (i : Row) {b : ℝ} (hb : 0 < b) (r : LowBody.RowRival) :
    rawH i b r ∈ Icc (0:ℝ) (1/2) := by
  unfold rawH
  split_ifs
  · exact clippedH_bounds (xi_pos i) hb _
  · norm_num

theorem raw_weightedH_identity (i : Row) (b l : ℝ) (r : LowBody.RowRival) :
    rawWeight i l r*rawH i b r=RivalGood.lowerTest (fun B =>
      FiniteGuards.eligibility (xi i) l (PrefixRoot.requiredDemand i) B*clippedH (xi i) b B) r := by
  unfold rawWeight rawH RivalGood.lowerTest
  split_ifs <;> simp

theorem raw_profile_integrals (i : Row) (V B : Ω → ℝ) (hV : Measurable V)
    (hB : Measurable B) {b : ℝ} (hb : 0 < b) (l : ℝ) :
    (∫ r, rawWeight i l r ∂ RawMixedSource.source i (joint μ V B))=
      cutoff i*(∫ ω, FiniteGuards.eligibility (xi i) l (PrefixRoot.requiredDemand i) (B ω) ∂μ) ∧
    (∫ r, rawWeight i l r*rawH i b r ∂ RawMixedSource.source i (joint μ V B))=
      cutoff i*(∫ ω, FiniteGuards.eligibility (xi i) l (PrefixRoot.requiredDemand i) (B ω)*
        clippedH (xi i) b (B ω) ∂μ) := by
  let G := joint μ V B
  letI : IsProbabilityMeasure G := Measure.isProbabilityMeasure_map (hV.prodMk hB).aemeasurable
  let w := FiniteGuards.eligibility (xi i) l (PrefixRoot.requiredDemand i)
  have hw : Measurable w := by unfold w FiniteGuards.eligibility FiniteGuards.clip01 exposure; fun_prop
  have hhc : Measurable (clippedH (xi i) b) := by unfold clippedH exposure; fun_prop
  have hwi : Integrable (fun p : ℝ × ℝ => w p.2) G :=
    Integrable.of_mem_Icc 0 1 (hw.comp measurable_snd).aemeasurable
      (Eventually.of_forall fun _ => FiniteGuards.eligibility_bounds _ _ _ _)
  have hgi : Integrable (fun p : ℝ × ℝ => w p.2*clippedH (xi i) b p.2) G := by
    apply Integrable.of_mem_Icc 0 (1/2)
      ((hw.comp measurable_snd).mul (hhc.comp measurable_snd)).aemeasurable
    exact Eventually.of_forall fun p => by
      have hwB := FiniteGuards.eligibility_bounds (xi i) l (PrefixRoot.requiredDemand i) p.2
      have hhB := clippedH_bounds (xi_pos i) hb p.2
      change w p.2 ∈ Icc (0:ℝ) 1 at hwB
      exact ⟨mul_nonneg hwB.1 hhB.1,
        (mul_le_mul_of_nonneg_left hhB.2 hwB.1).trans (by nlinarith [hwB.2])⟩
  constructor
  · change (∫ r, RivalGood.lowerTest w r ∂ RawMixedSource.source i G) = _
    rw [RawMixedSource.integral_lower_statistic i G w hw hwi]
    dsimp only [G,joint]
    rw [integral_map (f := fun p : ℝ × ℝ => w p.2)
      (hV.prodMk hB).aemeasurable (hw.comp measurable_snd).aestronglyMeasurable]
  · have hh := RawMixedSource.integral_lower_statistic i G (fun x => w x*clippedH (xi i) b x)
      (hw.mul hhc) hgi
    dsimp only [G,joint] at hh
    rw [integral_map (f := fun p : ℝ × ℝ => w p.2*clippedH (xi i) b p.2)
      (hV.prodMk hB).aemeasurable
      ((hw.mul hhc).comp measurable_snd).aestronglyMeasurable] at hh
    convert! hh using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun r => raw_weightedH_identity i b l r

theorem raw_profile_limits (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hlp : ∀ m, 0 < l m)
    (hb : Tendsto b atTop (𝓝 (entry i))) (hl : Tendsto l atTop (𝓝 (entry i))) :
    Tendsto (fun m => ∫ r, rawWeight i (l m) r ∂ RawMixedSource.source i (joint μ V (B m)))
      atTop (𝓝 (eligibleMass μ i V)) ∧
    Tendsto (fun m => ∫ r, rawWeight i (l m) r*rawH i (b m) r
      ∂ RawMixedSource.source i (joint μ V (B m))) atTop (𝓝 (eligibleHMass μ i V)) := by
  have hs := source_profile_limits μ i V B hV hB hvalue hadmissible hactive b l hbp hlp hb hl
  constructor
  · convert! hs.1 using 1
    funext m
    exact (raw_profile_integrals μ i V (B m) hV (hB m) (hbp m) (l m)).1
  · convert! hs.2 using 1
    funext m
    exact (raw_profile_integrals μ i V (B m) hV (hB m) (hbp m) (l m)).2

end FCAppendix.Affine.Uniform06.EntryEarlySourceLimits
