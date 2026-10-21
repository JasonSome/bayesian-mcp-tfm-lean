import FCAppendix.Affine.Uniform06.ActiveGraphComponent
import FCAppendix.Affine.Uniform06.MixedLaw
import FCAppendix.Affine.Uniform06.SubentryTilt
import FCAppendix.Affine.Uniform06.CapacityFloor
import FCAppendix.Affine.Uniform07.OutcomeIntegrals

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EarlyMean

open MeasureTheory Set Filter ProbabilityTheory
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open ActiveGraphComponent MixedLaw LowChernoff

theorem entry_pos (i : Row) : 0 < entry i :=
  mul_pos (by cases i <;> norm_num [x,xQ]) (cutoff_pos i)

theorem entry_lt_cutoff (i : Row) : entry i < cutoff i := by
  have hx : x i < 1 := by cases i <;> norm_num [x,xQ]
  unfold entry
  nlinarith [cutoff_pos i]

theorem value_support (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=conditionalValueLaw i) :
    ∀ᵐ p ∂G, p.1 ∈ Icc (0:ℝ) (cutoff i) := by
  apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp
  rw [hvalue,conditionalValueLaw]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem conditional_interval_mass (i : Row) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ cutoff i) :
    (conditionalValueLaw i).real (Ioc a b)=(b-a)/cutoff i := by
  rw [conditionalValueLaw,measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal
    (one_div_pos.mpr (cutoff_pos i)).le,measureReal_restrict_apply measurableSet_Ioc]
  have hi : Ioc a b ∩ Icc (0:ℝ) (cutoff i)=Ioc a b :=
    inter_eq_self_of_subset_left (fun _ hv => ⟨ha.trans hv.1.le,hv.2.trans hbt⟩)
  rw [hi,Real.volume_real_Ioc_of_le hab]
  ring

theorem lower_active_mass (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=conditionalValueLaw i) :
    G.real {p | p.1 ∈ Ioc (entry i) (cutoff i)}=1-x i := by
  have hm : G.real {p | p.1 ∈ Ioc (entry i) (cutoff i)}=
      (G.map Prod.fst).real (Ioc (entry i) (cutoff i)) := by
    rw [Measure.real,Measure.real,Measure.map_apply measurable_fst measurableSet_Ioc]
    rfl
  rw [hm,hvalue,conditional_interval_mass i (entry_pos i).le (entry_lt_cutoff i).le le_rfl]
  unfold entry
  field_simp [(cutoff_pos i).ne']

def activeOnly (i : Row) (v : ℝ) : ℝ :=
  (Ioc (entry i) (cutoff i)).indicator (activeMarginal (entry i)) v

theorem activeOnly_measurable (i : Row) : Measurable (activeOnly i) := by
  exact (measurable_const.sub (measurable_const.div measurable_id)).indicator measurableSet_Ioc

theorem exposure_entry_active (i : Row) {v : ℝ}
    (hv : v ∈ Ioc (entry i) (cutoff i)) :
    exposure (xi i) (entry i) (ActiveGraphComponent.activeBid i v)=
      activeMarginal (entry i) v := by
  have hx : x i ∈ Icc (1/2:ℝ) (x i) := by
    constructor
    · cases i <;> norm_num [x,xQ]
    · exact le_rfl
  have h := exposure_active_physical i hx ⟨hv.1.le,hv.2⟩
  have hξ := xi_pos i
  have hx0 : 0 < x i := by cases i <;> norm_num [x,xQ]
  have hk : 1-kappa i=xi i := by
    cases i <;> norm_num [kappa,kappaQ,xi,xiQ]
  change exposure (xi i) (entry i) _ = _ at h
  rw [h]
  unfold activeDemand reciprocalAffine activeMarginal
  rw [mul_div_cancel_left₀ (kappa i) hx0.ne',hk,div_self hξ.ne']
  rfl

theorem original_entry_exposure (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G, p.2 ≤ p.1)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1) :
    ∀ᵐ p ∂G, exposure (xi i) (entry i) p.2=activeOnly i p.1 := by
  filter_upwards [value_support i G hvalue,hbid,hactive] with p hpv hpb hpa
  by_cases hp : p.1 ∈ Ioc (entry i) (cutoff i)
  · rw [hpa hp,exposure_entry_active i hp]
    simp [activeOnly,hp]
  · have hpL : p.1 ≤ entry i := by
      by_contra h
      exact hp ⟨lt_of_not_ge h,hpv.2⟩
    rw [exposure_zero (hpb.trans hpL)]
    simp [activeOnly,hp]

theorem original_entry_mean_lower (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G, p.2 ≤ p.1)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1) :
    (∫ p, exposure (xi i) (entry i) p.2 ∂G)=
      (∫ v in entry i..cutoff i, activeMarginal (entry i) v)/cutoff i := by
  rw [integral_congr_ae (original_entry_exposure i G hvalue hbid hactive)]
  rw [← integral_map measurable_fst.aemeasurable
    (activeOnly_measurable i).aestronglyMeasurable,hvalue,conditionalValueLaw,
    integral_smul_measure,ENNReal.toReal_ofReal (one_div_pos.mpr (cutoff_pos i)).le]
  have hsubset : Ioc (entry i) (cutoff i) ⊆ Icc (0:ℝ) (cutoff i) :=
    fun _ hv => ⟨(entry_pos i).le.trans hv.1.le,hv.2⟩
  simp only [activeOnly]
  rw [integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_self_of_subset_left hsubset,
    intervalIntegral.integral_of_le (entry_lt_cutoff i).le]
  simp only [smul_eq_mul]
  ring

theorem physical_mean_formula (i : Row) {b : ℝ} (hb : 0 < b)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] :
    (∫ p, p.1 ∂MixedLaw.law i (physicalLowerLaw i b G))=
      (1-cutoff i)/2+cutoff i*(∫ p, exposure (xi i) b p.2 ∂G) := by
  letI := physicalLowerLaw_probability i hb G
  rw [integral_law i _ (physicalLowerLaw_bounds i hb G) continuous_fst]
  simp only [smul_eq_mul]
  have he : (∫ x, x ∂physicalLowerLaw i b G) = ∫ p, exposure (xi i) b p.2 ∂G := by
    convert! integral_map (μ := G) (f := fun x : ℝ => x)
      (((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd).aemeasurable)
      (measurable_id.aestronglyMeasurable) using 1
  rw [he]
  norm_num
  ring

theorem original_balanced_mean_at_entry (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G, p.2 ≤ p.1)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1) :
    (∫ p, p.1 ∂MixedLaw.law i (physicalLowerLaw i (entry i) G))=rho := by
  rw [physical_mean_formula i (entry_pos i) G,
    original_entry_mean_lower i G hvalue hbid hactive]
  have hi := (source_profile_integrals i).2
  have ht := cutoff_pos i
  field_simp [ht.ne']
  norm_num only [rho,delta] at *
  nlinarith

theorem active_price_drop (i : Row) {z v : ℝ}
    (hz : z ∈ Icc (1/2:ℝ) (x i))
    (hv : v ∈ Ioc (entry i) (cutoff i)) :
    (entry i-z*cutoff i)/cutoff i ≤
      exposure (xi i) (z*cutoff i) (ActiveGraphComponent.activeBid i v)-
        exposure (xi i) (entry i) (ActiveGraphComponent.activeBid i v) := by
  have ht := cutoff_pos i
  have he := entry_pos i
  have hv0 := he.trans hv.1
  have hx0 : 0 < x i := by cases i <;> norm_num [x,xQ]
  have hk : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hξ := xi_pos i
  have hκξ : kappa i+xi i=1 := by cases i <;> norm_num [kappa,kappaQ,xi,xiQ]
  have hdrop : 0 ≤ entry i-z*cutoff i := by
    unfold entry
    nlinarith [hz.2]
  rw [exposure_active_physical i hz ⟨hv.1.le,hv.2⟩,exposure_entry_active i hv]
  have hid : activeDemand i z v-activeMarginal (entry i) v=
      (entry i-z*cutoff i)*(kappa i/(xi i*entry i)+1/v) := by
    unfold activeDemand reciprocalAffine activeMarginal entry
    rw [show kappa i = 1-xi i by linarith]
    field_simp [hξ.ne',hx0.ne',ht.ne',hv0.ne']
    ring
  rw [hid]
  have hrecip : 1/cutoff i ≤ 1/v := one_div_le_one_div_of_le hv0 hv.2
  have hslope : 1/cutoff i ≤ kappa i/(xi i*entry i)+1/v := by
    have hnon : 0 ≤ kappa i/(xi i*entry i) := by positivity
    linarith
  have hm := mul_le_mul_of_nonneg_left hslope hdrop
  simpa only [div_eq_mul_inv,one_mul] using hm

theorem original_subentry_mean_gap (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G, p.2 ≤ p.1)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1)
    {z : ℝ} (hz : z ∈ Icc (1/2:ℝ) (x i)) :
    rho+(1-x i)*(entry i-z*cutoff i) ≤
      ∫ p, p.1 ∂MixedLaw.law i (physicalLowerLaw i (z*cutoff i) G) := by
  have hb : 0 < z*cutoff i := mul_pos (by linarith [hz.1]) (cutoff_pos i)
  have hlam := entry_pos i
  have hbL : z*cutoff i ≤ entry i := by
    unfold entry
    exact mul_le_mul_of_nonneg_right hz.2 (cutoff_pos i).le
  let E : Set (ℝ × ℝ) := {p | p.1 ∈ Ioc (entry i) (cutoff i)}
  have hE : MeasurableSet E := measurableSet_Ioc.preimage measurable_fst
  have hi (b : ℝ) (hb : 0 < b) :
      Integrable (fun p : ℝ × ℝ => exposure (xi i) b p.2) G :=
    Integrable.of_mem_Icc 0 1
      ((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd).aemeasurable
      (Filter.Eventually.of_forall fun _ =>
        ⟨exposure_nonneg (xi_pos i) hb,exposure_le_one _ _ _⟩)
  have hpt : ∀ᵐ p ∂G,
      E.indicator (fun _ => (entry i-z*cutoff i)/cutoff i) p ≤
        exposure (xi i) (z*cutoff i) p.2-exposure (xi i) (entry i) p.2 := by
    filter_upwards [hactive] with p hp
    by_cases hpE : p ∈ E
    · rw [Set.indicator_of_mem hpE,hp hpE]
      exact active_price_drop i hz hpE
    · rw [Set.indicator_of_notMem hpE]
      exact sub_nonneg.mpr (LowChernoff.exposure_antitone_price
        (xi_pos i) hb hbL)
  have hm := integral_mono_ae ((integrable_const _).indicator hE)
    ((hi _ hb).sub (hi _ hlam)) hpt
  simp only [Pi.sub_apply] at hm
  rw [integral_indicator_const _ hE,
    integral_sub (hi _ hb) (hi _ hlam)] at hm
  have hEm : G.real E=1-x i := lower_active_mass i G hvalue
  rw [hEm] at hm
  have hentry := original_balanced_mean_at_entry i G hvalue hbid hactive
  rw [physical_mean_formula i hlam G] at hentry
  rw [physical_mean_formula i hb G]
  have hs := mul_le_mul_of_nonneg_left hm (cutoff_pos i).le
  simp only [smul_eq_mul] at hs
  have hcancel : cutoff i*((1-x i)*((entry i-z*cutoff i)/cutoff i))=
      (1-x i)*(entry i-z*cutoff i) := by
    field_simp [(cutoff_pos i).ne']
  rw [hcancel] at hs
  nlinarith

theorem original_lower_zero_mass (i : Row) {b : ℝ}
    (hb : 0 < b) (hbt : b ≤ cutoff i)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G, p.2 ≤ p.1) :
    b/cutoff i ≤ (physicalLowerLaw i b G).real {0} := by
  have hE : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Ioc (0:ℝ) b} :=
    measurableSet_Ioc.preimage measurable_fst
  have hX : Measurable (fun p : ℝ × ℝ => exposure (xi i) b p.2) :=
    (continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd
  have hm : G {p | p.1 ∈ Ioc (0:ℝ) b} ≤ G {p | exposure (xi i) b p.2=0} := by
    apply measure_mono_ae
    filter_upwards [hbid] with p hp hpv
    exact exposure_zero (hp.trans hpv.2)
  have hreal := ENNReal.toReal_mono (measure_ne_top G _) hm
  have hlow : G.real {p | p.1 ∈ Ioc (0:ℝ) b}=b/cutoff i := by
    have hmap : G.real {p | p.1 ∈ Ioc (0:ℝ) b}=
        (G.map Prod.fst).real (Ioc (0:ℝ) b) := by
      rw [Measure.real,Measure.real,Measure.map_apply measurable_fst measurableSet_Ioc]
      rfl
    rw [hmap,hvalue,conditional_interval_mass i le_rfl hb.le hbt,sub_zero]
  rw [physicalLowerLaw,Measure.real,Measure.map_apply hX (measurableSet_singleton 0)]
  change b/cutoff i ≤ G.real {p | exposure (xi i) b p.2=0}
  rw [← hlow]
  exact hreal

theorem mixed_zero_mass (i : Row) (μ : Measure ℝ) :
    (MixedLaw.law i μ).real {p : MixedLaw.Pair | p.1=0}=
      cutoff i*μ.real {0} := by
  let E : Set MixedLaw.Pair := {p | p.1=0}
  have hE : MeasurableSet E := measurable_fst (measurableSet_singleton 0)
  have hl : lowerLift μ E=μ {0} := by
    rw [lowerLift,Measure.map_apply (by fun_prop) hE]
    congr 1
  have hu : upperSignLaw E=0 := by
    norm_num [upperSignLaw,Measure.add_apply,Measure.smul_apply,
      Measure.dirac_apply' _ hE,E]
  have he : MixedLaw.law i μ E=ENNReal.ofReal (cutoff i)*μ {0} := by
    rw [MixedLaw.law,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,hu,hl]
    simp
  change (MixedLaw.law i μ E).toReal= _
  rw [he,ENNReal.toReal_mul,ENNReal.toReal_ofReal (cutoff_pos i).le]
  rfl

theorem original_balanced_zero_mass (i : Row) {b : ℝ}
    (hb : 0 < b) (hbt : b ≤ cutoff i)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G, p.2 ≤ p.1) :
    b ≤ (MixedLaw.law i (physicalLowerLaw i b G)).real {p | p.1=0} := by
  rw [mixed_zero_mass]
  have h := mul_le_mul_of_nonneg_left
    (original_lower_zero_mass i hb hbt G hvalue hbid) (cutoff_pos i).le
  have hid : cutoff i*(b/cutoff i)=b := by field_simp [(cutoff_pos i).ne']
  rw [hid] at h
  exact h

theorem exists_matching_tilt_early_law (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G, p.2 ≤ p.1)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1)
    {z r : ℝ} (hz : z ∈ Ico (1/2:ℝ) (x i)) (hr : 0 < r)
    (hrmean : r < rho+(1-x i)*(entry i-z*cutoff i)) :
    ∃ θ ∈ Ioo (0:ℝ) (2/(r*(z*cutoff i))),
      SubentryTilt.mean (MixedLaw.law i (physicalLowerLaw i (z*cutoff i) G))
        Prod.fst θ=r := by
  have hb : 0 < z*cutoff i := mul_pos (by linarith [hz.1]) (cutoff_pos i)
  have hbt : z*cutoff i ≤ cutoff i := by
    have hx : x i ≤ 1 := by cases i <;> norm_num [x,xQ]
    nlinarith [cutoff_pos i,hz.2.le.trans hx]
  letI := physicalLowerLaw_probability i hb G
  have hbounds := demand_bounds i _ (physicalLowerLaw_bounds i hb G)
  exact SubentryTilt.exists_matching_tilt _ measurable_fst hbounds hr hb
    (original_balanced_zero_mass i hb hbt G hvalue hbid)
    (hrmean.trans_le (original_subentry_mean_gap i G hvalue hbid hactive
      ⟨hz.1,hz.2.le⟩))

theorem eventually_matching_tilt_early_law (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G, p.2 ≤ p.1)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1)
    {z : ℝ} (hz : z ∈ Ico (1/2:ℝ) (x i)) :
    ∀ᶠ m in atTop, ∃ θ > (0:ℝ),
      SubentryTilt.mean (MixedLaw.law i (physicalLowerLaw i (z*cutoff i) G))
        Prod.fst θ=(capacity m:ℝ)/((m-1:ℕ):ℝ) := by
  have hx : 0 < 1-x i := by cases i <;> norm_num [x,xQ]
  have hgap : 0 < (1-x i)*(entry i-z*cutoff i) := by
    have hdrop : 0 < entry i-z*cutoff i := by
      unfold entry
      nlinarith [cutoff_pos i,hz.2]
    exact mul_pos hx hdrop
  have hlim := PhysicalRates.rival_capacity_density_tendsto
  have hupper := hlim.eventually_lt_const (show rho < rho+
    (1-x i)*(entry i-z*cutoff i) by linarith)
  have hlower := hlim.eventually_const_lt (show (0:ℝ) < rho by norm_num [rho])
  filter_upwards [hupper,hlower] with m hmlo hmhi
  obtain ⟨θ,hθ,hmatch⟩ := exists_matching_tilt_early_law i G hvalue hbid hactive
    hz hmhi hmlo
  exact ⟨θ,hθ.1,hmatch⟩

end FCAppendix.Affine.Uniform06.EarlyMean
