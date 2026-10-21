import FCAppendix.Affine.Uniform06.EarlyMean
import FCAppendix.Affine.Uniform06.TiltStability

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FiniteMean

open MeasureTheory Set Filter ProbabilityTheory
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open LowChernoff ActiveGraphComponent MixedLaw EarlyMean

theorem exposure_ordered_lipschitz {ξ z a b : ℝ}
    (hξ : 0 < ξ) (hz : 0 < z) (hab : a ≤ b) :
    exposure ξ z b-exposure ξ z a ≤ (b-a)/(ξ*z) := by
  by_cases hb : b ≤ z
  · rw [exposure_zero hb,exposure_zero (hab.trans hb),sub_self]
    exact div_nonneg (sub_nonneg.mpr hab) (mul_pos hξ hz).le
  have hzb : z < b := lt_of_not_ge hb
  have hb0 := hz.trans hzb
  have hbform : exposure ξ z b=min 1 ((b-z)/(ξ*b)) := by
    unfold exposure
    rw [max_eq_left hzb.le,max_eq_right (sub_nonneg.mpr hzb.le)]
  by_cases ha : a ≤ z
  · rw [exposure_zero ha,sub_zero,hbform]
    calc
      _ ≤ (b-z)/(ξ*b) := min_le_right _ _
      _ ≤ (b-a)/(ξ*b) := div_le_div_of_nonneg_right (by linarith) (mul_pos hξ hb0).le
      _ ≤ (b-a)/(ξ*z) := div_le_div_of_nonneg_left (sub_nonneg.mpr hab)
        (mul_pos hξ hz) (mul_le_mul_of_nonneg_left hzb.le hξ.le)
  have hza : z < a := lt_of_not_ge ha
  have ha0 := hz.trans hza
  have haform : exposure ξ z a=min 1 ((a-z)/(ξ*a)) := by
    unfold exposure
    rw [max_eq_left hza.le,max_eq_right (sub_nonneg.mpr hza.le)]
  have hdiff : (b-z)/(ξ*b)-(a-z)/(ξ*a)=(b-a)*z/(ξ*a*b) := by
    field_simp [hξ.ne',ha0.ne',hb0.ne']
    ring
  have hraw : (b-z)/(ξ*b)-(a-z)/(ξ*a) ≤ (b-a)/(ξ*z) := by
    rw [hdiff]
    have hzab : z*z ≤ a*b := mul_le_mul hza.le hzb.le hz.le ha0.le
    apply (div_le_div_iff₀ (by positivity : 0 < ξ*a*b) (mul_pos hξ hz)).mpr

    nlinarith [mul_nonneg (mul_nonneg hξ.le (sub_nonneg.mpr hab)) (sub_nonneg.mpr hzab)]
  rw [haform,hbform]
  by_cases hA : 1 ≤ (a-z)/(ξ*a)
  · rw [min_eq_left hA]
    have hc := min_le_left (1:ℝ) ((b-z)/(ξ*b))
    have hn : 0 ≤ (b-a)/(ξ*z) := by positivity
    linarith
  · have hA' : (a-z)/(ξ*a) ≤ 1 := (lt_of_not_ge hA).le
    rw [min_eq_right hA']
    exact (sub_le_sub_right (min_le_right (1:ℝ) ((b-z)/(ξ*b))) _).trans hraw

theorem exposure_lipschitz {ξ z a b : ℝ} (hξ : 0 < ξ) (hz : 0 < z) :
    |exposure ξ z a-exposure ξ z b| ≤ |a-b| /(ξ*z) := by
  rcases le_total a b with hab | hba
  · have hm := exposure_monotone_bid hξ hz hab
    rw [abs_of_nonpos (sub_nonpos.mpr hm),abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using exposure_ordered_lipschitz hξ hz hab
  · have hm := exposure_monotone_bid hξ hz hba
    rw [abs_of_nonneg (sub_nonneg.mpr hm),abs_of_nonneg (sub_nonneg.mpr hba)]
    exact exposure_ordered_lipschitz hξ hz hba

theorem uniform_activeOnly_integral (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=conditionalValueLaw i) :
    (∫ p, activeOnly i p.1 ∂G)=
      (∫ v in entry i..cutoff i,activeMarginal (entry i) v)/cutoff i := by
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

theorem activeOnly_bounds (i : Row) (v : ℝ) : activeOnly i v ∈ Icc (0:ℝ) 1 := by
  by_cases hv : v ∈ Ioc (entry i) (cutoff i)
  · rw [activeOnly,Set.indicator_of_mem hv]
    have hv0 := (entry_pos i).trans hv.1
    have hdiv := (div_le_one hv0).mpr hv.1.le
    have hd0 := div_nonneg (entry_pos i).le hv0.le
    unfold activeMarginal
    constructor <;> linarith
  · simp [activeOnly,hv]

theorem finite_subentry_mean_lower (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=conditionalValueLaw i)
    {a e z : ℝ} (ha : 0 < a) (hat : entry i+a ≤ cutoff i) (he : 0 ≤ e)
    (hz : z ∈ Icc (1/2:ℝ) (x i))
    (hgraph : ∀ᵐ p ∂G, p.1 ∈ Ioc (entry i+a) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e) :
    rho+(1-x i)*(entry i-z*cutoff i)-a-e/(xi i*z) ≤
      ∫ p, p.1 ∂MixedLaw.law i (physicalLowerLaw i (z*cutoff i) G) := by
  let b : ℝ := z*cutoff i
  let d : ℝ := (entry i-b)/cutoff i
  let A : Set (ℝ × ℝ) := {p | p.1 ∈ Ioc (entry i) (cutoff i)}
  let S : Set (ℝ × ℝ) := {p | p.1 ∈ Ioc (entry i) (entry i+a)}
  have hb : 0 < b := mul_pos (by linarith [hz.1]) (cutoff_pos i)
  have hd : 0 ≤ d := by
    dsimp [d,b,entry]
    apply div_nonneg _ (cutoff_pos i).le
    nlinarith [hz.2,cutoff_pos i]
  have hA : MeasurableSet A := measurableSet_Ioc.preimage measurable_fst
  have hS : MeasurableSet S := measurableSet_Ioc.preimage measurable_fst
  have hpoint : ∀ᵐ p ∂G,
      activeOnly i p.1+A.indicator (fun _ => d) p-
          S.indicator (fun _ => (1:ℝ)) p-e/(xi i*b) ≤ exposure (xi i) b p.2 := by
    filter_upwards [value_support i G hvalue,hgraph] with p hpv hp
    by_cases hpa : p ∈ A
    · have hact := active_price_drop i hz hpa
      change d ≤ exposure (xi i) b (ActiveGraphComponent.activeBid i p.1)-
        exposure (xi i) (entry i) (ActiveGraphComponent.activeBid i p.1) at hact
      rw [exposure_entry_active i hpa] at hact
      have hone := exposure_le_one (xi i) b (ActiveGraphComponent.activeBid i p.1)
      rw [activeOnly,Set.indicator_of_mem (show p.1 ∈ Ioc (entry i) (cutoff i) from hpa),Set.indicator_of_mem hpa]
      by_cases hps : p ∈ S
      · rw [Set.indicator_of_mem hps]
        have he' : 0 ≤ e/(xi i*b) := div_nonneg he (mul_pos (xi_pos i) hb).le
        have hnon := exposure_nonneg (xi_pos i) hb (b := p.2)
        linarith
      · rw [Set.indicator_of_notMem hps]
        have hpstrip : p.1 ∈ Ioc (entry i+a) (cutoff i) := by
          refine ⟨?_,hpa.2⟩
          by_contra h
          exact hps ⟨hpa.1,le_of_not_gt h⟩
        have herr := (exposure_lipschitz (xi_pos i) hb
          (a := p.2) (b := ActiveGraphComponent.activeBid i p.1)).trans
          (div_le_div_of_nonneg_right (hp hpstrip) (mul_pos (xi_pos i) hb).le)
        have hlow := (abs_le.mp herr).1
        linarith
    · have hpL : p.1 ≤ entry i := by
        by_contra h
        exact hpa ⟨lt_of_not_ge h,hpv.2⟩
      have hps : p ∉ S := by intro h; exact (not_lt_of_ge hpL) h.1
      rw [activeOnly,Set.indicator_of_notMem (show p.1 ∉ Ioc (entry i) (cutoff i) from hpa),Set.indicator_of_notMem hpa,
        Set.indicator_of_notMem hps]
      have he' : 0 ≤ e/(xi i*b) := div_nonneg he (mul_pos (xi_pos i) hb).le
      have hnon := exposure_nonneg (xi_pos i) hb (b := p.2)
      linarith
  have hactiveI : Integrable (fun p : ℝ × ℝ => activeOnly i p.1) G :=
    Integrable.of_mem_Icc 0 1 ((activeOnly_measurable i).comp measurable_fst).aemeasurable
      (Filter.Eventually.of_forall fun p => activeOnly_bounds i p.1)
  have hAI : Integrable (A.indicator (fun _ => d)) G := (integrable_const d).indicator hA
  have hSI : Integrable (S.indicator (fun _ => (1:ℝ))) G := (integrable_const (1:ℝ)).indicator hS
  have hXI : Integrable (fun p : ℝ × ℝ => exposure (xi i) b p.2) G :=
    Integrable.of_mem_Icc 0 1
      ((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd).aemeasurable
      (Filter.Eventually.of_forall fun _ => ⟨exposure_nonneg (xi_pos i) hb,exposure_le_one _ _ _⟩)
  have hbound := integral_mono_ae
    (((hactiveI.add hAI).sub hSI).sub (integrable_const (e/(xi i*b)))) hXI hpoint
  have hadd : Integrable (fun p => activeOnly i p.1+A.indicator (fun _ => d) p) G := by
    convert! hactiveI.add hAI using 1
  have hsub : Integrable (fun p => activeOnly i p.1+A.indicator (fun _ => d) p-
      S.indicator (fun _ => (1:ℝ)) p) G := by
    convert! hadd.sub hSI using 1
  simp only [Pi.add_apply,Pi.sub_apply] at hbound
  rw [integral_sub hsub (integrable_const _),
    integral_sub hadd hSI,integral_add hactiveI hAI,
    integral_indicator_const _ hA,integral_indicator_const _ hS,
    integral_const,probReal_univ,one_smul,smul_eq_mul,smul_eq_mul,mul_one,
    uniform_activeOnly_integral i G hvalue] at hbound
  have hAm : G.real A=1-x i := lower_active_mass i G hvalue
  have hSm : G.real S=a/cutoff i := by
    have hmap : G.real S=(G.map Prod.fst).real (Ioc (entry i) (entry i+a)) := by
      rw [Measure.real,Measure.real,Measure.map_apply measurable_fst measurableSet_Ioc]
      rfl
    rw [hmap,hvalue,conditional_interval_mass i (entry_pos i).le (by linarith) hat]
    congr 1
    ring
  rw [hAm,hSm] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (cutoff_pos i).le
  have hz0 : 0 < z := by linarith [hz.1]
  have hcancel : cutoff i*((∫ v in entry i..cutoff i,activeMarginal (entry i) v)/cutoff i+
      (1-x i)*d-a/cutoff i-e/(xi i*b)) =
      (∫ v in entry i..cutoff i,activeMarginal (entry i) v)+
        (1-x i)*(entry i-z*cutoff i)-a-e/(xi i*z) := by
    dsimp [d,b]
    field_simp [(cutoff_pos i).ne',(xi_pos i).ne',hz0.ne']
  rw [hcancel] at hmul
  have hprofile := (source_profile_integrals i).2
  have hρ : rho=(1-cutoff i)/2+∫ v in entry i..cutoff i,activeMarginal (entry i) v := by
    norm_num only [rho,delta] at *
    linarith
  rw [physical_mean_formula i hb G,hρ]
  dsimp only [b] at hmul
  linarith

section UniformSource

variable (C : ℕ → Type*) (G : (m : ℕ) → C m → Measure (ℝ × ℝ))

theorem eventual_uniform_source_tilts (i : Row) {d : ℝ}
    (hd : 0 < d) (hdmax : d ≤ x i-1/2)
    (hprob : ∀ m (E : C m), IsProbabilityMeasure (G m E))
    (hvalue : ∀ m (E : C m), (G m E).map Prod.fst=conditionalValueLaw i)
    (hbid : ∀ m (E : C m), ∀ᵐ p ∂G m E, p.2 ≤ p.1)
    (hactive : ∀ a > (0:ℝ), ∀ e > (0:ℝ), ∀ᶠ m in atTop, ∀ E : C m,
      ∀ᵐ p ∂G m E, p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e) :
    ∃ θlo θhi vlo vhi : ℝ,
      0 < θlo ∧ 0 < θhi ∧ 0 < vlo ∧ 0 < vhi ∧
      ∀ᶠ m in atTop, ∀ E : C m, ∀ z ∈ Icc (1/2:ℝ) (x i-d),
        ∃ θ ∈ Icc θlo θhi,
          SubentryTilt.mean (MixedLaw.law i (physicalLowerLaw i (z*cutoff i) (G m E)))
            Prod.fst θ=(capacity m:ℝ)/((m-1:ℕ):ℝ) ∧
          variance Prod.fst ((MixedLaw.law i
            (physicalLowerLaw i (z*cutoff i) (G m E))).tilted
            (fun p => -θ*p.1)) ∈ Icc vlo vhi := by
  have ht := cutoff_pos i
  have hx : 0 < 1-x i := by cases i <;> norm_num [x,xQ]
  have hξ := xi_pos i
  have hρ : 0 < rho := by norm_num [rho]
  let g : ℝ := (1-x i)*d*cutoff i
  let a : ℝ := g/4
  let e : ℝ := g*xi i/8
  let r₀ : ℝ := rho/2
  let z₀ : ℝ := cutoff i/2
  have hg : 0 < g := by dsimp [g]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hz₀ : 0 < z₀ := by dsimp [z₀]; positivity
  have hd1 : d ≤ 1 := by
    have hx1 : x i ≤ 1 := by cases i <;> norm_num [x,xQ]
    linarith
  have hat : entry i+a ≤ cutoff i := by
    have hgd : g ≤ (1-x i)*cutoff i := by
      dsimp [g]
      nlinarith [mul_le_mul_of_nonneg_left hd1 (mul_pos hx ht).le]
    dsimp [a]
    unfold entry
    nlinarith
  let θlo : ℝ := (g/4)/Real.exp (4/(r₀*z₀))
  let θhi : ℝ := 2/(r₀*z₀)
  let vlo : ℝ := Real.exp (-4/(r₀*z₀))*z₀*r₀^2
  let vhi : ℝ := Real.exp (4/(r₀*z₀))
  refine ⟨θlo,θhi,vlo,vhi,by dsimp [θlo]; positivity,
    by dsimp [θhi]; positivity,by dsimp [vlo]; positivity,
    by dsimp [vhi]; positivity,?_⟩
  have htargetlo := PhysicalRates.rival_capacity_density_tendsto.eventually_const_lt
    (show r₀ < rho by dsimp [r₀]; linarith)
  have htargethi := PhysicalRates.rival_capacity_density_tendsto.eventually_lt_const
    (show rho < rho+g/4 by linarith)
  filter_upwards [hactive a ha e he,htargetlo,htargethi] with m hm hml hmu
  intro E z hz
  letI := hprob m E
  have hzrange : z ∈ Icc (1/2:ℝ) (x i) := ⟨hz.1,by linarith [hz.2]⟩
  have hzpos : 0 < z := by linarith [hz.1]
  have hb : 0 < z*cutoff i := mul_pos hzpos ht
  have hbt : z*cutoff i ≤ cutoff i := by
    have hx1 : x i ≤ 1 := by cases i <;> norm_num [x,xQ]
    nlinarith [hzrange.2,ht]
  letI := physicalLowerLaw_probability i hb (G m E)
  have hbounds := MixedLaw.demand_bounds i _ (physicalLowerLaw_bounds i hb (G m E))
  have hzero : z₀ ≤ (MixedLaw.law i (physicalLowerLaw i (z*cutoff i) (G m E))).real
      {p | p.1=0} := by
    have hl : z₀ ≤ z*cutoff i := by dsimp [z₀]; nlinarith [hz.1,ht]
    exact hl.trans (original_balanced_zero_mass i hb hbt (G m E) (hvalue m E) (hbid m E))
  have hfinite := finite_subentry_mean_lower i (G m E) (hvalue m E)
    ha hat he.le hzrange (hm E)
  have hgd : g ≤ (1-x i)*(entry i-z*cutoff i) := by
    dsimp [g]
    unfold entry
    have h := mul_le_mul_of_nonneg_left hz.2 (mul_pos hx ht).le
    nlinarith
  have hecost : e/(xi i*z) ≤ g/4 := by
    apply (div_le_iff₀ (mul_pos hξ hzpos)).mpr
    dsimp [e]
    nlinarith [mul_le_mul_of_nonneg_left hz.1 (mul_pos hg hξ).le]
  have hgap : (capacity m:ℝ)/((m-1:ℕ):ℝ)+g/4 ≤
      ∫ p, p.1 ∂MixedLaw.law i (physicalLowerLaw i (z*cutoff i) (G m E)) := by
    dsimp [a] at hfinite
    linarith
  obtain ⟨θ,hθl,hθu,hmatch,hvl,hvu⟩ :=
    TiltStability.exists_uniform_matching_tilt _ measurable_fst hbounds
      hz₀ hr₀ (by linarith : 0 < g/4) hml.le hzero hgap
  exact ⟨θ,⟨hθl,hθu.le⟩,hmatch,⟨hvl,hvu⟩⟩

end UniformSource

end FCAppendix.Affine.Uniform06.FiniteMean
