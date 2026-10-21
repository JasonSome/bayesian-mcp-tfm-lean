import FCAppendix.Affine.UniformFinite.ProductPayoff
import FCAppendix.Affine.UniformFinite.PhysicalLaw

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory
open Uniform05

lemma optimalExposure_eq_total {L : ℝ} (hL : 0< L) (v : ℝ) :
    optimalExposure L v=max 0 (v-L)/max v L := by
  by_cases hv : L< v
  · rw [optimalExposure,if_pos hv,max_eq_right (sub_pos.mpr hv).le,max_eq_left hv.le]
    field_simp [(hL.trans hv).ne']
  · rw [optimalExposure,if_neg hv,max_eq_left (sub_nonpos.mpr (le_of_not_gt hv)),
      zero_div]

lemma continuous_optimalExposure {L : ℝ} (hL : 0< L) :
    Continuous (optimalExposure L) := by
  rw [show optimalExposure L = (fun v => max 0 (v-L)/max v L) by
    funext v; exact optimalExposure_eq_total hL v]
  exact (continuous_const.max (continuous_id.sub continuous_const)).div
    (continuous_id.max continuous_const) (fun v=>(hL.trans_le (le_max_right v L)).ne')

lemma optimalExposure_bounds {L : ℝ} (hL : 0< L) (v : ℝ) :
    optimalExposure L v∈Icc (0:ℝ) 1 := by
  by_cases hv : L< v
  · rw [optimalExposure,if_pos hv]
    have hv0 := hL.trans hv
    have hr0 := div_nonneg hL.le hv0.le
    have hr1 := (div_le_one hv0).mpr hv.le
    constructor <;> linarith
  · simp [optimalExposure,hv]

lemma optimalExposure_antitone {L K : ℝ} (hL : 0< L) (hLK : L≤ K) (v : ℝ) :
    optimalExposure K v≤ optimalExposure L v := by
  by_cases hv : K< v
  · have hvL := hLK.trans_lt hv
    simp only [optimalExposure,if_pos hv,if_pos hvL]
    exact sub_le_sub_left (div_le_div_of_nonneg_right hLK (hL.trans hvL).le) 1
  · rw [optimalExposure,if_neg hv]
    exact (optimalExposure_bounds hL v).1

lemma optimalExposure_strict {L K v : ℝ} (hL : 0< L) (hLK : L< K) (hv : K< v) :
    optimalExposure K v< optimalExposure L v := by
  simp only [optimalExposure,if_pos hv,if_pos (hLK.trans hv)]
  exact sub_lt_sub_left (div_lt_div_of_pos_right hLK (hL.trans (hLK.trans hv))) 1

lemma floor_below_entry (i : Row) {v : ℝ} (hvt : v≤ t i) : floorBid i v< lambda i := by
  have ht := t_pos i
  have hm : max 0 (v-v0 i)≤ t i-v0 i := by
    apply max_le
    · dsimp [v0]
      linarith
    · linarith
  exact ((floor_le_chi_positivePart i v).trans
    (mul_le_mul_of_nonneg_left hm (by norm_num [chi]))).trans_lt
      (full_floor_max_below_lambda i)

lemma lambda_lt_t (i : Row) : lambda i< t i := by
  have ht := t_pos i
  have hx := x_range i
  unfold lambda
  nlinarith

lemma source_cap_receipt (i : Row) : (1-xi i)*cap i< lambda i := by
  have h := numerical_root_receipt_gap i
  have ht := t_pos i
  change kappa i*cap i< lambda i
  cases i <;> dsimp [lambda,x] at * <;> linarith

theorem optimal_exposure_lower_of_root_below (i : Row) {L v b : ℝ}
    (hL : 0< L) (hclip : (1-xi i)*cap i≤ L) (hLl : L≤ lambda i)
    (hv : v∈Icc (0:ℝ) (t i))
    (hb : b∈Icc (floorBid i v) (min v (cap i)))
    (hopt : ∀a∈Icc (floorBid i v) (min v (cap i)),
      productPayoff (xi i) v L a≤ productPayoff (xi i) v L b) :
    optimalExposure L v≤ exposure (xi i) L b := by
  by_cases hLv : L< v
  · have hx := xi_range i
    let B := activeBidAt (xi i) L v
    have hB := activeBidAt_bounds hx.1 hx.2 hL hLv
    have hBU : B≤ cap i := by
      have hroot := activeBidAt_mono_root hx.1 hx.2 hL hLl hv.1
      have hval := activeBidAt_mono_value hx.1 hx.2 (lambda_pos i) hv.1 hv.2
      have ht := t_pos i
      change activeBidAt (xi i) L v≤ cap i
      calc
        _ ≤ activeBidAt (xi i) (lambda i) v := hroot
        _ ≤ activeBid i (t i) := by simpa only [source_activeBid_eq] using hval
        _ ≤ cap i := by unfold cap; linarith
    by_cases hf : floorBid i v≤ B
    · have hmax := hopt B ⟨hf,le_min hB.2.1.le hBU⟩
      rw [show productPayoff (xi i) v L B=(v-L)^2/v from
        activeBidAt_product hx.1 hx.2 hL hLv] at hmax
      have hup := product_upper_bound hx.1 hx.2 hL hclip
        (hb.2.trans (min_le_right _ _)) hLv
      have he := product_maximum_unique hx.1 hx.2 hL hclip
        (hb.2.trans (min_le_right _ _)) hLv (le_antisymm hup hmax)
      rw [he,activeBidAt_exposure hx.1 hx.2 hL hLv,optimalExposure,if_pos hLv]
    · have hBb : B≤ b := (le_of_not_ge hf).trans hb.1
      have hm := exposure_monotone_bid hx.1 hL hBb
      simpa only [B,activeBidAt_exposure hx.1 hx.2 hL hLv,
        optimalExposure,if_pos hLv] using hm
  · rw [optimalExposure,if_neg hLv]
    exact exposure_nonneg (xi_range i).1 hL

theorem optimal_exposure_upper_of_root_above (i : Row) {L v b : ℝ}
    (hL : 0< L) (hclip : (1-xi i)*cap i≤ L) (hlL : lambda i≤ L)
    (hv : v∈Icc (0:ℝ) (t i))
    (hb : b∈Icc (floorBid i v) (min v (cap i)))
    (hopt : ∀a∈Icc (floorBid i v) (min v (cap i)),
      productPayoff (xi i) v L a≤ productPayoff (xi i) v L b) :
    exposure (xi i) L b≤ optimalExposure L v := by
  by_cases hLv : L< v
  · have hx := xi_range i
    let B := activeBidAt (xi i) L v
    have hB := activeBidAt_bounds hx.1 hx.2 hL hLv
    by_cases hBU : B≤ cap i
    · have hf : floorBid i v≤ B :=
        ((floor_below_entry i hv.2).le.trans hlL).trans hB.1.le
      have hmax := hopt B ⟨hf,le_min hB.2.1.le hBU⟩
      rw [show productPayoff (xi i) v L B=(v-L)^2/v from
        activeBidAt_product hx.1 hx.2 hL hLv] at hmax
      have hup := product_upper_bound hx.1 hx.2 hL hclip
        (hb.2.trans (min_le_right _ _)) hLv
      have he := product_maximum_unique hx.1 hx.2 hL hclip
        (hb.2.trans (min_le_right _ _)) hLv (le_antisymm hup hmax)
      rw [he,activeBidAt_exposure hx.1 hx.2 hL hLv,optimalExposure,if_pos hLv]
    · have hbB : b≤ B :=
        (hb.2.trans (min_le_right _ _)).trans (le_of_not_ge hBU)
      have hm := exposure_monotone_bid hx.1 hL hbB
      simpa only [B,activeBidAt_exposure hx.1 hx.2 hL hLv,
        optimalExposure,if_pos hLv] using hm
  · rw [optimalExposure,if_neg hLv,
      exposure_zero ((hb.2.trans (min_le_left _ _)).trans (le_of_not_gt hLv))]

lemma integrable_optimalExposure {L : ℝ} (hL : 0< L)
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsFiniteMeasure mu]
    (v : Ω→ℝ) (hv : Measurable v) : Integrable (fun a=> optimalExposure L (v a)) mu := by
  apply Integrable.of_bound ((continuous_optimalExposure hL).measurable.comp hv).aestronglyMeasurable 1
  exact ae_of_all mu (fun a=> by
    change |optimalExposure L (v a)| ≤ 1
    rw [abs_of_nonneg (optimalExposure_bounds hL (v a)).1]
    exact (optimalExposure_bounds hL (v a)).2)

def meanOptimalExposure (i : Row) (L : ℝ) : ℝ :=
  ∫v,optimalExposure L v ∂lowerValueMeasure i

lemma integral_original_optimalExposure (i : Row) (G : RestrictedLaw i)
    {L : ℝ} (hL : 0< L) :
    (∫p,optimalExposure L p.1 ∂(G.1 : Measure (ℝ×Bid i)))=meanOptimalExposure i L := by
  unfold meanOptimalExposure
  have hh := integral_map (μ := (G.1 : Measure (ℝ × Bid i)))
    measurable_fst.aemeasurable
    (continuous_optimalExposure hL).measurable.aestronglyMeasurable
  rw [G.2.1] at hh
  exact hh.symm

lemma meanOptimalExposure_source (i : Row) :
    meanOptimalExposure i (lambda i)=requiredDemand i := by
  have hL := lambda_pos i
  have hLt := lambda_lt_t i
  have ht := t_pos i
  have hc := continuous_optimalExposure hL
  have hzero : (∫v in (0:ℝ)..lambda i,optimalExposure (lambda i) v)=0 := by
    rw [intervalIntegral.integral_of_le hL.le]
    have he : (∫v in Ioc (0:ℝ) (lambda i),optimalExposure (lambda i) v)=
        ∫v in Ioc (0:ℝ) (lambda i),(0:ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro v hv
      simp [optimalExposure,not_lt.mpr hv.2]
    rw [he]
    simp
  have hactive : (∫v in lambda i..t i,optimalExposure (lambda i) v)=
      ∫v in lambda i..t i,Uniform07.activeMarginal (lambda i) v := by
    rw [intervalIntegral.integral_of_le hLt.le,intervalIntegral.integral_of_le hLt.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    simp [optimalExposure,hv.1,Uniform07.activeMarginal]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (lambda i) (μ := volume))
    (hc.intervalIntegrable (lambda i) (t i) (μ := volume))
  rw [hzero,zero_add,hactive] at hsplit
  have hclear := (Uniform07.source_profile_integrals i).2
  rw [← t_eq_canonical i,← lambda_eq_canonical i,← delta_eq_canonical] at hclear
  unfold meanOptimalExposure lowerValueMeasure
  rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht.le,← hsplit]
  change (1/t i)*(∫v in lambda i..t i,Uniform07.activeMarginal (lambda i) v)=
    (t i-delta)/(2*t i)
  field_simp [ht.ne']
  nlinarith

lemma meanOptimalExposure_strict (i : Row) (G : RestrictedLaw i)
    {L K : ℝ} (hL : 0< L) (hLK : L< K) (hKt : K< t i) :
    meanOptimalExposure i K< meanOptimalExposure i L := by
  have hK := hL.trans hLK
  let mu : Measure (ℝ×Bid i) := G.1
  let f : (ℝ×Bid i)→ℝ := fun p=> optimalExposure L p.1-optimalExposure K p.1
  have hLi := integrable_optimalExposure hL mu Prod.fst measurable_fst
  have hKi := integrable_optimalExposure hK mu Prod.fst measurable_fst
  have hnonneg : ∀p,0≤ f p := fun p=> sub_nonneg.mpr (optimalExposure_antitone hL hLK.le p.1)
  have hmass : mu {p | K< p.1 ∧ p.1≤ t i}≠0 := by
    have hratio0 : 0≤ K/t i := div_nonneg hK.le (t_pos i).le
    have hratio1 : K/t i<1 := (div_lt_one (t_pos i)).mpr hKt
    have he := G.value_interval_mass hratio0 hratio1.le le_rfl
    have htne := (t_pos i).ne'
    simp only [div_mul_cancel₀ _ htne,one_mul] at he
    rw [he]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hsub : {p : ℝ×Bid i | K< p.1 ∧ p.1≤ t i}⊆Function.support f := by
    intro p hp
    exact (sub_pos.mpr (optimalExposure_strict hL hLK hp.1)).ne'
  have hpos : 0<∫p,f p ∂mu := by
    apply (integral_pos_iff_support_of_nonneg hnonneg (hLi.sub hKi)).mpr
    exact pos_iff_ne_zero.mpr (mt (measure_mono_null hsub) hmass)
  rw [show f=(fun p=> optimalExposure L p.1-optimalExposure K p.1) from rfl,
    integral_sub hLi hKi] at hpos
  rw [integral_original_optimalExposure i G hL,
    integral_original_optimalExposure i G hK] at hpos
  linarith

def ProductOptimal (i : Row) (G : RestrictedLaw i) : Prop :=
  ∀ᵐp ∂(G.1 : Measure (ℝ×Bid i)),
    ∀a∈Icc (floorBid i p.1) (min p.1 (cap i)),
      productPayoff (xi i) p.1 G.multiplier a≤
        productPayoff (xi i) p.1 G.multiplier p.2

theorem only_source_multiplier_clears (i : Row) (G : RestrictedLaw i)
    (hopt : ProductOptimal i G) : G.multiplier=lambda i := by
  have hg := G.multiplier_guards
  have hL : 0< G.multiplier := (demandLo_pos i).trans hg.1
  have hclip : (1-xi i)*cap i≤ G.multiplier := hg.2.2.2.le
  have hLt : G.multiplier< t i := hg.2.2.1.trans (cap_lt_t i)
  have hex : Integrable (fun p : ℝ×Bid i=> exposure (xi i) G.multiplier p.2)
      (G.1 : Measure (ℝ×Bid i)) := by
    apply integrable_of_unit_bounds
    · exact ((continuous_exposure (xi_range i).1 hL).comp
        (continuous_subtype_val.comp continuous_snd)).measurable
    · exact fun _=> exposure_nonneg (xi_range i).1 hL
    · exact fun _=> exposure_le_one _ _ _
  have hdem : (∫p,exposure (xi i) G.multiplier p.2
      ∂(G.1 : Measure (ℝ×Bid i)))=requiredDemand i := by
    rw [← G.integral_bidLaw (integrable_lawDemand i G.bidLaw hL).aestronglyMeasurable]
    exact G.multiplier_equation
  have hi := integrable_optimalExposure hL (G.1 : Measure (ℝ×Bid i)) Prod.fst measurable_fst
  rcases lt_trichotomy G.multiplier (lambda i) with hl | he | hh
  · have hmean : meanOptimalExposure i G.multiplier≤ requiredDemand i := by
      have hle : ∀ᵐp ∂(G.1 : Measure (ℝ×Bid i)),
          optimalExposure G.multiplier p.1≤ exposure (xi i) G.multiplier p.2 := by
        filter_upwards [G.2.2,hopt] with p hp ho
        exact optimal_exposure_lower_of_root_below i hL hclip hl.le hp.1
          ⟨hp.2.1,le_min hp.2.2 p.2.property.2⟩ ho
      have h := integral_mono_ae hi hex hle
      rwa [integral_original_optimalExposure i G hL,hdem] at h
    have hstrict := meanOptimalExposure_strict i G hL hl (lambda_lt_t i)
    rw [meanOptimalExposure_source] at hstrict
    exact False.elim ((not_lt_of_ge hmean) hstrict)
  · exact he
  · have hmean : requiredDemand i≤ meanOptimalExposure i G.multiplier := by
      have hle : ∀ᵐp ∂(G.1 : Measure (ℝ×Bid i)),
          exposure (xi i) G.multiplier p.2≤ optimalExposure G.multiplier p.1 := by
        filter_upwards [G.2.2,hopt] with p hp ho
        exact optimal_exposure_upper_of_root_above i hL hclip hh.le hp.1
          ⟨hp.2.1,le_min hp.2.2 p.2.property.2⟩ ho
      have h := integral_mono_ae hex hi hle
      rwa [hdem,integral_original_optimalExposure i G hL] at h
    have hstrict := meanOptimalExposure_strict i G (lambda_pos i) hh hLt
    rw [meanOptimalExposure_source] at hstrict
    exact False.elim ((not_lt_of_ge hmean) hstrict)

theorem product_optimal_active_graph (i : Row) (G : RestrictedLaw i)
    (hopt : ProductOptimal i G) :
    G.multiplier=lambda i ∧
    (∀ᵐp ∂(G.1 : Measure (ℝ×Bid i)),
      (lambda i< p.1→(p.2:ℝ)=activeBid i p.1) ∧
      (p.1≤ lambda i→(p.2:ℝ)≤ lambda i)) := by
  have he := only_source_multiplier_clears i G hopt
  refine ⟨he,?_⟩
  filter_upwards [G.2.2,hopt] with p hp ho
  rw [he] at ho
  exact ⟨fun hv=> source_active_maximizer i hv hp.1.2
    ⟨hp.2.1,le_min hp.2.2 p.2.property.2⟩ ho,
    fun hv=> hp.2.2.trans hv⟩

end FCAppendix.Affine.UniformFinite
