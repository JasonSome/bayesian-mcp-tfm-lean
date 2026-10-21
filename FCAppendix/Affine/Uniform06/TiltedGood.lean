import FCAppendix.Probability.BoundedTiltVariance
import FCAppendix.Affine.LowBody.ClusterLossBound
import FCAppendix.Affine.Uniform06.CostAmplification
import FCAppendix.Affine.Uniform06.EarlyRankCeiling
import FCAppendix.Affine.Uniform06.CapacityFloor

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.TiltedGood

open MeasureTheory ProbabilityTheory Set Filter LowBody
open FCAppendix.ExponentialTilt FCAppendix.Affine.ClippedResidual
open Uniform07 RawMixedSource RivalGood CostAmplification
open scoped BigOperators

def law (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) : Measure RowRival :=
  (source i G).tilted (fun r => -θ*demand (xi i) b r)

theorem law_probability (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ : ℝ) : IsProbabilityMeasure (law i G b θ) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_of_bounded (source i G)
    (measurable_demand _ _).aemeasurable
    (ae_of_all _ fun r => demand_bounds (xi_pos i) hb r) (-θ))

theorem original_no_active_tag (i : Row) (G : Measure (ℝ × ℝ)) :
    ∀ᵐ r ∂source i G, r.1 ≠ 1 := by
  unfold source rivalLaw
  simp only [ENNReal.ofReal_zero,zero_smul,add_zero,ae_add_measure_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    exact ae_of_all _ fun r => by norm_num [Fin.ext_iff]
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (by measurability)).mpr
    norm_num [Fin.ext_iff]
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (by measurability)).mpr
    norm_num [Fin.ext_iff]

theorem tilted_no_active_tag (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) :
    ∀ᵐ r ∂law i G b θ, r.1 ≠ 1 :=
  (tilted_absolutelyContinuous _ _).ae_le (original_no_active_tag i G)

theorem tag_unit (j : Fin 4) (r : RowRival) : tag j r ∈ Icc (0:ℝ) 1 := by
  unfold tag
  split_ifs <;> norm_num

theorem sign_tags (r : RowRival) : sign r=tag 2 r-tag 3 r := by
  obtain ⟨j,b⟩ := r
  fin_cases j <;> norm_num [sign,tag,Fin.ext_iff]

theorem retained_tags (r : RowRival) (hr : r.1 ≠ 1) :
    tag 0 r+tag 2 r+tag 3 r=1 := by
  obtain ⟨j,b⟩ := r
  fin_cases j <;> norm_num [tag,Fin.ext_iff] at *

theorem demand_tags (ξ b : ℝ) (r : RowRival) (hr : r.1 ≠ 1) :
    demand ξ b r=lowerTest (exposure ξ b) r+(tag 2 r+tag 3 r)/2 := by
  obtain ⟨j,z⟩ := r
  fin_cases j <;> norm_num [demand,lowerTest,tag,Fin.ext_iff] at *

theorem tilted_sign_mean (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    (∫ r, sign r ∂law i G b θ)=0 := by
  letI := MixedLaw.physicalLowerLaw_probability i hb G
  rw [law,integral_tilted_mul_eq_cgf _
    (integrable_exp_mul_of_bounded (source i G) (measurable_demand _ _).aemeasurable
      (ae_of_all _ fun r => demand_bounds (xi_pos i) hb r) (-θ))]
  simp only [smul_eq_mul]
  have he := integral_source_test i G hb
    (fun p => Real.exp (-θ*p.1-cgf (demand (xi i) b) (source i G) (-θ))*p.2)
    (by fun_prop)
  change (∫ r, Real.exp (-θ*demand (xi i) b r-
      cgf (demand (xi i) b) (source i G) (-θ))*sign r ∂source i G)=_ at he
  rw [he,MixedLaw.integral_law i _ (MixedLaw.physicalLowerLaw_bounds i hb G) (by fun_prop)]
  simp only [smul_eq_mul,mul_zero,integral_zero]
  ring

def lowerProbability (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) : ℝ :=
  ∫ r, tag 0 r ∂law i G b θ

def upperProbability (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) : ℝ :=
  ∫ r, tag 2 r ∂law i G b θ

def lowerDemand (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) : ℝ :=
  ∫ r, lowerTest (exposure (xi i) b) r ∂law i G b θ

theorem tilted_population_identities (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    (∫ r, tag 3 r ∂law i G b θ)=upperProbability i G b θ ∧
    lowerProbability i G b θ+2*upperProbability i G b θ=1 ∧
    0 ≤ lowerProbability i G b θ ∧ 0 ≤ upperProbability i G b θ ∧
    upperProbability i G b θ ≤ 1/2 ∧
    (∫ r, demand (xi i) b r ∂law i G b θ)=
      lowerDemand i G b θ+upperProbability i G b θ := by
  let ν := law i G b θ
  letI : IsProbabilityMeasure ν := law_probability i G hb θ
  have hi (j : Fin 4) : Integrable (tag j) ν := Integrable.of_mem_Icc 0 1
    (measurable_tag j).aemeasurable (ae_of_all _ fun r => tag_unit j r)
  have hli : Integrable (lowerTest (exposure (xi i) b)) ν :=
    Integrable.of_mem_Icc 0 1 (measurable_lowerTest (by unfold exposure; fun_prop)).aemeasurable
      (ae_of_all _ fun r => lowerTest_unit
        (fun z => ⟨exposure_nonneg (xi_pos i) hb,exposure_le_one _ _ _⟩) r)
  have hs := tilted_sign_mean i G hb θ
  simp_rw [sign_tags] at hs
  rw [integral_sub (hi 2) (hi 3)] at hs
  have heq : (∫ r, tag 3 r ∂ν)=(∫ r, tag 2 r ∂ν) := by linarith
  have hsum := integral_congr_ae ((tilted_no_active_tag i G b θ).mono
    fun r hr => retained_tags r hr)
  have h02 : Integrable (fun r => tag 0 r+tag 2 r) ν := by
    convert! (hi 0).add (hi 2) using 1
  change (∫ r, tag 0 r+tag 2 r+tag 3 r ∂ν)=(∫ r, (1:ℝ) ∂ν) at hsum
  rw [integral_add h02 (hi 3),integral_add (hi 0) (hi 2),
    integral_const] at hsum
  simp only [probReal_univ,smul_eq_mul,mul_one] at hsum
  have hp0 : 0 ≤ ∫ r, tag 0 r ∂ν := integral_nonneg fun r => (tag_unit 0 r).1
  have hp2 : 0 ≤ ∫ r, tag 2 r ∂ν := integral_nonneg fun r => (tag_unit 2 r).1
  have hd := integral_congr_ae ((tilted_no_active_tag i G b θ).mono
    fun r hr => demand_tags (xi i) b r hr)
  have h23 : Integrable (fun r => tag 2 r+tag 3 r) ν := by
    convert! (hi 2).add (hi 3) using 1
  have hdiv : Integrable (fun r => (tag 2 r+tag 3 r)/2) ν := h23.div_const 2
  change (∫ r, demand (xi i) b r ∂ν)=
    (∫ r, lowerTest (exposure (xi i) b) r+(tag 2 r+tag 3 r)/2 ∂ν) at hd
  rw [integral_add hli hdiv,integral_div,integral_add (hi 2) (hi 3),heq] at hd
  refine ⟨heq,?_,hp0,hp2,?_,?_⟩
  · change (∫ r, tag 0 r ∂ν)+2*(∫ r, tag 2 r ∂ν)=1
    linarith
  · change (∫ r, tag 2 r ∂ν) ≤ 1/2
    linarith
  · change (∫ r, demand (xi i) b r ∂ν)=
      (∫ r, lowerTest (exposure (xi i) b) r ∂ν)+(∫ r, tag 2 r ∂ν)
    linarith

theorem original_strip_mass (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {lo U : ℝ} (hcap : ∀ᵐ p ∂G, p.2 ≤ U) :
    (source i G).real (activeStrip lo U)=
      cutoff i-PureRankCounts.sourceRank (cutoff i) (G.map Prod.snd) lo := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hc : ∀ᵐ z ∂G.map Prod.snd, z ≤ U :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_Iic).mpr hcap
  have he : Ioc lo U =ᵐ[G.map Prod.snd] Ioi lo := by
    filter_upwards [hc] with z hz
    apply propext
    change (lo < z ∧ z ≤ U) ↔ lo < z
    exact and_iff_left hz
  have hm := lowCluster_probability (cutoff i) 0 (1-cutoff i) (cutoff_pos i).le
    (G.map Prod.snd) (Ioc lo U) measurableSet_Ioc
  change (source i G).real (activeStrip lo U)=_ at hm
  rw [hm,measureReal_def,measure_congr he]
  change cutoff i*(G.map Prod.snd).real (Ioi lo)=_
  have ht := probReal_compl_eq_one_sub (μ := G.map Prod.snd)
    (s := Iic lo) measurableSet_Iic
  rw [show Ioi lo=(Iic lo)ᶜ by simp,ht,PureRankCounts.sourceRank]
  ring

def stripMass (i : Row) : ℝ := cutoff i-RankCutoff.Mstar i

theorem stripMass_pos (i : Row) : 0 < stripMass i := by
  have hh : x i+1/200 < 1 := by cases i <;> norm_num [x,xQ]
  have ht := mul_lt_mul_of_pos_right hh (cutoff_pos i)
  simpa [stripMass,RankCutoff.Mstar] using sub_pos.mpr ht

theorem early_original_strip_mass (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hcap : ∀ᵐ p ∂G, p.2 ≤ ReceiptGap.cap i)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000)
    {lo : ℝ} (hlo : lo ≤ EarlyRankCeiling.prefixEnd i) :
    stripMass i ≤ (source i G).real (activeStrip lo (ReceiptGap.cap i)) := by
  rw [original_strip_mass i G hcap]
  exact sub_le_sub_left (EarlyRankCeiling.source_early_rank_ceiling i G hvalue hactive lo hlo).le _

def stripTest (lo U : ℝ) : RowRival → ℝ := (activeStrip lo U).indicator (fun _ => 1)

theorem measurable_stripTest (lo U : ℝ) : Measurable (stripTest lo U) :=
  measurable_const.indicator (measurable_activeStrip lo U)

theorem stripTest_unit (lo U : ℝ) (r : RowRival) : stripTest lo U r ∈ Icc (0:ℝ) 1 := by
  unfold stripTest
  by_cases hr : r ∈ activeStrip lo U <;> simp [hr]

theorem integral_stripTest (μ : Measure RowRival) [IsFiniteMeasure μ] (lo U : ℝ) :
    (∫ r, stripTest lo U r ∂μ)=μ.real (activeStrip lo U) := by
  rw [stripTest,integral_indicator (measurable_activeStrip lo U),setIntegral_const]
  simp

theorem tilted_strip_mass_lower (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b θ Θ lo U q : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) (hΘ : θ ≤ Θ)
    (hq : q ≤ (source i G).real (activeStrip lo U)) :
    Real.exp (-2*Θ)*q ≤ (law i G b θ).real (activeStrip lo U) := by
  letI := law_probability i G hb θ
  have hh := (integral_tilted_bounds (source i G) (measurable_demand _ _)
    (ae_of_all _ fun r => demand_bounds (xi_pos i) hb r)
    (show |-θ| ≤ Θ by simpa [abs_of_nonneg hθ] using hΘ)
    ((integrable_const (1:ℝ)).indicator (measurable_activeStrip lo U))
    (ae_of_all _ fun r => (stripTest_unit lo U r).1)).1
  change Real.exp (-2*Θ)*(∫ r, stripTest lo U r ∂source i G) ≤
    (∫ r, stripTest lo U r ∂law i G b θ) at hh
  rw [integral_stripTest,integral_stripTest] at hh
  exact (mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le).trans hh

def exposureMargin (i : Row) (hi lo U : ℝ) : ℝ := min 1 ((lo-hi)/(xi i*U))

theorem exposureMargin_pos (i : Row) {hi lo U : ℝ} (hl : hi < lo) (hU : 0 < U) :
    0 < exposureMargin i hi lo U :=
  lt_min (by norm_num) (div_pos (sub_pos.mpr hl) (mul_pos (xi_pos i) hU))

theorem strip_exposure_lower (i : Row) {b hi lo U : ℝ}
    (hb : 0 < b) (hhi : b ≤ hi) (hl : hi < lo) (hU : 0 < U) (r : RowRival) :
    exposureMargin i hi lo U*stripTest lo U r ≤ lowerTest (exposure (xi i) b) r := by
  by_cases hr : r ∈ activeStrip lo U
  · have hbr : b < r.2 := (hhi.trans_lt hl).trans hr.2.1
    have hr0 : 0 < r.2 := hb.trans hbr
    have hfrac : (lo-hi)/(xi i*U) ≤ (r.2-b)/(xi i*r.2) := by
      apply (div_le_div_iff₀ (mul_pos (xi_pos i) hU) (mul_pos (xi_pos i) hr0)).mpr
      have hh : (lo-hi)*r.2 ≤ (r.2-b)*U := by
        have h1 := mul_nonneg (sub_nonneg.mpr hr.2.1.le) hU.le
        have h2 := mul_nonneg (sub_nonneg.mpr hhi) hU.le
        have h3 := mul_nonneg (sub_nonneg.mpr hl.le) (sub_nonneg.mpr hr.2.2)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh (xi_pos i).le]
    rw [stripTest,indicator_of_mem hr, mul_one,lowerTest,if_pos hr.1]
    unfold exposureMargin exposure
    rw [max_eq_left hbr.le,max_eq_right (sub_nonneg.mpr hbr.le)]
    exact min_le_min_left 1 hfrac
  · rw [stripTest,indicator_of_notMem hr,mul_zero]
    exact (lowerTest_unit
      (fun z => ⟨exposure_nonneg (xi_pos i) hb,exposure_le_one _ _ _⟩) r).1

theorem tilted_lower_demand (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b hi lo U θ Θ q : ℝ} (hb : 0 < b) (hhi : b ≤ hi) (hl : hi < lo) (hU : 0 < U)
    (hθ : 0 ≤ θ) (hΘ : θ ≤ Θ) (hq : q ≤ (source i G).real (activeStrip lo U)) :
    exposureMargin i hi lo U*Real.exp (-2*Θ)*q ≤ lowerDemand i G b θ := by
  let ν := law i G b θ
  letI : IsProbabilityMeasure ν := law_probability i G hb θ
  have hs := tilted_strip_mass_lower i G hb hθ hΘ hq
  have hlo := integral_mono
    (((integrable_const (1:ℝ) (μ := ν)).indicator (measurable_activeStrip lo U)).const_mul
      (exposureMargin i hi lo U))
    (Integrable.of_mem_Icc 0 1
      (measurable_lowerTest (by unfold exposure; fun_prop)).aemeasurable
      (ae_of_all _ fun r => lowerTest_unit
        (fun z => ⟨exposure_nonneg (xi_pos i) hb,exposure_le_one _ _ _⟩) r))
    (fun r => strip_exposure_lower i hb hhi hl hU r)
  rw [integral_const_mul] at hlo
  change exposureMargin i hi lo U*(∫ r, stripTest lo U r ∂ν) ≤ lowerDemand i G b θ at hlo
  rw [integral_stripTest] at hlo
  have hh := mul_le_mul_of_nonneg_left hs (exposureMargin_pos i hl hU).le
  have hh' : exposureMargin i hi lo U*Real.exp (-2*Θ)*q ≤
      exposureMargin i hi lo U*ν.real (activeStrip lo U) := by
    convert! hh using 1
    ring
  exact hh'.trans hlo

theorem matching_residual_margins (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {m : ℕ} (hm : 2 ≤ m)
    {b hi lo U θ Θ q : ℝ} (hb : 0 < b) (hhi : b ≤ hi) (hl : hi < lo) (hU : 0 < U)
    (hθ : 0 ≤ θ) (hΘ : θ ≤ Θ) (hq : q ≤ (source i G).real (activeStrip lo U))
    (hmatch : (∫ r, demand (xi i) b r ∂law i G b θ)=
      (capacity m:ℝ)/((m-1:ℕ):ℝ)) :
    exposureMargin i hi lo U*Real.exp (-2*Θ)*q-1/((m-1:ℕ):ℝ) ≤
      rho-upperProbability i G b θ ∧
    (1/2000:ℝ) ≤ lowerProbability i G b θ-(rho-upperProbability i G b θ) := by
  have hpop := tilted_population_identities i G hb θ
  have hd := tilted_lower_demand i G hb hhi hl hU hθ hΘ hq
  have herr := abs_le.mp (PhysicalRates.rival_capacity_density_error hm)
  rw [hmatch] at hpop
  constructor
  · linarith [hpop.2.2.2.2.2]
  · norm_num only [rho] at *
    linarith [hpop.2.1,hpop.2.2.2.2.1]

def statistics (lo U : ℝ) : Fin 4 → RowRival → ℝ :=
  ![tag 0,tag 2,tag 3,stripTest lo U]

theorem statistics_measurable (lo U : ℝ) : ∀ k, Measurable (statistics lo U k) := by
  intro k
  fin_cases k
  · exact measurable_tag 0
  · exact measurable_tag 2
  · exact measurable_tag 3
  · exact measurable_stripTest lo U

theorem statistics_unit (lo U : ℝ) : ∀ k r, statistics lo U k r ∈ Icc (0:ℝ) 1 := by
  intro k r
  fin_cases k
  · exact tag_unit 0 r
  · exact tag_unit 2 r
  · exact tag_unit 3 r
  · exact stripTest_unit lo U r

theorem source_good_complement (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ lo U : ℝ) {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => law i G b θ)).real
      (RivalGood.good (law i G b θ) (statistics lo U) N ε)ᶜ ≤
      8*Real.exp (-2*(N:ℝ)*ε^2) := by
  letI := law_probability i G hb θ
  have hh := RivalGood.good_complement_le (law i G b θ) (statistics lo U)
    (fun k => (statistics_measurable lo U k).aemeasurable)
    (fun k => ae_of_all _ fun r => statistics_unit lo U k r) N hN hε
  norm_num only [Fintype.card_fin,Nat.cast_ofNat,show (2:ℝ)*4=8 by norm_num] at hh
  exact hh

theorem source_good_with_marks (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ lo U : ℝ) {N r m : ℕ} (hN : 0 < N) (hsize : N+r=m)
    {ε : ℝ} (hε : 0 ≤ ε) {ω : Fin N → RowRival}
    (hgood : ω ∈ RivalGood.good (law i G b θ) (statistics lo U) N ε) :
    ∀ marks : Fin r → RowRival, ∀ k,
      |(∑ j, statistics lo U k (ω j))+(∑ j, statistics lo U k (marks j))-
        (m:ℝ)*(∫ z, statistics lo U k z ∂law i G b θ)| ≤ ε*(m:ℝ)+(r:ℝ) := by
  letI := law_probability i G hb θ
  intro marks
  exact RivalGood.insertions_error hsize
    (fun k => (statistics_measurable lo U k).aemeasurable)
    (fun k => ae_of_all _ fun z => statistics_unit lo U k z)
    hε hgood hN (fun j k => statistics lo U k (marks j))
    (fun j k => statistics_unit lo U k (marks j))

end FCAppendix.Affine.Uniform06.TiltedGood
