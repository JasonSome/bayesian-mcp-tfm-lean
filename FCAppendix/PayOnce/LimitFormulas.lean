import FCAppendix.Exclusive.Duplication

namespace FCAppendix
namespace PayOnce
namespace Limit

open MeasureTheory Filter Topology Set

noncomputable def pStar (n : ℕ) (t w : ℝ) : ℝ :=
  if 0 < w then max 0 (1 - (t / w) ^ (1 / ((n : ℝ) - 1))) else 0

noncomputable def demand (μW : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ w, pStar n t w ∂μW

noncomputable def coverage (μW : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ w, success n (pStar n t w) ∂μW

section Pointwise

variable {n : ℕ} {t w : ℝ}

theorem exponent_pos (hn : 2 ≤ n) : 0 < 1 / ((n : ℝ) - 1) := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact one_div_pos.mpr (by linarith)

theorem pStar_of_pos (hw : 0 < w) :
    pStar n t w = max 0 (1 - (t / w) ^ (1 / ((n : ℝ) - 1))) := if_pos hw

theorem pStar_of_nonpos (hw : w ≤ 0) : pStar n t w = 0 := if_neg (not_lt.mpr hw)

theorem pStar_nonneg : 0 ≤ pStar n t w := by
  unfold pStar
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem pStar_le_one (ht : 0 ≤ t) : pStar n t w ≤ 1 := by
  unfold pStar
  split_ifs with hw
  · apply max_le zero_le_one
    have := Real.rpow_nonneg (div_nonneg ht (le_of_lt hw)) (1 / ((n : ℝ) - 1))
    linarith
  · exact zero_le_one

theorem rpow_lt_one_iff_lt (hn : 2 ≤ n) (ht : 0 ≤ t) (hw : 0 < w) :
    (t / w) ^ (1 / ((n : ℝ) - 1)) < 1 ↔ t < w := by
  constructor
  · intro h
    by_contra hle
    have h1 : 1 ≤ t / w := (one_le_div hw).mpr (not_lt.mp hle)
    exact absurd h (not_lt.mpr (Real.one_le_rpow h1 (le_of_lt (exponent_pos hn))))
  · intro h
    exact Real.rpow_lt_one (div_nonneg ht (le_of_lt hw)) ((div_lt_one hw).mpr h)
      (exponent_pos hn)

theorem pStar_pos_iff (hn : 2 ≤ n) (ht : 0 ≤ t) : 0 < pStar n t w ↔ t < w := by
  by_cases hw : 0 < w
  · rw [pStar_of_pos hw, lt_max_iff, sub_pos, rpow_lt_one_iff_lt hn ht hw]
    simp
  · rw [pStar_of_nonpos (not_lt.mp hw)]
    constructor
    · intro h
      exact absurd h (lt_irrefl 0)
    · intro h
      exact absurd (lt_of_le_of_lt ht h) hw

theorem pStar_eq_zero_of_le (hn : 2 ≤ n) (ht : 0 ≤ t) (hwt : w ≤ t) : pStar n t w = 0 := by
  have h := (pStar_pos_iff (n := n) (w := w) hn ht).not.mpr (not_lt.mpr hwt)
  exact le_antisymm (not_lt.mp h) pStar_nonneg

theorem pStar_of_lt (hn : 2 ≤ n) (ht : 0 ≤ t) (htw : t < w) :
    pStar n t w = 1 - (t / w) ^ (1 / ((n : ℝ) - 1)) := by
  have hw : 0 < w := lt_of_le_of_lt ht htw
  rw [pStar_of_pos hw]
  apply max_eq_right
  have := (rpow_lt_one_iff_lt hn ht hw).mpr htw
  linarith

theorem pStar_lt_one (hn : 2 ≤ n) (ht : 0 < t) (htw : t < w) : pStar n t w < 1 := by
  rw [pStar_of_lt hn (le_of_lt ht) htw]
  have := Real.rpow_pos_of_pos (div_pos ht (lt_trans ht htw)) (1 / ((n : ℝ) - 1))
  linarith

@[simp] theorem pStar_zero_price (hn : 2 ≤ n) (w : ℝ) :
    pStar n 0 w = (Ioi (0 : ℝ)).indicator 1 w := by
  by_cases hw : 0 < w
  · rw [pStar_of_pos hw, indicator_of_mem (show w ∈ Ioi (0 : ℝ) from hw), zero_div,
      Real.zero_rpow (ne_of_gt (exponent_pos hn))]
    simp
  · rw [pStar_of_nonpos (not_lt.mp hw), indicator_of_notMem (show w ∉ Ioi (0 : ℝ) from hw)]

theorem pStar_antitone_price (hn : 2 ≤ n) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h : t₁ ≤ t₂) (w : ℝ) :
    pStar n t₂ w ≤ pStar n t₁ w := by
  by_cases hw : 0 < w
  · rw [pStar_of_pos hw, pStar_of_pos hw]
    apply max_le_max le_rfl
    have := Real.rpow_le_rpow (div_nonneg h₁ (le_of_lt hw))
      (div_le_div_of_nonneg_right h (le_of_lt hw)) (le_of_lt (exponent_pos hn))
    linarith
  · rw [pStar_of_nonpos (not_lt.mp hw), pStar_of_nonpos (not_lt.mp hw)]

theorem pStar_strictAnti_price (hn : 2 ≤ n) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h : t₁ < t₂)
    (hw : t₂ < w) : pStar n t₂ w < pStar n t₁ w := by
  have hw0 : 0 < w := lt_of_le_of_lt h₁ (lt_trans h hw)
  rw [pStar_of_lt hn (le_trans h₁ (le_of_lt h)) hw, pStar_of_lt hn h₁ (lt_trans h hw)]
  have := Real.rpow_lt_rpow (div_nonneg h₁ (le_of_lt hw0)) (div_lt_div_of_pos_right h hw0)
    (exponent_pos hn)
  linarith

theorem pStar_mono_value (hn : 2 ≤ n) (ht : 0 ≤ t) : Monotone (pStar n t) := by
  intro w₁ w₂ h
  by_cases hw : 0 < w₁
  · have hw2 : 0 < w₂ := lt_of_lt_of_le hw h
    rw [pStar_of_pos hw, pStar_of_pos hw2]
    apply max_le_max le_rfl
    have := Real.rpow_le_rpow (div_nonneg ht (le_of_lt hw2))
      (div_le_div_of_nonneg_left ht hw h) (le_of_lt (exponent_pos hn))
    linarith
  · rw [pStar_of_nonpos (not_lt.mp hw)]
    exact pStar_nonneg

theorem pStar_strictMonoOn_value (hn : 2 ≤ n) (ht : 0 < t) : StrictMonoOn (pStar n t) (Ioi t) := by
  intro w₁ hw₁ w₂ hw₂ h
  have hw₁' : t < w₁ := hw₁
  have hw₂' : t < w₂ := hw₂
  rw [pStar_of_lt hn (le_of_lt ht) hw₁', pStar_of_lt hn (le_of_lt ht) hw₂']
  have h0 : 0 < w₁ := lt_trans ht hw₁'
  have := Real.rpow_lt_rpow (div_nonneg (le_of_lt ht) (le_of_lt (lt_trans h0 h)))
    (div_lt_div_of_pos_left ht h0 h) (exponent_pos hn)
  linarith

theorem continuous_pStar_price (hn : 2 ≤ n) (w : ℝ) : Continuous (fun t => pStar n t w) := by
  by_cases hw : 0 < w
  · simp only [pStar_of_pos hw]
    have hc : Continuous (fun x : ℝ => x ^ (1 / ((n : ℝ) - 1))) :=
      Real.continuous_rpow_const (le_of_lt (exponent_pos hn))
    fun_prop
  · simp only [pStar_of_nonpos (not_lt.mp hw)]
    exact continuous_const

theorem measurable_pStar (n : ℕ) (t : ℝ) : Measurable (pStar n t) := by
  unfold pStar
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

end Pointwise

section Failure

variable {n : ℕ} {t w : ℝ}

theorem failure_eq (hn : 2 ≤ n) (ht : 0 ≤ t) (htw : t < w) :
    (1 - pStar n t w) ^ n = (t / w) ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
  rw [pStar_of_lt hn ht htw, sub_sub_cancel]
  rw [← Real.rpow_mul_natCast (div_nonneg ht (le_of_lt (lt_of_le_of_lt ht htw)))]
  congr 1
  ring

theorem failure_pos (hn : 2 ≤ n) (ht : 0 < t) (htw : t < w) :
    0 < (1 - pStar n t w) ^ n := by
  rw [failure_eq hn (le_of_lt ht) htw]
  exact Real.rpow_pos_of_pos (div_pos ht (lt_trans ht htw)) _

theorem success_pStar (hn : 2 ≤ n) (ht : 0 ≤ t) (htw : t < w) :
    success n (pStar n t w) = 1 - (t / w) ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
  unfold success
  rw [failure_eq hn ht htw]

theorem success_pStar_of_le (hn : 2 ≤ n) (ht : 0 ≤ t) (hwt : w ≤ t) :
    success n (pStar n t w) = 0 := by
  rw [pStar_eq_zero_of_le hn ht hwt]
  simp [success]

end Failure

section Multiplicity

variable {n : ℕ}

theorem success_lt_mul (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    success n p < (n : ℝ) * p := by
  have hn0 : 0 < n := by omega
  have hH := H_strict n hn 0 p hp0 hp1
  rw [H_zero n hn0] at hH
  rw [← H_mul n hn0 p]
  have hnp : 0 < (n : ℝ) * p := mul_pos (by exact_mod_cast hn0) hp0
  calc (n : ℝ) * p * H n p < (n : ℝ) * p * 1 := mul_lt_mul_of_pos_left hH hnp
    _ = _ := mul_one _

theorem success_le_mul (hn : 0 < n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    success n p ≤ (n : ℝ) * p := by
  rw [← H_mul n hn p]
  have hnp : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg n) hp0
  calc (n : ℝ) * p * H n p ≤ (n : ℝ) * p * 1 :=
        mul_le_mul_of_nonneg_left (H_bounds n hn p hp0 hp1).2 hnp
    _ = _ := mul_one _

theorem le_success (hn : 0 < n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : p ≤ success n p := by
  unfold success
  have := pow_le_of_le_one (sub_nonneg.mpr hp1) (by linarith) (Nat.pos_iff_ne_zero.mp hn)
  linarith

theorem success_nonneg (hn : 0 < n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ success n p :=
  le_trans hp0 (le_success hn hp0 hp1)

theorem conditional_multiplicity_gt_one (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    1 < (n : ℝ) * p / success n p := by
  have hS := success_pos n (by omega) p hp0 hp1
  rw [one_lt_div hS]
  exact success_lt_mul hn hp0 hp1

theorem served_multiplicity_gt_one (hn : 2 ≤ n) {t w : ℝ} (ht : 0 ≤ t) (htw : t < w) :
    1 < (n : ℝ) * pStar n t w / success n (pStar n t w) :=
  conditional_multiplicity_gt_one hn ((pStar_pos_iff hn ht).mpr htw) (pStar_le_one ht)

end Multiplicity

section Mixture

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem mixture_success_lt (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    (hpos : 0 < μ {ω | 0 < p ω}) :
    (∫ ω, success n (p ω) ∂μ) < (n : ℝ) * ∫ ω, p ω ∂μ := by
  have hpint := UnitInterval.integrable μ p hp hp0 hp1
  have hsint := UnitInterval.integrable_success μ p hp hp0 hp1 n
  have hdiff : Integrable (fun ω => (n : ℝ) * p ω - success n (p ω)) μ :=
    (hpint.const_mul (n : ℝ)).sub hsint
  have hnn : 0 ≤ᵐ[μ] (fun ω => (n : ℝ) * p ω - success n (p ω)) :=
    Eventually.of_forall fun ω => sub_nonneg.mpr (success_le_mul (by omega) (hp0 ω) (hp1 ω))
  have hsupp : {ω | 0 < p ω} ⊆ Function.support (fun ω => (n : ℝ) * p ω - success n (p ω)) := by
    intro ω hω
    exact (sub_pos.mpr (success_lt_mul hn hω (hp1 ω))).ne'
  have h := (integral_pos_iff_support_of_nonneg_ae hnn hdiff).mpr
    (lt_of_lt_of_le hpos (measure_mono hsupp))
  rw [integral_sub (hpint.const_mul (n : ℝ)) hsint, integral_const_mul] at h
  linarith

theorem jensen_coverage (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) (n : ℕ) {ρm : ℝ}
    (hmean : ∫ ω, p ω ∂μ = ρm) :
    (∫ ω, success n (p ω) ∂μ) ≤ 1 - (1 - ρm) ^ n := by
  have h := UnitInterval.success_mean_le μ p hp hp0 hp1 n
  rw [hmean] at h
  exact h

theorem jensen_multiplicity (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) {n : ℕ} (hn : 0 < n) {ρm : ℝ}
    (hmean : ∫ ω, p ω ∂μ = ρm) (hρ : 0 < ρm) :
    (n : ℝ) * ρm / (1 - (1 - ρm) ^ n) ≤ (n : ℝ) * ρm / ∫ ω, success n (p ω) ∂μ := by
  have hpint := UnitInterval.integrable μ p hp hp0 hp1
  have hsint := UnitInterval.integrable_success μ p hp hp0 hp1 n
  have hge : ρm ≤ ∫ ω, success n (p ω) ∂μ := by
    rw [← hmean]
    exact integral_mono hpint hsint (fun ω => le_success hn (hp0 ω) (hp1 ω))
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (Nat.cast_nonneg n) hρ.le
  · exact lt_of_lt_of_le hρ hge
  · exact jensen_coverage μ p hp hp0 hp1 n hmean

end Mixture

section Demand

variable (μW : Measure ℝ) [IsProbabilityMeasure μW] {n : ℕ}

theorem integrable_pStar {t : ℝ} (ht : 0 ≤ t) : Integrable (pStar n t) μW :=
  UnitInterval.integrable μW (pStar n t) (measurable_pStar n t)
    (fun _ => pStar_nonneg) (fun _ => pStar_le_one ht)

theorem integrable_success_pStar {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun w => success n (pStar n t w)) μW :=
  UnitInterval.integrable_success μW (pStar n t) (measurable_pStar n t)
    (fun _ => pStar_nonneg) (fun _ => pStar_le_one ht) n

omit [IsProbabilityMeasure μW] in
theorem demand_nonneg (t : ℝ) : 0 ≤ demand μW n t :=
  integral_nonneg (fun _ => pStar_nonneg)

omit [IsProbabilityMeasure μW] in

theorem demand_zero (hn : 2 ≤ n) : demand μW n 0 = μW.real (Ioi 0) := by
  unfold demand
  simp only [pStar_zero_price hn]
  exact integral_indicator_one measurableSet_Ioi

theorem demand_le_tail (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    demand μW n t ≤ μW.real (Ioi t) := by
  rw [← integral_indicator_one measurableSet_Ioi]
  apply integral_mono (integrable_pStar μW ht)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi)
  intro w
  by_cases hw : t < w
  · rw [indicator_of_mem (show w ∈ Ioi t from hw)]
    exact pStar_le_one ht
  · rw [indicator_of_notMem (show w ∉ Ioi t from hw), pStar_eq_zero_of_le hn ht (not_lt.mp hw)]

theorem tail_pos_of_demand_pos (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (hd : 0 < demand μW n t) :
    0 < μW.real (Ioi t) :=
  lt_of_lt_of_le hd (demand_le_tail μW hn ht)

theorem demand_antitone (hn : 2 ≤ n) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h : t₁ ≤ t₂) :
    demand μW n t₂ ≤ demand μW n t₁ :=
  integral_mono (integrable_pStar μW (le_trans h₁ h)) (integrable_pStar μW h₁)
    (fun w => pStar_antitone_price hn h₁ h w)

theorem demand_strictAnti (hn : 2 ≤ n) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h : t₁ < t₂)
    (htail : 0 < μW.real (Ioi t₂)) : demand μW n t₂ < demand μW n t₁ := by
  have hi₁ := integrable_pStar (n := n) μW h₁
  have hi₂ := integrable_pStar (n := n) μW (le_trans h₁ (le_of_lt h))
  have hnn : 0 ≤ᵐ[μW] (fun w => pStar n t₁ w - pStar n t₂ w) :=
    Eventually.of_forall fun w => sub_nonneg.mpr (pStar_antitone_price hn h₁ (le_of_lt h) w)
  have hsupp : Ioi t₂ ⊆ Function.support (fun w => pStar n t₁ w - pStar n t₂ w) := by
    intro w hw
    exact (sub_pos.mpr (pStar_strictAnti_price hn h₁ h hw)).ne'
  have hmeas : 0 < μW (Ioi t₂) :=
    pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp htail.ne')
  have hpos := (integral_pos_iff_support_of_nonneg_ae hnn (hi₁.sub hi₂)).mpr
    (lt_of_lt_of_le hmeas (measure_mono hsupp))
  rw [integral_sub hi₁ hi₂] at hpos
  unfold demand
  linarith

theorem demand_strictAntiOn (hn : 2 ≤ n) :
    StrictAntiOn (demand μW n) {t | 0 ≤ t ∧ 0 < μW.real (Ioi t)} :=
  fun _ ha _ hb hab => demand_strictAnti μW hn ha.1 hab hb.2

theorem continuousOn_demand (hn : 2 ≤ n) : ContinuousOn (demand μW n) (Ici 0) := by
  show ContinuousOn (fun t => ∫ w, pStar n t w ∂μW) (Ici 0)
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t _
    exact (measurable_pStar n t).aestronglyMeasurable
  · intro t ht
    refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg pStar_nonneg]
    exact pStar_le_one ht
  · exact integrable_const 1
  · exact Eventually.of_forall fun w => (continuous_pStar_price hn w).continuousOn

theorem continuousOn_coverage (hn : 2 ≤ n) : ContinuousOn (coverage μW n) (Ici 0) := by
  show ContinuousOn (fun t => ∫ w, success n (pStar n t w) ∂μW) (Ici 0)
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t _
    exact ((continuous_success n).measurable.comp (measurable_pStar n t)).aestronglyMeasurable
  · intro t ht
    refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (success_nonneg (by omega) pStar_nonneg (pStar_le_one ht))]
    exact success_le_one n _ (pStar_le_one ht)
  · exact integrable_const 1
  · exact Eventually.of_forall fun w =>
      ((continuous_success n).comp (continuous_pStar_price hn w)).continuousOn

theorem tendsto_demand_zero (hn : 2 ≤ n) :
    Tendsto (demand μW n) (𝓝[>] 0) (𝓝 (μW.real (Ioi 0))) := by
  have h : Tendsto (demand μW n) (𝓝[Ici 0] 0) (𝓝 (demand μW n 0)) :=
    continuousOn_demand μW hn 0 self_mem_Ici
  rw [demand_zero μW hn] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

theorem tendsto_demand_atTop (hn : 2 ≤ n) : Tendsto (demand μW n) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μW) (l := atTop)
    (F := fun t w => pStar n t w) (f := fun _ => (0 : ℝ)) (fun _ => 1)
    (Eventually.of_forall fun t => (measurable_pStar n t).aestronglyMeasurable) ?_
    (integrable_const 1) ?_
  · convert h using 1
    · rfl
    · simp
  · filter_upwards [eventually_ge_atTop 0] with t ht
    refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg pStar_nonneg]
    exact pStar_le_one ht
  · refine Eventually.of_forall fun w => ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max w 0)] with t ht
    exact (pStar_eq_zero_of_le hn (le_trans (le_max_right _ _) ht)
      (le_trans (le_max_left _ _) ht)).symm

theorem exists_capacity_root (hn : 2 ≤ n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < μW.real (Ioi 0)) :
    ∃ t, 0 < t ∧ demand μW n t = ρ := by
  obtain ⟨ε, hερ, hε⟩ : ∃ ε, ρ < demand μW n ε ∧ 0 < ε :=
    (((tendsto_demand_zero μW hn).eventually (lt_mem_nhds hρ)).and
      self_mem_nhdsWithin).exists
  obtain ⟨T, hTρ, hT⟩ : ∃ T, demand μW n T < ρ ∧ ε ≤ T :=
    (((tendsto_demand_atTop μW hn).eventually (gt_mem_nhds hρ0)).and
      (eventually_ge_atTop ε)).exists
  have hsub : Icc ε T ⊆ Ici 0 := fun x hx => le_trans (le_of_lt hε) hx.1
  obtain ⟨t, ht, hd⟩ := intermediate_value_Icc' hT ((continuousOn_demand μW hn).mono hsub)
    ⟨le_of_lt hTρ, le_of_lt hερ⟩
  exact ⟨t, lt_of_lt_of_le hε ht.1, hd⟩

theorem capacity_root_unique (hn : 2 ≤ n) {ρ t₁ t₂ : ℝ} (hρ0 : 0 < ρ)
    (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (hd₁ : demand μW n t₁ = ρ) (hd₂ : demand μW n t₂ = ρ) :
    t₁ = t₂ := by
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · have htail := tail_pos_of_demand_pos μW hn h₂ (hd₂ ▸ hρ0)
    have := demand_strictAnti μW hn h₁ h htail
    linarith
  · exact h
  · have htail := tail_pos_of_demand_pos μW hn h₁ (hd₁ ▸ hρ0)
    have := demand_strictAnti μW hn h₂ h htail
    linarith

theorem capacity_root (hn : 2 ≤ n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < μW.real (Ioi 0)) :
    ∃! t, 0 < t ∧ demand μW n t = ρ := by
  obtain ⟨t, ht, hd⟩ := exists_capacity_root μW hn hρ0 hρ
  exact ⟨t, ⟨ht, hd⟩, fun s hs => capacity_root_unique μW hn hρ0 (le_of_lt hs.1)
    (le_of_lt ht) hs.2 hd⟩

theorem demand_lt_positive_mass (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (hd : 0 < demand μW n t) :
    demand μW n t < μW.real (Ioi 0) := by
  rw [← demand_zero μW hn]
  exact demand_strictAnti μW hn le_rfl ht (tail_pos_of_demand_pos μW hn (le_of_lt ht) hd)

noncomputable def capRoot (μW : Measure ℝ) (n : ℕ) (ρ : ℝ) : ℝ := by
  classical
  exact if h : ∃ t, 0 < t ∧ demand μW n t = ρ then h.choose else 0

theorem capRoot_spec (hn : 2 ≤ n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < μW.real (Ioi 0)) :
    0 < capRoot μW n ρ ∧ demand μW n (capRoot μW n ρ) = ρ := by
  have h := exists_capacity_root μW hn hρ0 hρ
  rw [capRoot, dif_pos h]
  exact h.choose_spec

theorem capRoot_eq (hn : 2 ≤ n) {ρ t : ℝ} (hρ0 : 0 < ρ) (ht : 0 < t)
    (hd : demand μW n t = ρ) : capRoot μW n ρ = t := by
  have hρ : ρ < μW.real (Ioi 0) := hd ▸ demand_lt_positive_mass μW hn ht (hd ▸ hρ0)
  obtain ⟨h0, hd'⟩ := capRoot_spec μW hn hρ0 hρ
  exact capacity_root_unique μW hn hρ0 (le_of_lt h0) (le_of_lt ht) hd' hd

theorem continuousAt_capRoot (hn : 2 ≤ n) {ρ₀ : ℝ} (hρ0 : 0 < ρ₀)
    (hρ : ρ₀ < μW.real (Ioi 0)) : ContinuousAt (capRoot μW n) ρ₀ := by
  obtain ⟨ht0, hd0⟩ := capRoot_spec μW hn hρ0 hρ
  have htail0 : 0 < μW.real (Ioi (capRoot μW n ρ₀)) :=
    tail_pos_of_demand_pos μW hn (le_of_lt ht0) (by rw [hd0]; exact hρ0)
  have hgood : ∀ᶠ ρ in 𝓝 ρ₀, ρ ∈ Ioo 0 (μW.real (Ioi 0)) :=
    isOpen_Ioo.mem_nhds ⟨hρ0, hρ⟩
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro a ha
    have ha'0 : 0 ≤ max a (capRoot μW n ρ₀ / 2) :=
      le_trans (by positivity) (le_max_right _ _)
    have ha't : max a (capRoot μW n ρ₀ / 2) < capRoot μW n ρ₀ := max_lt ha (by linarith)
    have hda : ρ₀ < demand μW n (max a (capRoot μW n ρ₀ / 2)) :=
      by have := demand_strictAnti μW hn ha'0 ha't htail0; rwa [hd0] at this
    filter_upwards [hgood, gt_mem_nhds hda] with ρ hρ' hlt
    obtain ⟨hr0, hrd⟩ := capRoot_spec μW hn hρ'.1 hρ'.2
    by_contra hle
    have := demand_antitone μW hn (le_of_lt hr0)
      (le_trans (not_lt.mp hle) (le_max_left a (capRoot μW n ρ₀ / 2)))
    linarith
  · intro b hb
    have hb0 : 0 ≤ b := le_trans (le_of_lt ht0) (le_of_lt hb)
    have hdb : demand μW n b < ρ₀ := by
      by_contra hge
      have hpos : 0 < demand μW n b := lt_of_lt_of_le hρ0 (not_lt.mp hge)
      have := demand_strictAnti μW hn (le_of_lt ht0) hb (tail_pos_of_demand_pos μW hn hb0 hpos)
      linarith
    filter_upwards [hgood, lt_mem_nhds hdb] with ρ hρ' hgt
    obtain ⟨hr0, hrd⟩ := capRoot_spec μW hn hρ'.1 hρ'.2
    by_contra hle
    have := demand_antitone μW hn hb0 (not_lt.mp hle)
    linarith

end Demand

section Coverage

variable (μW : Measure ℝ) [IsProbabilityMeasure μW] {n : ℕ}

theorem demand_le_coverage (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    demand μW n t ≤ coverage μW n t :=
  integral_mono (integrable_pStar μW ht) (integrable_success_pStar μW ht)
    (fun _ => le_success (by omega) pStar_nonneg (pStar_le_one ht))

theorem coverage_lt_mul_demand (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (hd : 0 < demand μW n t) :
    coverage μW n t < (n : ℝ) * demand μW n t := by
  have htail := tail_pos_of_demand_pos μW hn ht hd
  have hset : {w | 0 < pStar n t w} = Ioi t := by
    ext w
    exact pStar_pos_iff hn ht
  have hpos : 0 < μW {w | 0 < pStar n t w} := by
    rw [hset]
    exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp htail.ne')
  exact mixture_success_lt μW (pStar n t) (measurable_pStar n t) (fun _ => pStar_nonneg)
    (fun _ => pStar_le_one ht) hn hpos

theorem coverage_lt_capacity (hn : 2 ≤ n) {t ρ : ℝ} (ht : 0 ≤ t) (hρ0 : 0 < ρ)
    (hd : demand μW n t = ρ) : coverage μW n t < (n : ℝ) * ρ := by
  have h := coverage_lt_mul_demand μW hn ht (hd ▸ hρ0)
  rwa [hd] at h

noncomputable def multiplicity (μW : Measure ℝ) (n : ℕ) (β : ℝ) : ℝ :=
  β / coverage μW n (capRoot μW n (β / n))

omit [IsProbabilityMeasure μW] in
theorem capacity_range (hn : 2 ≤ n) {β : ℝ} (hβ0 : 0 < β) (hβ : β < n * μW.real (Ioi 0)) :
    0 < β / n ∧ β / n < μW.real (Ioi 0) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨div_pos hβ0 hnR, (div_lt_iff₀' hnR).mpr hβ⟩

theorem coverage_root_pos (hn : 2 ≤ n) {β : ℝ} (hβ0 : 0 < β) (hβ : β < n * μW.real (Ioi 0)) :
    0 < coverage μW n (capRoot μW n (β / n)) := by
  obtain ⟨h0, h1⟩ := capacity_range μW hn hβ0 hβ
  obtain ⟨hr, hd⟩ := capRoot_spec μW hn h0 h1
  exact lt_of_lt_of_le (by rw [hd]; exact h0) (demand_le_coverage μW hn (le_of_lt hr))

theorem one_lt_multiplicity (hn : 2 ≤ n) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < n * μW.real (Ioi 0)) : 1 < multiplicity μW n β := by
  obtain ⟨h0, h1⟩ := capacity_range μW hn hβ0 hβ
  obtain ⟨hr, hd⟩ := capRoot_spec μW hn h0 h1
  have hQ := coverage_root_pos μW hn hβ0 hβ
  have hlt := coverage_lt_capacity μW hn (le_of_lt hr) h0 hd
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [mul_div_cancel₀ β hnR] at hlt
  exact (one_lt_div hQ).mpr hlt

theorem multiplicity_ge_jensen (hn : 2 ≤ n) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < n * μW.real (Ioi 0)) :
    β / success n (β / n) ≤ multiplicity μW n β := by
  obtain ⟨h0, h1⟩ := capacity_range μW hn hβ0 hβ
  obtain ⟨hr, hd⟩ := capRoot_spec μW hn h0 h1
  have hQ := coverage_root_pos μW hn hβ0 hβ
  have hJ := jensen_coverage μW (pStar n (capRoot μW n (β / n))) (measurable_pStar n _)
    (fun _ => pStar_nonneg) (fun _ => pStar_le_one (le_of_lt hr)) n hd
  exact div_le_div_of_nonneg_left (le_of_lt hβ0) hQ hJ

theorem continuousAt_multiplicity (hn : 2 ≤ n) {β₀ : ℝ} (hβ0 : 0 < β₀)
    (hβ : β₀ < n * μW.real (Ioi 0)) : ContinuousAt (multiplicity μW n) β₀ := by
  obtain ⟨h0, h1⟩ := capacity_range μW hn hβ0 hβ
  obtain ⟨hr, _⟩ := capRoot_spec μW hn h0 h1
  have hroot : ContinuousAt (fun β : ℝ => capRoot μW n (β / n)) β₀ :=
    ContinuousAt.comp (f := fun β : ℝ => β / n) (continuousAt_capRoot μW hn h0 h1)
      (continuousAt_id.div_const _)
  have hcov : ContinuousAt (coverage μW n) (capRoot μW n (β₀ / n)) :=
    (continuousOn_coverage μW hn).continuousAt (Ici_mem_nhds hr)
  exact continuousAt_id.div (ContinuousAt.comp (f := fun β : ℝ => capRoot μW n (β / n))
    hcov hroot) (coverage_root_pos μW hn hβ0 hβ).ne'

theorem tendsto_jensen_rhs (hn : 2 ≤ n) :
    Tendsto (fun β : ℝ => β / success n (β / n)) (𝓝 1) (𝓝 (1 / success n (1 / n))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS : 0 < success n (1 / n) := success_pos n (by omega) _ (by positivity)
    ((div_le_one hnR).mpr (by exact_mod_cast (show 1 ≤ n by omega)))
  have hcont : ContinuousAt (fun β : ℝ => β / success n (β / n)) 1 :=
    continuousAt_id.div ((continuous_success n).continuousAt.comp
      (f := fun β : ℝ => β / n) (continuousAt_id.div_const _)) hS.ne'
  exact hcont.tendsto

theorem eventually_multiplicity_gt (hn : 2 ≤ n) (h1 : 1 < n * μW.real (Ioi 0)) {c : ℝ}
    (hc : c < 1 / success n (1 / n)) : ∀ᶠ β in 𝓝 (1 : ℝ), c < multiplicity μW n β := by
  have hrange : ∀ᶠ β in 𝓝 (1 : ℝ), β ∈ Ioo 0 (n * μW.real (Ioi 0)) :=
    isOpen_Ioo.mem_nhds ⟨one_pos, h1⟩
  filter_upwards [(tendsto_jensen_rhs hn).eventually (lt_mem_nhds hc), hrange] with β hβ hβr
  exact lt_of_lt_of_le hβ (multiplicity_ge_jensen μW hn hβr.1 hβr.2)

theorem liminf_multiplicity_ge (hn : 2 ≤ n) (h1 : 1 < n * μW.real (Ioi 0)) :
    Tendsto (multiplicity μW n) (𝓝[>] 1) (𝓝 (multiplicity μW n 1)) ∧
    Filter.liminf (multiplicity μW n) (𝓝[>] 1) = multiplicity μW n 1 ∧
    1 / success n (1 / n) ≤ multiplicity μW n 1 := by
  have hT : Tendsto (multiplicity μW n) (𝓝[>] 1) (𝓝 (multiplicity μW n 1)) :=
    (continuousAt_multiplicity μW hn one_pos h1).tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨hT, hT.liminf_eq, multiplicity_ge_jensen μW hn one_pos h1⟩

theorem tendsto_jensen_bound :
    Tendsto (fun n : ℕ => 1 / success n (1 / n)) atTop (𝓝 (1 / (1 - Real.exp (-1)))) := by
  have h := Real.tendsto_one_add_div_pow_exp (-1)
  have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h' : Tendsto (fun n : ℕ => 1 / (1 - (1 + (-1) / (n : ℝ)) ^ n)) atTop
      (𝓝 (1 / (1 - Real.exp (-1)))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub h) (by linarith)
  refine h'.congr fun n => ?_
  simp only [success, neg_div, ← sub_eq_add_neg]

theorem multiplicity_one_gt (hn : 2 ≤ n) (h1 : 1 < n * μW.real (Ioi 0))
    (hnc : ∀ c : ℝ, ¬ (∀ᵐ w ∂μW, w = c)) :
    1 / success n (1 / n) < multiplicity μW n 1 := by
  obtain ⟨h0, hP⟩ := capacity_range μW hn one_pos h1
  obtain ⟨hr, hd⟩ := capRoot_spec μW hn h0 hP
  have hQ := coverage_root_pos μW hn one_pos h1
  set t := capRoot μW n (1 / n) with ht_def
  rcases UnitInterval.strict_success_or_constant μW (pStar n t) (measurable_pStar n t)
      (fun _ => pStar_nonneg) (fun _ => pStar_le_one (le_of_lt hr)) n hn with hconst | hstrict
  · exfalso
    have hc : ∀ᵐ w ∂μW, pStar n t w = 1 / n := by
      filter_upwards [hconst] with w hw
      exact hw.trans hd
    have hserved : ∀ᵐ w ∂μW, t < w ∧ pStar n t w = 1 / n := by
      filter_upwards [hc] with w hw
      exact ⟨(pStar_pos_iff hn (le_of_lt hr)).mp (hw ▸ h0), hw⟩
    obtain ⟨w₀, hw₀t, hw₀⟩ := hserved.exists
    apply hnc w₀
    filter_upwards [hserved] with w hw
    exact (pStar_strictMonoOn_value hn hr).injOn hw.1 hw₀t (hw.2.trans hw₀.symm)
  · have hd' : demand μW n t = ∫ w, pStar n t w ∂μW := rfl
    rw [← hd', hd] at hstrict
    change coverage μW n t < success n (1 / n) at hstrict
    unfold multiplicity
    exact one_div_lt_one_div_of_lt hQ hstrict

theorem not_ae_const_of_noAtoms [NullSingletonClass μW] (c : ℝ) : ¬ (∀ᵐ w ∂μW, w = c) := by
  intro h
  have h0 : μW {c}ᶜ = 0 := by
    rw [ae_iff] at h
    simpa [compl_def] using h
  rw [prob_compl_eq_one_sub (measurableSet_singleton c), measure_singleton] at h0
  simp at h0

theorem strict_boundary_gap [NullSingletonClass μW] (hn : 2 ≤ n) (h1 : 1 < n * μW.real (Ioi 0)) :
    Filter.liminf (multiplicity μW n) (𝓝[>] 1) = multiplicity μW n 1 ∧
    1 / success n (1 / n) < multiplicity μW n 1 :=
  ⟨(liminf_multiplicity_ge μW hn h1).2.1,
    multiplicity_one_gt μW hn h1 (not_ae_const_of_noAtoms μW)⟩

theorem positive_mass_of_ae_pos (hpos : ∀ᵐ w ∂μW, 0 < w) : μW.real (Ioi 0) = 1 := by
  have hset : {w : ℝ | ¬ 0 < w} = (Ioi 0)ᶜ := by
    ext w
    simp
  have h0 : μW (Ioi 0)ᶜ = 0 := by
    rw [ae_iff, hset] at hpos
    exact hpos
  rw [prob_compl_eq_zero_iff measurableSet_Ioi] at h0
  simp [measureReal_def, h0]

theorem one_lt_of_ae_pos (hn : 2 ≤ n) (hpos : ∀ᵐ w ∂μW, 0 < w) :
    1 < n * μW.real (Ioi 0) := by
  rw [positive_mass_of_ae_pos μW hpos, mul_one]
  exact_mod_cast (show 1 < n by omega)

theorem po_jensen_limit (hn : 2 ≤ n) (hpos : ∀ᵐ w ∂μW, 0 < w) :
    (∀ β : ℝ, 0 < β → β < n → β / success n (β / n) ≤ multiplicity μW n β) ∧
    Tendsto (multiplicity μW n) (𝓝[>] 1) (𝓝 (multiplicity μW n 1)) ∧
    Filter.liminf (multiplicity μW n) (𝓝[>] 1) = multiplicity μW n 1 ∧
    1 / success n (1 / n) ≤ multiplicity μW n 1 := by
  have h1 := one_lt_of_ae_pos μW hn hpos
  refine ⟨fun β hβ0 hβ => multiplicity_ge_jensen μW hn hβ0 ?_,
    liminf_multiplicity_ge μW hn h1⟩
  rw [positive_mass_of_ae_pos μW hpos, mul_one]
  exact hβ

theorem po_jensen_strict [NullSingletonClass μW] (hn : 2 ≤ n) (hpos : ∀ᵐ w ∂μW, 0 < w) :
    1 / success n (1 / n) < Filter.liminf (multiplicity μW n) (𝓝[>] 1) := by
  obtain ⟨hlim, hgap⟩ := strict_boundary_gap μW hn (one_lt_of_ae_pos μW hn hpos)
  rw [hlim]
  exact hgap

end Coverage

end Limit
end PayOnce
end FCAppendix
