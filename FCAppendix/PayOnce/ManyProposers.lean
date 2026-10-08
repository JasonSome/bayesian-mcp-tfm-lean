import FCAppendix.PayOnce.Polynomial
import FCAppendix.Probability.IndependentCounts

namespace FCAppendix
namespace PayOnce
namespace ManyProposers

open MeasureTheory Filter Topology Set

noncomputable def logPlus (x : ℝ) : ℝ := Real.log (max 1 x)

theorem max_one_pos (x : ℝ) : 0 < max 1 x := lt_of_lt_of_le one_pos (le_max_left _ _)

theorem logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x := Real.log_nonneg (le_max_left _ _)

theorem logPlus_of_le_one {x : ℝ} (hx : x ≤ 1) : logPlus x = 0 := by
  simp [logPlus, max_eq_left hx]

theorem logPlus_of_one_le {x : ℝ} (hx : 1 ≤ x) : logPlus x = Real.log x := by
  simp [logPlus, max_eq_right hx]

theorem logPlus_eq_max_log {x : ℝ} (hx : 0 < x) : logPlus x = max 0 (Real.log x) := by
  rcases le_total x 1 with h | h
  · rw [logPlus_of_le_one h, max_eq_left (Real.log_nonpos hx.le h)]
  · rw [logPlus_of_one_le h, max_eq_right (Real.log_nonneg h)]

theorem logPlus_pos {x : ℝ} (hx : 1 < x) : 0 < logPlus x := by
  rw [logPlus_of_one_le hx.le]
  exact Real.log_pos hx

theorem continuous_logPlus : Continuous logPlus :=
  (continuous_const.max continuous_id).log (fun x => (max_one_pos x).ne')

theorem logPlus_mono : Monotone logPlus := fun _ _ hxy =>
  Real.log_le_log (max_one_pos _) (max_le_max le_rfl hxy)

theorem logPlus_mul_le (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    logPlus (x * y) ≤ logPlus x + logPlus y := by
  unfold logPlus
  rw [← Real.log_mul (max_one_pos x).ne' (max_one_pos y).ne']
  apply Real.log_le_log (max_one_pos _)
  apply max_le
  · nlinarith [le_max_left 1 x, le_max_left 1 y]
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hy (max_one_pos x).le

theorem div_le_one_of_nonpos {T w : ℝ} (hT : 0 < T) (hw : w ≤ 0) : w / T ≤ 1 := by
  have := div_nonpos_of_nonpos_of_nonneg hw hT.le
  linarith

theorem logPlus_div_le {T : ℝ} (hT : 0 < T) (w : ℝ) :
    logPlus (w / T) ≤ logPlus w + logPlus T⁻¹ := by
  rcases le_or_gt w 0 with hw | hw
  · rw [logPlus_of_le_one (div_le_one_of_nonpos hT hw)]
    exact add_nonneg (logPlus_nonneg _) (logPlus_nonneg _)
  · rw [div_eq_mul_inv]
    exact logPlus_mul_le w (inv_nonneg.mpr hT.le)

theorem logPlus_div_eq_zero {T w : ℝ} (hT : 0 < T) (hw : w ≤ T) : logPlus (w / T) = 0 :=
  logPlus_of_le_one ((div_le_one hT).mpr hw)

theorem logPlus_div_anti {T₁ T₂ : ℝ} (h1 : 0 < T₁) (h12 : T₁ ≤ T₂) (w : ℝ) :
    logPlus (w / T₂) ≤ logPlus (w / T₁) := by
  rcases le_or_gt w 0 with hw | hw
  · rw [logPlus_of_le_one (div_le_one_of_nonpos (h1.trans_le h12) hw)]
    exact logPlus_nonneg _
  · exact logPlus_mono (div_le_div_of_nonneg_left hw.le h1 h12)

theorem logPlus_div_strict {T₁ T₂ w : ℝ} (h1 : 0 < T₁) (h12 : T₁ < T₂) (hw : T₁ < w) :
    logPlus (w / T₂) < logPlus (w / T₁) := by
  have hw0 : 0 < w := h1.trans hw
  have hgt : 1 < w / T₁ := (one_lt_div h1).mpr hw
  rw [logPlus_of_one_le hgt.le]
  rcases le_total (w / T₂) 1 with h | h
  · rw [logPlus_of_le_one h]
    exact Real.log_pos hgt
  · rw [logPlus_of_one_le h]
    exact Real.log_lt_log (by linarith) (div_lt_div_of_pos_left hw0 h1 h12)

theorem continuous_logPlus_div (T : ℝ) : Continuous (fun w => logPlus (w / T)) :=
  continuous_logPlus.comp (continuous_id.div_const T)

section LogDemand

variable (μW : Measure ℝ)

noncomputable def logDemand (T : ℝ) : ℝ := ∫ w, logPlus (w / T) ∂μW

variable [IsFiniteMeasure μW]

theorem integrable_logPlus_div (hlog : Integrable logPlus μW) {T : ℝ} (hT : 0 < T) :
    Integrable (fun w => logPlus (w / T)) μW := by
  refine Integrable.mono' (hlog.add (integrable_const (logPlus T⁻¹)))
    (continuous_logPlus_div T).aestronglyMeasurable (Eventually.of_forall (fun w => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (logPlus_nonneg _)]
  exact logPlus_div_le hT w

omit [IsFiniteMeasure μW] in
theorem logDemand_nonneg (T : ℝ) : 0 ≤ logDemand μW T :=
  integral_nonneg (fun w => logPlus_nonneg (w / T))

theorem logDemand_anti (hlog : Integrable logPlus μW) {T₁ T₂ : ℝ} (h1 : 0 < T₁)
    (h12 : T₁ ≤ T₂) : logDemand μW T₂ ≤ logDemand μW T₁ :=
  integral_mono (integrable_logPlus_div μW hlog (h1.trans_le h12))
    (integrable_logPlus_div μW hlog h1) (fun w => logPlus_div_anti h1 h12 w)

theorem measure_Ioi_pos_of_logDemand_pos (hlog : Integrable logPlus μW) {T : ℝ}
    (hT : 0 < T) (hpos : 0 < logDemand μW T) : 0 < μW (Ioi T) := by
  have h := (integral_pos_iff_support_of_nonneg (fun w => logPlus_nonneg (w / T))
    (integrable_logPlus_div μW hlog hT)).mp hpos
  refine lt_of_lt_of_le h (measure_mono ?_)
  intro w hw
  by_contra hle
  exact (Function.mem_support.mp hw) (logPlus_div_eq_zero hT (not_lt.mp hle))

theorem logDemand_strict (hlog : Integrable logPlus μW) {T₁ T₂ : ℝ} (h1 : 0 < T₁)
    (h12 : T₁ < T₂) (hpos : 0 < logDemand μW T₁) : logDemand μW T₂ < logDemand μW T₁ := by
  have hI1 := integrable_logPlus_div μW hlog h1
  have hI2 := integrable_logPlus_div μW hlog (h1.trans h12)
  have hdiff : 0 < ∫ w, (logPlus (w / T₁) - logPlus (w / T₂)) ∂μW := by
    rw [integral_pos_iff_support_of_nonneg
      (fun w => sub_nonneg.mpr (logPlus_div_anti h1 h12.le w)) (hI1.sub hI2)]
    refine lt_of_lt_of_le (measure_Ioi_pos_of_logDemand_pos μW hlog h1 hpos) (measure_mono ?_)
    intro w hw
    exact Function.mem_support.mpr (sub_pos.mpr (logPlus_div_strict h1 h12 hw)).ne'
  rw [integral_sub hI1 hI2] at hdiff
  unfold logDemand
  linarith

theorem continuousOn_logDemand_Ici (hlog : Integrable logPlus μW) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (logDemand μW) (Ici a) := by
  refine continuousOn_of_dominated (bound := fun w => logPlus w + logPlus a⁻¹)
    (fun T _ => (continuous_logPlus_div T).aestronglyMeasurable) ?_
    (hlog.add (integrable_const _)) (Eventually.of_forall (fun w => ?_))
  · intro T hT
    refine Eventually.of_forall (fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (logPlus_nonneg _)]
    exact (logPlus_div_anti ha (mem_Ici.mp hT) w).trans (logPlus_div_le ha w)
  · refine continuous_logPlus.comp_continuousOn
      (continuousOn_const.div continuousOn_id (fun T hT => ?_))
    exact (ha.trans_le (mem_Ici.mp hT)).ne'

theorem continuousOn_logDemand (hlog : Integrable logPlus μW) :
    ContinuousOn (logDemand μW) (Ioi 0) := by
  intro T hT
  have hT0 : 0 < T := hT
  have h := continuousOn_logDemand_Ici μW hlog (half_pos hT0)
  exact (h.continuousAt (Ici_mem_nhds (half_lt_self hT0))).continuousWithinAt

omit [IsFiniteMeasure μW] in

theorem tendsto_logDemand_atTop (hlog : Integrable logPlus μW) :
    Tendsto (logDemand μW) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μW) (l := atTop)
    (F := fun T w => logPlus (w / T)) (f := fun _ => 0) logPlus
    (Eventually.of_forall (fun T => (continuous_logPlus_div T).aestronglyMeasurable)) ?_ hlog ?_
  · convert h using 1
    · rfl
    · simp
  · filter_upwards [eventually_ge_atTop 1] with T hT
    refine Eventually.of_forall (fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (logPlus_nonneg _)]
    simpa using logPlus_div_anti one_pos hT w
  · refine Eventually.of_forall (fun w => ?_)
    have h0 : Tendsto (fun T : ℝ => w / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have := (continuous_logPlus.tendsto 0).comp h0
    simpa [Function.comp_def, logPlus_of_le_one zero_le_one] using this

omit [IsFiniteMeasure μW] in
theorem exists_pos_measure_Ioi (hpos : 0 < μW (Ioi 0)) : ∃ ε > 0, 0 < μW (Ioi ε) := by
  by_contra h
  push Not at h
  have hU : Ioi (0 : ℝ) = ⋃ k : ℕ, Ioi (1 / ((k : ℝ) + 1)) := by
    ext x
    simp only [mem_Ioi, mem_iUnion]
    constructor
    · intro hx
      exact exists_nat_one_div_lt hx
    · rintro ⟨k, hk⟩
      exact lt_trans (by positivity) hk
  have h0 : μW (Ioi 0) = 0 := by
    rw [hU]
    exact measure_iUnion_null (fun k => le_antisymm (h _ (by positivity)) (zero_le))
  exact hpos.ne' h0

theorem tendsto_logDemand_nhdsGT_zero (hlog : Integrable logPlus μW) (hpos : 0 < μW (Ioi 0)) :
    Tendsto (logDemand μW) (𝓝[>] 0) atTop := by
  obtain ⟨ε, hε, hμε⟩ := exists_pos_measure_Ioi μW hpos
  have hc : 0 < μW.real (Ioi ε) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hμε.ne' (measure_ne_top _ _)
  have hlim : Tendsto (fun T => μW.real (Ioi ε) * Real.log (ε / T)) (𝓝[>] 0) atTop := by
    refine Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp ?_)
    exact (Tendsto.const_mul_atTop hε tendsto_inv_nhdsGT_zero).congr
      (fun T => (div_eq_mul_inv ε T).symm)
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT hε] with T hT
  have hT0 : 0 < T := hT.1
  have hind : ∀ w, (Ioi ε).indicator (fun _ => Real.log (ε / T)) w ≤ logPlus (w / T) := by
    intro w
    by_cases hw : w ∈ Ioi ε
    · rw [indicator_of_mem hw]
      have h1 : 1 ≤ ε / T := (one_le_div hT0).mpr hT.2.le
      calc Real.log (ε / T) = logPlus (ε / T) := (logPlus_of_one_le h1).symm
        _ ≤ logPlus (w / T) :=
          logPlus_mono (div_le_div_of_nonneg_right (le_of_lt (mem_Ioi.mp hw)) hT0.le)
    · rw [indicator_of_notMem hw]
      exact logPlus_nonneg _
  have h := integral_mono ((integrable_const _).indicator measurableSet_Ioi)
    (integrable_logPlus_div μW hlog hT0) hind
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul] at h
  exact h

theorem existsUnique_logRoot (hlog : Integrable logPlus μW) (hpos : 0 < μW (Ioi 0))
    {β : ℝ} (hβ : 0 < β) :
    ∃! T, 0 < T ∧ ∫ w, logPlus (w / T) ∂μW = β := by
  obtain ⟨a, ha, ha0⟩ :=
    (((tendsto_logDemand_nhdsGT_zero μW hlog hpos).eventually_gt_atTop β).and
      self_mem_nhdsWithin).exists
  obtain ⟨b, hb, hb0⟩ :=
    (((tendsto_order.1 (tendsto_logDemand_atTop μW hlog)).2 β hβ).and
      (eventually_gt_atTop 0)).exists
  have ha0' : 0 < a := ha0
  have hab : a < b := by
    by_contra hba
    have := logDemand_anti μW hlog hb0 (not_lt.mp hba)
    linarith
  have hcont : ContinuousOn (logDemand μW) (Icc a b) :=
    (continuousOn_logDemand μW hlog).mono (fun x hx => lt_of_lt_of_le ha0' hx.1)
  obtain ⟨T, hTab, hT⟩ := intermediate_value_Icc' hab.le hcont ⟨hb.le, ha.le⟩
  refine ⟨T, ⟨lt_of_lt_of_le ha0' hTab.1, hT⟩, ?_⟩
  rintro y ⟨hy0, hy⟩
  have hT0 : 0 < T := lt_of_lt_of_le ha0' hTab.1
  change logDemand μW y = β at hy
  rcases lt_trichotomy y T with h | h | h
  · have := logDemand_strict μW hlog hy0 h (by rw [hy]; exact hβ)
    rw [hy, hT] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := logDemand_strict μW hlog hT0 h (by rw [hT]; exact hβ)
    rw [hy, hT] at this
    exact absurd this (lt_irrefl _)

end LogDemand

noncomputable def pStar (n : ℕ) (t w : ℝ) : ℝ :=
  if 0 < w then max 0 (1 - (t / w) ^ (1 / ((n : ℝ) - 1))) else 0

theorem nat_sub_one_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) - 1 := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem pStar_eq_exp {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (w : ℝ) :
    pStar n t w = 1 - Real.exp (-(logPlus (w / t) / ((n : ℝ) - 1))) := by
  have hn1 := nat_sub_one_pos hn
  unfold pStar
  split_ifs with hw
  · rw [Real.rpow_def_of_pos (div_pos ht hw)]
    have hlog : Real.log (t / w) = -Real.log (w / t) := by
      rw [← Real.log_inv, inv_div]
    rw [hlog]
    rcases le_total w t with hwt | hwt
    · have h1 : w / t ≤ 1 := (div_le_one ht).mpr hwt
      rw [logPlus_of_le_one h1]
      have h0 : 0 ≤ -Real.log (w / t) * (1 / ((n : ℝ) - 1)) :=
        mul_nonneg (neg_nonneg.mpr (Real.log_nonpos (div_pos hw ht).le h1)) (by positivity)
      have hexp := Real.one_le_exp h0
      rw [max_eq_left (by linarith)]
      simp
    · have h1 : 1 ≤ w / t := (one_le_div ht).mpr hwt
      rw [logPlus_of_one_le h1]
      have h0 : -Real.log (w / t) * (1 / ((n : ℝ) - 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.log_nonneg h1)) (by positivity)
      have hexp : Real.exp (-Real.log (w / t) * (1 / ((n : ℝ) - 1))) ≤ 1 :=
        Real.exp_le_one_iff.mpr h0
      rw [max_eq_right (by linarith)]
      congr 2
      ring
  · rw [logPlus_of_le_one (div_le_one_of_nonpos ht (not_lt.mp hw))]
    simp

theorem pStar_nonneg (n : ℕ) (t w : ℝ) : 0 ≤ pStar n t w := by
  unfold pStar
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem pStar_le_one (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (w : ℝ) : pStar n t w ≤ 1 := by
  unfold pStar
  split_ifs with hw
  · exact max_le zero_le_one
      (by linarith [Real.rpow_nonneg (div_nonneg ht hw.le) (1 / ((n : ℝ) - 1))])
  · exact zero_le_one

theorem pStar_eq_zero {n : ℕ} (hn : 2 ≤ n) {t w : ℝ} (ht : 0 < t) (hw : w ≤ t) :
    pStar n t w = 0 := by
  rw [pStar_eq_exp hn ht, logPlus_div_eq_zero ht hw]
  simp

theorem pStar_pos {n : ℕ} (hn : 2 ≤ n) {t w : ℝ} (ht : 0 < t) (hw : t < w) :
    0 < pStar n t w := by
  rw [pStar_eq_exp hn ht]
  have hL : 0 < logPlus (w / t) / ((n : ℝ) - 1) :=
    div_pos (logPlus_pos ((one_lt_div ht).mpr hw)) (nat_sub_one_pos hn)
  have : Real.exp (-(logPlus (w / t) / ((n : ℝ) - 1))) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos hL)
  linarith

theorem continuous_pStar {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    Continuous (pStar n t) := by
  have h : pStar n t = fun w => 1 - Real.exp (-(logPlus (w / t) / ((n : ℝ) - 1))) :=
    funext (pStar_eq_exp hn ht)
  rw [h]
  exact continuous_const.sub (Real.continuous_exp.comp
    (((continuous_logPlus_div t).div_const _).neg))

theorem pStar_anti {n : ℕ} (hn : 2 ≤ n) {t₁ t₂ : ℝ} (h1 : 0 < t₁) (h12 : t₁ ≤ t₂) (w : ℝ) :
    pStar n t₂ w ≤ pStar n t₁ w := by
  rw [pStar_eq_exp hn h1, pStar_eq_exp hn (h1.trans_le h12)]
  have := div_le_div_of_nonneg_right (logPlus_div_anti h1 h12 w) (nat_sub_one_pos hn).le
  have := Real.exp_le_exp.mpr (neg_le_neg this)
  linarith

theorem pStar_mono_value {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) {w₁ w₂ : ℝ}
    (hw : w₁ ≤ w₂) : pStar n t w₁ ≤ pStar n t w₂ := by
  rw [pStar_eq_exp hn ht, pStar_eq_exp hn ht]
  have := div_le_div_of_nonneg_right (logPlus_mono (div_le_div_of_nonneg_right hw ht.le))
    (nat_sub_one_pos hn).le
  have := Real.exp_le_exp.mpr (neg_le_neg this)
  linarith

theorem nat_mul_pStar_of_lt {n : ℕ} (hn : 2 ≤ n) {t w : ℝ} (ht : 0 < t) (hw : t < w) :
    (n : ℝ) * pStar n t w = (n : ℝ) * (1 - Real.exp (-(Real.log (w / t) / ((n : ℝ) - 1)))) := by
  rw [pStar_eq_exp hn ht, logPlus_of_one_le ((one_le_div ht).mpr hw.le)]

theorem one_sub_pStar_pow {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (w : ℝ) :
    (1 - pStar n t w) ^ n = Real.exp (-((n : ℝ) * (logPlus (w / t) / ((n : ℝ) - 1)))) := by
  rw [pStar_eq_exp hn ht, sub_sub_cancel, ← Real.exp_nat_mul]
  ring_nf

theorem integrable_pStar (μW : Measure ℝ) [IsFiniteMeasure μW] {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 0 < t) : Integrable (pStar n t) μW := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (continuous_pStar hn ht).aestronglyMeasurable
    (Eventually.of_forall (fun w => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (pStar_nonneg n t w)]
  exact pStar_le_one n ht.le w

theorem integral_pStar_anti (μW : Measure ℝ) [IsFiniteMeasure μW] {n : ℕ} (hn : 2 ≤ n)
    {t₁ t₂ : ℝ} (h1 : 0 < t₁) (h12 : t₁ ≤ t₂) :
    ∫ w, pStar n t₂ w ∂μW ≤ ∫ w, pStar n t₁ w ∂μW :=
  integral_mono (integrable_pStar μW hn (h1.trans_le h12)) (integrable_pStar μW hn h1)
    (fun w => pStar_anti hn h1 h12 w)

theorem one_sub_exp_neg_le {x : ℝ} : 1 - Real.exp (-x) ≤ x := by
  have := Real.add_one_le_exp (-x)
  linarith

theorem div_one_add_le_one_sub_exp_neg {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have h1 : 0 < 1 + x := by linarith
  have hexp : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ h1 (by linarith [Real.add_one_le_exp x])
  have : x / (1 + x) = 1 - 1 / (1 + x) := by field_simp; ring
  linarith

theorem tendsto_inv_nat_sub_one :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) - 1)) atTop (𝓝 0) := by
  refine tendsto_const_nhds.div_atTop ?_
  simpa [sub_eq_add_neg] using
    tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop

theorem tendsto_nat_div_nat_sub_one :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_nat_sub_one
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have := (nat_sub_one_pos hn).ne'
  field_simp
  ring

theorem tendsto_nat_mul_one_sub_exp {a : ℕ → ℝ} {L : ℝ} (ha0 : ∀ᶠ n in atTop, 0 ≤ a n)
    (ha : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - Real.exp (-(a n / ((n : ℝ) - 1))))) atTop (𝓝 L) := by
  have hx : Tendsto (fun n : ℕ => a n / ((n : ℝ) - 1)) atTop (𝓝 0) := by
    have := ha.mul tendsto_inv_nat_sub_one
    rw [mul_zero] at this
    exact this.congr (fun n => by ring)
  have hup : Tendsto (fun n : ℕ => (n : ℝ) * (a n / ((n : ℝ) - 1))) atTop (𝓝 L) := by
    have := tendsto_nat_div_nat_sub_one.mul ha
    rw [one_mul] at this
    exact this.congr (fun n => by ring)
  have hlow : Tendsto (fun n : ℕ => (n : ℝ) * (a n / ((n : ℝ) - 1)) /
      (1 + a n / ((n : ℝ) - 1))) atTop (𝓝 L) := by
    have := hup.div (tendsto_const_nhds.add hx) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    convert this using 1 <;> first | rfl | simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [ha0, eventually_ge_atTop 2] with n hn0 hn2
    have hx0 : 0 ≤ a n / ((n : ℝ) - 1) := div_nonneg hn0 (nat_sub_one_pos hn2).le
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_one_add_le_one_sub_exp_neg hx0) (Nat.cast_nonneg n)
  · filter_upwards with n
    exact mul_le_mul_of_nonneg_left one_sub_exp_neg_le (Nat.cast_nonneg n)

theorem tendsto_nat_mul_one_sub_exp_const {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - Real.exp (-(L / ((n : ℝ) - 1))))) atTop (𝓝 L) :=
  tendsto_nat_mul_one_sub_exp (Eventually.of_forall (fun _ => hL)) tendsto_const_nhds

theorem nat_mul_one_sub_exp_le {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 ≤ L) :
    (n : ℝ) * (1 - Real.exp (-(L / ((n : ℝ) - 1)))) ≤ 2 * L := by
  have hn1 := nat_sub_one_pos hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) * (1 - Real.exp (-(L / ((n : ℝ) - 1))))
      ≤ (n : ℝ) * (L / ((n : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left one_sub_exp_neg_le (Nat.cast_nonneg n)
    _ = (n : ℝ) / ((n : ℝ) - 1) * L := by ring
    _ ≤ 2 * L := by
        apply mul_le_mul_of_nonneg_right _ hL
        rw [div_le_iff₀ hn1]
        linarith

theorem nat_mul_one_sub_exp_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (n : ℝ) * (1 - Real.exp (-x)) := by
  have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  exact mul_nonneg (Nat.cast_nonneg n) (by linarith)

section Root

variable (μW : Measure ℝ) [IsFiniteMeasure μW]

theorem tendsto_nat_mul_integral_pStar (hlog : Integrable logPlus μW) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ w, pStar n T w ∂μW) atTop
      (𝓝 (∫ w, logPlus (w / T) ∂μW)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μW) (l := atTop)
    (F := fun (n : ℕ) w => (n : ℝ) * pStar n T w) (f := fun w => logPlus (w / T))
    (fun w => 2 * logPlus (w / T)) ?_ ?_ ((integrable_logPlus_div μW hlog hT).const_mul 2) ?_
  · exact h.congr (fun n => integral_const_mul _ _)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact (continuous_const.mul (continuous_pStar hn hT)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 2] with n hn
    refine Eventually.of_forall (fun w => ?_)
    rw [pStar_eq_exp hn hT, Real.norm_eq_abs, abs_of_nonneg (nat_mul_one_sub_exp_nonneg n
      (div_nonneg (logPlus_nonneg _) (nat_sub_one_pos hn).le))]
    exact nat_mul_one_sub_exp_le hn (logPlus_nonneg _)
  · refine Eventually.of_forall (fun w => ?_)
    refine (tendsto_nat_mul_one_sub_exp_const (logPlus_nonneg (w / T))).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [pStar_eq_exp hn hT]

omit [IsFiniteMeasure μW] in

theorem abs_nat_mul_one_sub_exp_sub_le {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    |(n : ℝ) * (1 - Real.exp (-(x / ((n : ℝ) - 1)))) - x| ≤
      x / ((n : ℝ) - 1) + min x (x ^ 2 / ((n : ℝ) - 1)) := by
  have hm := nat_sub_one_pos hn
  have hm1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set m : ℝ := (n : ℝ) - 1 with hmdef
  have hnm : (n : ℝ) = m + 1 := by rw [hmdef]; ring
  set y := x / m with hydef
  have hy : 0 ≤ y := div_nonneg hx hm.le
  have hxy : x = m * y := by rw [hydef]; field_simp
  set L := 1 - Real.exp (-y) with hLdef
  have hup : L ≤ y := one_sub_exp_neg_le
  have hlow : y / (1 + y) ≤ L := div_one_add_le_one_sub_exp_neg hy
  have hlow' : y ≤ L * (1 + y) := by
    have h1 : 0 < 1 + y := by linarith
    rwa [div_le_iff₀ h1] at hlow
  have hL0 : 0 ≤ L := le_trans (div_nonneg hy (by linarith)) hlow
  have hmin0 : 0 ≤ min x (x ^ 2 / m) := le_min hx (by positivity)
  rw [hnm, abs_le]
  constructor
  · have h1 : m * y - (m + 1) * L ≤ m * y := by nlinarith
    have h2 : m * y - (m + 1) * L ≤ m * y ^ 2 := by nlinarith
    have h3 : x ^ 2 / m = m * y ^ 2 := by rw [hxy]; field_simp
    have h4 : m * y - (m + 1) * L ≤ min x (x ^ 2 / m) := by
      rw [h3, hxy]
      exact le_min h1 h2
    rw [hxy]
    rw [hxy] at h4
    linarith
  · rw [hxy] at hmin0 ⊢
    have := mul_le_mul_of_nonneg_left hup (by linarith : (0 : ℝ) ≤ m + 1)
    linarith

theorem tendstoUniformlyOn_nat_mul_integral_pStar (hlog : Integrable logPlus μW) {a : ℝ}
    (ha : 0 < a) :
    TendstoUniformlyOn (fun (n : ℕ) T => (n : ℝ) * ∫ w, pStar n T w ∂μW) (logDemand μW)
      atTop (Ici a) := by
  set h : ℕ → ℝ → ℝ := fun n w => logPlus (w / a) / ((n : ℝ) - 1) +
    min (logPlus (w / a)) (logPlus (w / a) ^ 2 / ((n : ℝ) - 1)) with hhdef
  have hcont : ∀ n, Continuous (h n) := fun n =>
    ((continuous_logPlus_div a).div_const _).add
      ((continuous_logPlus_div a).min (((continuous_logPlus_div a).pow 2).div_const _))
  have hIa := integrable_logPlus_div μW hlog ha
  have hbound : ∀ n, 2 ≤ n → ∀ w, 0 ≤ h n w ∧ h n w ≤ 2 * logPlus (w / a) := by
    intro n hn w
    have hm := nat_sub_one_pos hn
    have hm1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hL := logPlus_nonneg (w / a)
    have h1 : logPlus (w / a) / ((n : ℝ) - 1) ≤ logPlus (w / a) :=
      div_le_self hL hm1
    have h2 := min_le_left (logPlus (w / a)) (logPlus (w / a) ^ 2 / ((n : ℝ) - 1))
    have h3 : 0 ≤ min (logPlus (w / a)) (logPlus (w / a) ^ 2 / ((n : ℝ) - 1)) :=
      le_min hL (by positivity)
    refine ⟨add_nonneg (div_nonneg hL hm.le) h3, ?_⟩
    simp only [hhdef]
    linarith
  have hint : ∀ n, 2 ≤ n → Integrable (h n) μW := fun n hn =>
    Integrable.mono' (hIa.const_mul 2) (hcont n).aestronglyMeasurable
      (Eventually.of_forall (fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound n hn w).1]
        exact (hbound n hn w).2))
  have hlim : Tendsto (fun n => ∫ w, h n w ∂μW) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μW) (l := atTop)
      (F := h) (f := fun _ => 0) (fun w => 2 * logPlus (w / a))
      (Eventually.of_forall (fun n => (hcont n).aestronglyMeasurable))
      (by
        filter_upwards [eventually_ge_atTop 2] with n hn
        refine Eventually.of_forall (fun w => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound n hn w).1]
        exact (hbound n hn w).2)
      (hIa.const_mul 2)
      (Eventually.of_forall (fun w => by
        have hA : Tendsto (fun n : ℕ => logPlus (w / a) / ((n : ℝ) - 1)) atTop (𝓝 0) := by
          have := (tendsto_const_nhds (x := logPlus (w / a))).mul tendsto_inv_nat_sub_one
          rw [mul_zero] at this
          exact this.congr (fun n => by ring)
        have hB : Tendsto (fun n : ℕ => logPlus (w / a) ^ 2 / ((n : ℝ) - 1)) atTop (𝓝 0) := by
          have := (tendsto_const_nhds (x := logPlus (w / a) ^ 2)).mul tendsto_inv_nat_sub_one
          rw [mul_zero] at this
          exact this.congr (fun n => by ring)
        have hC : Tendsto (fun n : ℕ => min (logPlus (w / a))
            (logPlus (w / a) ^ 2 / ((n : ℝ) - 1))) atTop (𝓝 0) := by
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB ?_ ?_
          · filter_upwards [eventually_ge_atTop 2] with n hn
            exact le_min (logPlus_nonneg _) (div_nonneg (by positivity) (nat_sub_one_pos hn).le)
          · exact Eventually.of_forall (fun n => min_le_right _ _)
        simpa using hA.add hC))
    simpa using this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 hlim).2 ε hε, eventually_ge_atTop 2] with n hn hn2 T hT
  have hT0 : 0 < T := lt_of_lt_of_le ha hT
  have hIT := integrable_logPlus_div μW hlog hT0
  have hIp : Integrable (fun w => (n : ℝ) * pStar n T w) μW :=
    (integrable_pStar μW hn2 hT0).const_mul _
  rw [dist_comm, Real.dist_eq, ← integral_const_mul, logDemand, ← integral_sub hIp hIT]
  refine lt_of_le_of_lt (abs_integral_le_integral_abs.trans (integral_mono (hIp.sub hIT).abs
    (hint n hn2) (fun w => ?_))) hn
  have hLT := logPlus_nonneg (w / T)
  have hLa : logPlus (w / T) ≤ logPlus (w / a) := logPlus_div_anti ha hT w
  have hm := nat_sub_one_pos hn2
  simp only [hhdef]
  rw [pStar_eq_exp hn2 hT0]
  refine (abs_nat_mul_one_sub_exp_sub_le hn2 hLT).trans ?_
  exact add_le_add (div_le_div_of_nonneg_right hLa hm.le)
    (min_le_min hLa (div_le_div_of_nonneg_right (pow_le_pow_left₀ hLT hLa 2) hm.le))

theorem tendsto_capacityRoot (hlog : Integrable logPlus μW) {β T : ℝ} (hβ : 0 < β)
    (hT : 0 < T) (hroot : ∫ w, logPlus (w / T) ∂μW = β) {t : ℕ → ℝ}
    (hcap : ∀ᶠ n in atTop, 0 < t n ∧ ∫ w, pStar n (t n) w ∂μW = β / n) :
    Tendsto t atTop (𝓝 T) := by
  have hG : logDemand μW T = β := hroot
  have hcap' : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 0 < t n ∧ (n : ℝ) * ∫ w, pStar n (t n) w ∂μW = β := by
    filter_upwards [hcap, eventually_ge_atTop 2] with n hn hn2
    refine ⟨hn2, hn.1, ?_⟩
    rw [hn.2]
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have ha'0 : 0 < max a (T / 2) := lt_of_lt_of_le (half_pos hT) (le_max_right _ _)
    have ha'T : max a (T / 2) < T := max_lt ha (half_lt_self hT)
    have hGa : β < logDemand μW (max a (T / 2)) := by
      have := logDemand_strict μW hlog ha'0 ha'T
        (by linarith [logDemand_anti μW hlog ha'0 ha'T.le])
      linarith
    filter_upwards [hcap',
      (tendsto_order.1 (tendsto_nat_mul_integral_pStar μW hlog ha'0)).1 β hGa] with n hn hlim
    obtain ⟨hn2, htn, heq⟩ := hn
    by_contra hle
    push Not at hle
    have hmono := integral_pStar_anti μW hn2 htn (hle.trans (le_max_left a (T / 2)))
    have := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  · have hGb : logDemand μW b < β := by
      have := logDemand_strict μW hlog hT hb (by rw [hG]; exact hβ)
      linarith
    filter_upwards [hcap',
      (tendsto_order.1 (tendsto_nat_mul_integral_pStar μW hlog (hT.trans hb))).2 β hGb]
      with n hn hlim
    obtain ⟨hn2, htn, heq⟩ := hn
    by_contra hle
    push Not at hle
    have hmono := integral_pStar_anti μW hn2 (hT.trans hb) hle
    have := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith

end Root

section Pointwise

variable {t : ℕ → ℝ} {T : ℝ}

theorem eventually_pos_of_tendsto (ht : Tendsto t atTop (𝓝 T)) (hT : 0 < T) :
    ∀ᶠ n in atTop, 0 < t n :=
  ht.eventually (lt_mem_nhds hT)

theorem tendsto_logPlus_div_root (ht : Tendsto t atTop (𝓝 T)) (hT : 0 < T) (w : ℝ) :
    Tendsto (fun n => logPlus (w / t n)) atTop (𝓝 (logPlus (w / T))) :=
  (continuous_logPlus.tendsto _).comp (tendsto_const_nhds.div ht hT.ne')

theorem tendsto_nat_mul_pStar_root (ht : Tendsto t atTop (𝓝 T)) (hT : 0 < T) (w : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * pStar n (t n) w) atTop (𝓝 (logPlus (w / T))) := by
  refine (tendsto_nat_mul_one_sub_exp (Eventually.of_forall (fun n => logPlus_nonneg _))
    (tendsto_logPlus_div_root ht hT w)).congr' ?_
  filter_upwards [eventually_pos_of_tendsto ht hT, eventually_ge_atTop 2] with n htn hn
  rw [pStar_eq_exp hn htn]

theorem tendsto_pStar_root_zero (ht : Tendsto t atTop (𝓝 T)) (hT : 0 < T) (w : ℝ) :
    Tendsto (fun n : ℕ => pStar n (t n) w) atTop (𝓝 0) := by
  have := (tendsto_nat_mul_pStar_root ht hT w).mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end Pointwise

noncomputable def binomialMass (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

theorem binomial_prob_eq_binomialMass (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) :
    (IndependentCounts.binomial n p hp0 hp1).prob (fun r => r.val = j) =
      binomialMass n p j := by
  induction n generalizing j with
  | zero =>
    rw [FiniteLaw.prob_eq_expect]
    change (FiniteLaw.dirac (0 : Fin 1)).expect _ = _
    rw [FiniteLaw.expect_dirac]
    cases j <;> simp [binomialMass]
  | succ n ih =>
    rw [FiniteLaw.prob_eq_expect, IndependentCounts.expect_binomial_succ]
    simp only [IndependentCounts.val_add_false, IndependentCounts.val_add_true]
    have e0 : ∀ k, (IndependentCounts.binomial n p hp0 hp1).expect
        (fun r => if r.val = k then (1 : ℝ) else 0) = binomialMass n p k := fun k => by
      rw [← FiniteLaw.prob_eq_expect]
      exact ih k
    rw [e0 j]
    cases j with
    | zero =>
      have h0 : (IndependentCounts.binomial n p hp0 hp1).expect
          (fun r => if 1 + r.val = 0 then (1 : ℝ) else 0) = 0 := by
        simp
      rw [h0]
      simp [binomialMass, pow_succ]
      ring
    | succ k =>
      have h1 : (IndependentCounts.binomial n p hp0 hp1).expect
          (fun r => if 1 + r.val = k + 1 then (1 : ℝ) else 0) = binomialMass n p k := by
        rw [← e0 k]
        apply FiniteLaw.expect_congr
        intro r
        simp [add_comm]
      rw [h1]
      unfold binomialMass
      rw [Nat.choose_succ_succ', Nat.cast_add]
      rcases Nat.lt_or_ge n (k + 1) with h | h
      · rw [Nat.choose_eq_zero_of_lt h]
        have hk : n - k = 0 := by omega
        have hk' : n + 1 - (k + 1) = 0 := by omega
        rw [hk, hk']
        simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, pow_zero, mul_one, pow_succ]
        ring
      · have hk : n - k = n - (k + 1) + 1 := by omega
        have hk' : n + 1 - (k + 1) = n - (k + 1) + 1 := by omega
        rw [hk, hk']
        ring

theorem choose_mul_pow_eq_prod {n j : ℕ} (hj : j ≤ n) (p : ℝ) :
    (n.choose j : ℝ) * p ^ j =
      (∏ i ∈ Finset.range j, (((n : ℝ) - i) * p)) / (j.factorial : ℝ) := by
  have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hdesc : ((n.descFactorial j : ℕ) : ℝ) = ∏ i ∈ Finset.range j, ((n : ℝ) - i) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Nat.cast_sub (by have := Finset.mem_range.mp hi; omega)]
  have hchoose : (n.choose j : ℝ) = ((n.descFactorial j : ℕ) : ℝ) / (j.factorial : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  rw [hchoose, hdesc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  ring

theorem tendsto_binomialMass_of_tendsto_mul {p : ℕ → ℝ} {lam : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) (j : ℕ) :
    Tendsto (fun n => binomialMass n (p n) j) atTop
      (𝓝 (Real.exp (-lam) * lam ^ j / (j.factorial : ℝ))) := by
  have hp0 : Tendsto p atTop (𝓝 0) := by
    have := hp.mul tendsto_one_div_atTop_nhds_zero_nat
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hpow : Tendsto (fun n : ℕ => (1 - p n) ^ n) atTop (𝓝 (Real.exp (-lam))) := by
    have h := Real.tendsto_one_add_pow_exp_of_tendsto (g := fun n => -p n) (t := -lam)
      (by simpa [mul_neg] using hp.neg)
    simpa [sub_eq_add_neg] using h
  have hq : Tendsto (fun n : ℕ => 1 - p n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hp0
  have hqj : Tendsto (fun n : ℕ => (1 - p n) ^ j) atTop (𝓝 1) := by
    simpa using hq.pow j
  have hprod : Tendsto (fun n : ℕ => ∏ i ∈ Finset.range j, (((n : ℝ) - i) * p n)) atTop
      (𝓝 (lam ^ j)) := by
    have h := tendsto_finsetProd (Finset.range j) (fun i _ =>
      (show Tendsto (fun n : ℕ => ((n : ℝ) - i) * p n) atTop (𝓝 lam) from by
        have := hp.sub (hp0.const_mul (i : ℝ))
        rw [mul_zero, sub_zero] at this
        exact this.congr (fun n => by ring)))
    simpa [Finset.prod_const, Finset.card_range] using h
  have hlim := (hprod.div_const (j.factorial : ℝ)).mul (hpow.div hqj one_ne_zero)
  have heq : (fun n : ℕ => (∏ i ∈ Finset.range j, (((n : ℝ) - i) * p n)) /
      (j.factorial : ℝ) * ((1 - p n) ^ n / (1 - p n) ^ j)) =ᶠ[atTop]
      fun n => binomialMass n (p n) j := by
    filter_upwards [eventually_ge_atTop j, hq.eventually_ne one_ne_zero] with n hn hq0
    rw [binomialMass, choose_mul_pow_eq_prod hn, pow_sub₀ _ hq0 hn, div_eq_mul_inv _ ((1 - p n) ^ j)]
  have := hlim.congr' heq
  convert this using 2
  ring

theorem poissonPMFReal_toNNReal {lam : ℝ} (h : 0 ≤ lam) (j : ℕ) :
    (ProbabilityTheory.poissonMeasure lam.toNNReal).real {j} =
      Real.exp (-lam) * lam ^ j / (j.factorial : ℝ) := by
  simp [ProbabilityTheory.poissonMeasure_real_singleton, Real.coe_toNNReal _ h]

theorem tendsto_binomialMass_poisson {t : ℕ → ℝ} {T : ℝ} (ht : Tendsto t atTop (𝓝 T))
    (hT : 0 < T) (w : ℝ) (j : ℕ) :
    Tendsto (fun n => binomialMass n (pStar n (t n) w) j) atTop
      (𝓝 ((ProbabilityTheory.poissonMeasure (logPlus (w / T)).toNNReal).real {j})) := by
  rw [poissonPMFReal_toNNReal (logPlus_nonneg _)]
  exact tendsto_binomialMass_of_tendsto_mul (tendsto_nat_mul_pStar_root ht hT w) j

theorem tendsto_binomial_prob_poisson {t : ℕ → ℝ} {T : ℝ} (htpos : ∀ n, 0 ≤ t n)
    (ht : Tendsto t atTop (𝓝 T)) (hT : 0 < T) (w : ℝ) (j : ℕ) :
    Tendsto (fun n => (IndependentCounts.binomial n (pStar n (t n) w) (pStar_nonneg _ _ _)
      (pStar_le_one n (htpos n) w)).prob (fun r => r.val = j)) atTop
      (𝓝 ((ProbabilityTheory.poissonMeasure (logPlus (w / T)).toNNReal).real {j})) := by
  simp only [binomial_prob_eq_binomialMass]
  exact tendsto_binomialMass_poisson ht hT w j

theorem success_pStar_eq {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (w : ℝ) :
    success n (pStar n t w) =
      1 - Real.exp (-((n : ℝ) * (logPlus (w / t) / ((n : ℝ) - 1)))) := by
  unfold success
  rw [one_sub_pStar_pow hn ht]

theorem success_pStar_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (w : ℝ) :
    0 ≤ success n (pStar n t w) := by
  unfold success
  have := pow_le_one₀ (n := n) (sub_nonneg.mpr (pStar_le_one n ht w))
    (by linarith [pStar_nonneg n t w])
  linarith

theorem abs_success_pStar_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (w : ℝ) :
    |success n (pStar n t w)| ≤ 1 := by
  rw [abs_of_nonneg (success_pStar_nonneg n ht w)]
  exact success_le_one n _ (pStar_le_one n ht w)

theorem tendsto_success_pStar_root {t : ℕ → ℝ} {T : ℝ} (ht : Tendsto t atTop (𝓝 T))
    (hT : 0 < T) (w : ℝ) :
    Tendsto (fun n : ℕ => success n (pStar n (t n) w)) atTop
      (𝓝 (1 - Real.exp (-(logPlus (w / T))))) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * (logPlus (w / t n) / ((n : ℝ) - 1))) atTop
      (𝓝 (logPlus (w / T))) := by
    have := tendsto_nat_div_nat_sub_one.mul (tendsto_logPlus_div_root ht hT w)
    rw [one_mul] at this
    exact this.congr (fun n => by ring)
  have h2 : Tendsto (fun n : ℕ => 1 - Real.exp (-((n : ℝ) * (logPlus (w / t n) /
      ((n : ℝ) - 1))))) atTop (𝓝 (1 - Real.exp (-(logPlus (w / T))))) :=
    tendsto_const_nhds.sub ((Real.continuous_exp.tendsto _).comp h1.neg)
  refine h2.congr' ?_
  filter_upwards [eventually_pos_of_tendsto ht hT, eventually_ge_atTop 2] with n htn hn
  rw [success_pStar_eq hn htn]

section Coverage

variable (μW : Measure ℝ) [IsFiniteMeasure μW]

theorem tendsto_coverage_root {t : ℕ → ℝ} {T : ℝ} (ht : Tendsto t atTop (𝓝 T)) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∫ w, success n (pStar n (t n) w) ∂μW) atTop
      (𝓝 (∫ w, (1 - Real.exp (-(logPlus (w / T)))) ∂μW)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
    (integrable_const 1) (Eventually.of_forall (tendsto_success_pStar_root ht hT))
  · filter_upwards [eventually_pos_of_tendsto ht hT, eventually_ge_atTop 2] with n htn hn
    exact ((continuous_success n).comp (continuous_pStar hn htn)).aestronglyMeasurable
  · filter_upwards [eventually_pos_of_tendsto ht hT] with n htn
    exact Eventually.of_forall (fun w => abs_success_pStar_le n htn.le w)

theorem integrable_one_sub_exp_logPlus (T : ℝ) :
    Integrable (fun w => 1 - Real.exp (-(logPlus (w / T)))) μW := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((continuous_const.sub (Real.continuous_exp.comp
      (continuous_logPlus_div T).neg)).aestronglyMeasurable) (Eventually.of_forall (fun w => ?_))
  have h1 : Real.exp (-(logPlus (w / T))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (logPlus_nonneg _))
  have h2 := Real.exp_pos (-(logPlus (w / T)))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

theorem integral_one_sub_exp_logPlus_pos (hlog : Integrable logPlus μW) {β T : ℝ}
    (hβ : 0 < β) (hT : 0 < T) (hroot : ∫ w, logPlus (w / T) ∂μW = β) :
    0 < ∫ w, (1 - Real.exp (-(logPlus (w / T)))) ∂μW := by
  have hμ := measure_Ioi_pos_of_logDemand_pos μW hlog hT (by
    change 0 < ∫ w, logPlus (w / T) ∂μW
    rw [hroot]
    exact hβ)
  have hnn : ∀ w, 0 ≤ 1 - Real.exp (-(logPlus (w / T))) := fun w => by
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (logPlus_nonneg (w / T)))
    linarith
  rw [integral_pos_iff_support_of_nonneg hnn (integrable_one_sub_exp_logPlus μW T)]
  refine lt_of_lt_of_le hμ (measure_mono ?_)
  intro w hw
  refine Function.mem_support.mpr (ne_of_gt ?_)
  have hL := logPlus_pos ((one_lt_div hT).mpr (mem_Ioi.mp hw))
  have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hL)
  linarith

theorem tendsto_multiplicity_root (hlog : Integrable logPlus μW) {β T : ℝ} (hβ : 0 < β)
    (hT : 0 < T) (hroot : ∫ w, logPlus (w / T) ∂μW = β) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 T)) :
    Tendsto (fun n : ℕ => β / ∫ w, success n (pStar n (t n) w) ∂μW) atTop
      (𝓝 (β / ∫ w, (1 - Real.exp (-(logPlus (w / T)))) ∂μW)) :=
  tendsto_const_nhds.div (tendsto_coverage_root μW ht hT)
    (integral_one_sub_exp_logPlus_pos μW hlog hβ hT hroot).ne'

end Coverage

theorem logRoot_eq_exp_of_ae_gt (μW : Measure ℝ) [IsProbabilityMeasure μW]
    (hlog : Integrable logPlus μW) {β T : ℝ} (hT : 0 < T)
    (hroot : ∫ w, logPlus (w / T) ∂μW = β) (hgt : ∀ᵐ w ∂μW, T < w) :
    Integrable Real.log μW ∧ T = Real.exp ((∫ w, Real.log w ∂μW) - β) := by
  have hae : (fun w => Real.log w) =ᵐ[μW] (fun w => logPlus (w / T) + Real.log T) := by
    filter_upwards [hgt] with w hw
    rw [logPlus_of_one_le ((one_le_div hT).mpr hw.le), Real.log_div (by linarith) hT.ne']
    ring
  have hI := integrable_logPlus_div μW hlog hT
  have hint : Integrable (fun w => logPlus (w / T) + Real.log T) μW :=
    hI.add (integrable_const _)
  refine ⟨hint.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add hI (integrable_const _), hroot]
  simp [Real.exp_log hT]

theorem cor_tails_ii (μW : Measure ℝ) [IsProbabilityMeasure μW]
    (hlog : Integrable logPlus μW) (hpos : 0 < μW (Ioi 0)) {β : ℝ} (hβ : 0 < β) :
    ∃! T, 0 < T ∧ ∫ w, logPlus (w / T) ∂μW = β ∧
      ∀ t : ℕ → ℝ, (∀ᶠ n in atTop, 0 < t n ∧ ∫ w, pStar n (t n) w ∂μW = β / n) →
        Tendsto t atTop (𝓝 T) ∧
        (∀ w, Tendsto (fun n : ℕ => (n : ℝ) * pStar n (t n) w) atTop
          (𝓝 (logPlus (w / T)))) ∧
        (∀ w, Tendsto (fun n : ℕ => pStar n (t n) w) atTop (𝓝 0)) ∧
        (∀ w (j : ℕ), Tendsto (fun n => binomialMass n (pStar n (t n) w) j) atTop
          (𝓝 ((ProbabilityTheory.poissonMeasure (logPlus (w / T)).toNNReal).real {j}))) ∧
        Tendsto (fun n : ℕ => ∫ w, success n (pStar n (t n) w) ∂μW) atTop
          (𝓝 (∫ w, (1 - Real.exp (-(logPlus (w / T)))) ∂μW)) ∧
        Tendsto (fun n : ℕ => β / ∫ w, success n (pStar n (t n) w) ∂μW) atTop
          (𝓝 (β / ∫ w, (1 - Real.exp (-(logPlus (w / T)))) ∂μW)) := by
  obtain ⟨T, ⟨hT, hroot⟩, huniq⟩ := existsUnique_logRoot μW hlog hpos hβ
  refine ⟨T, ⟨hT, hroot, fun t hcap => ?_⟩, fun y hy => huniq y ⟨hy.1, hy.2.1⟩⟩
  have ht := tendsto_capacityRoot μW hlog hβ hT hroot hcap
  exact ⟨ht, tendsto_nat_mul_pStar_root ht hT, tendsto_pStar_root_zero ht hT,
    tendsto_binomialMass_poisson ht hT, tendsto_coverage_root μW ht hT,
    tendsto_multiplicity_root μW hlog hβ hT hroot ht⟩

end ManyProposers
end PayOnce
end FCAppendix
