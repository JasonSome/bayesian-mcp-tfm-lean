import FCAppendix.PayOnce.BidFormula
import FCAppendix.PayOnce.EndpointVariance

namespace FCAppendix.PayOnce.GaussianParameters
open MeasureTheory ProbabilityTheory Set Filter Topology
open OwnImpact

def LocalFullSupport (μ : Measure ℝ) (t : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ a b : ℝ, t-ε < a → a < b → b < t+ε → 0 < μ (Ioo a b)

theorem LocalFullSupport.crossing {μ : Measure ℝ} {t : ℝ} (h : LocalFullSupport μ t) :
    0 < μ (Iio t) ∧ 0 < μ (Ioi t) := by
  obtain ⟨ε,hε,h⟩ := h
  constructor
  · exact (h (t-ε/2) t (by linarith) (by linarith) (by linarith)).trans_le
      (measure_mono fun _ hx => hx.2)
  · exact (h t (t+ε/2) (by linarith) (by linarith) (by linarith)).trans_le
      (measure_mono fun _ hx => hx.1)

noncomputable def priceDensity (n : ℕ) (t w : ℝ) : ℝ :=
  (Ioi t).indicator
    (fun w => H n (Limit.pStar n t w)/(t*Hslope n (Limit.pStar n t w))) w

theorem priceDensity_eq_source (n : ℕ) (t w : ℝ) :
    priceDensity n t w = (Ioi t).indicator
      (fun w => 1/(Limit.bidStar n t w*(-deriv (H n) (Limit.pStar n t w)))) w := by
  by_cases hw : t < w
  · rw [priceDensity,indicator_of_mem (show w ∈ Ioi t from hw),indicator_of_mem (show w ∈ Ioi t from hw),Limit.bidStar_of_lt hw,
      neg_deriv_H_eq_Hslope]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
    ring
  · rw [priceDensity,indicator_of_notMem (show w ∉ Ioi t from hw),indicator_of_notMem (show w ∉ Ioi t from hw)]

theorem priceSlope_eq_integral (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    EndpointVariance.priceSlope μ n t = ∫ w, priceDensity n t w ∂μ := by
  unfold EndpointVariance.priceSlope EndpointVariance.priceWeight priceDensity
  simp only [neg_deriv_H_eq_Hslope]
  rfl

theorem priceSlope_eq_source (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    EndpointVariance.priceSlope μ n t = ∫ w, (Ioi t).indicator
      (fun w => 1/(Limit.bidStar n t w*(-deriv (H n) (Limit.pStar n t w)))) w ∂μ := by
  rw [priceSlope_eq_integral]
  exact integral_congr_ae (Eventually.of_forall (priceDensity_eq_source n t))

theorem measurable_priceDensity (n : ℕ) (t : ℝ) : Measurable (priceDensity n t) := by
  have hs : Measurable (Hslope n) := by unfold Hslope; fun_prop
  exact (((continuous_H n).measurable.comp (Limit.measurable_pStar n t)).div
    (measurable_const.mul (hs.comp (Limit.measurable_pStar n t)))).indicator measurableSet_Ioi

theorem priceDensity_bounds {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (w : ℝ) :
    priceDensity n t w ∈ Icc (0:ℝ) ((n:ℝ)/t) := by
  have hp : Limit.pStar n t w ∈ Icc (0:ℝ) 1 :=
    ⟨Limit.pStar_nonneg,Limit.pStar_le_one ht.le⟩
  have hH := H_pos n (by omega) _ hp.1 hp.2
  have hs := Hslope_pos hn hp
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  by_cases hw : t < w
  · rw [priceDensity,indicator_of_mem (show w ∈ Ioi t from hw)]
    refine ⟨(div_pos hH (mul_pos ht hs)).le,?_⟩
    apply (div_le_iff₀ (mul_pos ht hs)).mpr
    have hlower := (div_le_iff₀ hnR).mp (Hslope_bounds hn hp).1
    have he : (n:ℝ)/t*(t*Hslope n (Limit.pStar n t w)) =
        (n:ℝ)*Hslope n (Limit.pStar n t w) := by field_simp
    rw [he]
    exact (H_bounds n (by omega) _ hp.1 hp.2).2.trans (by nlinarith)
  · rw [priceDensity,indicator_of_notMem (show w ∉ Ioi t from hw)]
    exact ⟨le_rfl,(div_pos hnR ht).le⟩

theorem priceDensity_pos_iff {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (w : ℝ) :
    0 < priceDensity n t w ↔ t < w := by
  by_cases hw : t < w
  · rw [priceDensity,indicator_of_mem (show w ∈ Ioi t from hw)]
    have hp : Limit.pStar n t w ∈ Icc (0:ℝ) 1 :=
      ⟨Limit.pStar_nonneg,Limit.pStar_le_one ht.le⟩
    exact iff_of_true (div_pos (H_pos n (by omega) _ hp.1 hp.2)
      (mul_pos ht (Hslope_pos hn hp))) hw
  · rw [priceDensity,indicator_of_notMem (show w ∉ Ioi t from hw)]
    exact iff_of_false (lt_irrefl _) hw

theorem integrable_priceDensity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) : Integrable (priceDensity n t) μ := by
  apply Integrable.of_bound (measurable_priceDensity n t).aestronglyMeasurable ((n:ℝ)/t)
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (priceDensity_bounds hn ht w).1]
  exact (priceDensity_bounds hn ht w).2

theorem priceSlope_pos (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (hupper : 0 < μ (Ioi t)) :
    0 < EndpointVariance.priceSlope μ n t := by
  rw [priceSlope_eq_integral]
  apply (integral_pos_iff_support_of_nonneg (fun w => (priceDensity_bounds hn ht w).1)
    (integrable_priceDensity μ hn ht)).mpr
  apply hupper.trans_le
  apply measure_mono
  intro w hw
  exact ((priceDensity_pos_iff hn ht w).mpr hw).ne'

theorem priceSlope_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    EndpointVariance.priceSlope μ n t ≤ (n:ℝ)/t := by
  rw [priceSlope_eq_integral]
  have hh := integral_mono (integrable_priceDensity μ hn ht) (integrable_const ((n:ℝ)/t))
    (fun w => (priceDensity_bounds hn ht w).2)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

theorem pStar_memLp (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (q : ENNReal) : MemLp (Limit.pStar n t) q μ :=
  memLp_of_bounded (Eventually.of_forall fun _ => ⟨Limit.pStar_nonneg,Limit.pStar_le_one ht⟩)
    (Limit.measurable_pStar n t).aestronglyMeasurable q

theorem pStar_not_ae_const (μ : Measure ℝ) {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t)
    (hlower : 0 < μ (Iio t)) (hupper : 0 < μ (Ioi t)) (c : ℝ) :
    ¬ (∀ᵐ w ∂μ, Limit.pStar n t w = c) := by
  intro h
  obtain ⟨w₀,hw₀,hc₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hlower.ne' (ae_restrict_of_ae h)
  have hc : c = 0 := by rw [Limit.pStar_eq_zero_of_le hn ht hw₀.le] at hc₀; exact hc₀.symm
  obtain ⟨w₁,hw₁,hc₁⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hupper.ne' (ae_restrict_of_ae h)
  have hp := (Limit.pStar_pos_iff hn ht).mpr hw₁
  rw [hc₁,hc] at hp
  exact (lt_irrefl _) hp

theorem variance_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (hlocal : LocalFullSupport μ t) :
    0 < ProbabilityTheory.variance (Limit.pStar n t) μ := by
  by_contra h
  have hz : ProbabilityTheory.variance (Limit.pStar n t) μ = 0 :=
    le_antisymm (le_of_not_gt h) (ProbabilityTheory.variance_nonneg _ _)
  exact pStar_not_ae_const μ hn ht.le hlocal.crossing.1 hlocal.crossing.2 _
    (ae_eq_integral_of_variance_eq_zero (pStar_memLp μ n ht.le 2) hz)

theorem variance_le_quarter (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ProbabilityTheory.variance (Limit.pStar n t) μ ≤ 1/4 := by
  have hh := variance_le_sq_of_bounded (μ := μ)
    (Eventually.of_forall fun w => (show Limit.pStar n t w ∈ Icc (0:ℝ) 1 from
      ⟨Limit.pStar_nonneg,Limit.pStar_le_one ht⟩)) (Limit.measurable_pStar n t).aemeasurable
  norm_num at hh ⊢
  exact hh

noncomputable def sigma (μ : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (ProbabilityTheory.variance (Limit.pStar n t) μ)/EndpointVariance.priceSlope μ n t

noncomputable def entryCoeff (n : ℕ) (t : ℝ) : ℝ := 2*(n:ℝ)/(((n:ℝ)-1)*t)

theorem sigma_sq (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    sigma μ n t ^ 2 = EndpointVariance.sigmaSq μ n t := by
  unfold sigma EndpointVariance.sigmaSq
  rw [div_pow,Real.sq_sqrt (ProbabilityTheory.variance_nonneg _ _)]
  rfl

theorem sigma_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (hlocal : LocalFullSupport μ t) :
    0 < sigma μ n t :=
  div_pos (Real.sqrt_pos.mpr (variance_pos μ hn ht hlocal))
    (priceSlope_pos μ hn ht hlocal.crossing.2)

theorem entryCoeff_pos {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    0 < entryCoeff n t := by
  unfold entryCoeff
  have hnR : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  positivity

theorem parameters_nondegenerate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (hlocal : LocalFullSupport μ t) :
    Integrable (priceDensity n t) μ ∧
      MemLp (Limit.pStar n t) 2 μ ∧
      0 < EndpointVariance.priceSlope μ n t ∧ EndpointVariance.priceSlope μ n t ≤ (n:ℝ)/t ∧
      0 < ProbabilityTheory.variance (Limit.pStar n t) μ ∧
      ProbabilityTheory.variance (Limit.pStar n t) μ ≤ 1/4 ∧
      0 < sigma μ n t ∧ sigma μ n t ^ 2 = EndpointVariance.sigmaSq μ n t ∧
      0 < entryCoeff n t :=
  ⟨integrable_priceDensity μ hn ht,pStar_memLp μ n ht.le 2,
    priceSlope_pos μ hn ht hlocal.crossing.2,priceSlope_le μ hn ht,
    variance_pos μ hn ht hlocal,variance_le_quarter μ n ht.le,
    sigma_pos μ hn ht hlocal,sigma_sq μ n t,entryCoeff_pos hn ht⟩

end FCAppendix.PayOnce.GaussianParameters
