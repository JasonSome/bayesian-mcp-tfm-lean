import FCAppendix.PayOnce.KernelDerivative
import FCAppendix.PayOnce.GaussianParameters

namespace FCAppendix.PayOnce.OwnImpact
open MeasureTheory ProbabilityTheory Filter Topology Set CommonList KernelTailEvent

noncomputable def kernelPriceSlope (n : ℕ) (b L : ℝ) : ℝ :=
  (Ioo L ((n:ℝ)*L)).indicator (fun b => sensitivity n b (kernel n b L)) b

theorem kernel_interior_iff {n : ℕ} (hn : 2 ≤ n) {b L : ℝ} (hL : 0 < L) :
    (0 < kernel n b L ∧ kernel n b L < 1) ↔ L < b ∧ b < (n:ℝ)*L := by
  constructor
  · intro hp
    constructor
    · by_contra h
      rw [kernel_of_le n (le_of_not_gt h)] at hp
      exact hp.1.false
    · by_contra h
      rw [kernel_of_ge n hn hL (le_of_not_gt h)] at hp
      exact hp.2.false
  · intro hb
    have hbpos := hL.trans hb.1
    have hp := kernel_bounds hn hL b
    constructor
    · apply lt_of_le_of_ne hp.1
      intro he
      exact hb.1.not_ge ((kernel_eq_zero_iff n hn hbpos hL).mp he.symm)
    · apply lt_of_le_of_ne hp.2
      intro he
      have hh := (le_div_iff₀ (Nat.cast_pos.mpr (show 0 < n by omega))).mp
        ((kernel_eq_one_iff n hn hbpos hL).mp he)
      nlinarith [hb.2]

theorem hasStrictDerivAt_kernel_price_slope {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hL : 0 < L) (hzero : b ≠ L) (hone : b ≠ (n:ℝ)*L) :
    HasStrictDerivAt (kernel n b) (-kernelPriceSlope n b L) L := by
  classical
  by_cases hb : 0 < b
  · have hh := hasStrictDerivAt_kernel_price hn hb hL hzero hone
    simpa only [kernel_interior_iff hn hL,kernelPriceSlope,Set.indicator,mem_Ioo,
      neg_ite,neg_zero] using hh
  · have hbl : b < L := (le_of_not_gt hb).trans_lt hL
    have hnmem : b ∉ Ioo L ((n:ℝ)*L) := fun hx => hbl.not_gt hx.1
    rw [kernelPriceSlope,indicator_of_notMem hnmem,neg_zero]
    exact hasStrictDerivAt_kernel_price_zero hbl

theorem hasDerivAt_kernel_price_slope {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hL : 0 < L) (hzero : b ≠ L) (hone : b ≠ (n:ℝ)*L) :
    HasDerivAt (kernel n b) (-kernelPriceSlope n b L) L :=
  (hasStrictDerivAt_kernel_price_slope hn hL hzero hone).hasDerivAt

theorem kernelPriceSlope_bounds {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (b : ℝ) :
    kernelPriceSlope n b L ∈ Icc (0:ℝ) ((n:ℝ)/L) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  by_cases hb : b ∈ Ioo L ((n:ℝ)*L)
  · rw [kernelPriceSlope,indicator_of_mem hb]
    have hbpos := hL.trans hb.1
    have hp := kernel_bounds hn hL b
    refine ⟨(sensitivity_pos hn hbpos hp).le,?_⟩
    have hd : L/(n:ℝ) ≤ b*Hslope n (kernel n b L) := calc
      L/(n:ℝ) ≤ b/(n:ℝ) := div_le_div_of_nonneg_right hb.1.le hnR.le
      _ = b*(1/(n:ℝ)) := by ring
      _ ≤ b*Hslope n (kernel n b L) :=
        mul_le_mul_of_nonneg_left (Hslope_bounds hn hp).1 hbpos.le
    have hh := one_div_le_one_div_of_le (div_pos hL hnR) hd
    simpa only [sensitivity,one_div_div] using hh
  · rw [kernelPriceSlope,indicator_of_notMem hb]
    exact ⟨le_rfl,(div_pos hnR hL).le⟩

theorem abs_deriv_kernel_price_le {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hL : 0 < L) (hzero : b ≠ L) (hone : b ≠ (n:ℝ)*L) :
    |deriv (kernel n b) L| ≤ (n:ℝ)/L := by
  rw [(hasDerivAt_kernel_price_slope hn hL hzero hone).deriv,abs_neg,
    abs_of_nonneg (kernelPriceSlope_bounds hn hL b).1]
  exact (kernelPriceSlope_bounds hn hL b).2

theorem measurable_kernelPriceSlope {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) :
    Measurable (fun b => kernelPriceSlope n b L) := by
  have hs : Measurable (Hslope n) := by unfold Hslope; fun_prop
  exact (measurable_const.div (measurable_id.mul
    (hs.comp (continuous_kernel_bid hn hL).measurable))).indicator measurableSet_Ioo

theorem tendsto_kernelPriceSlope {α : Type*} {l : Filter α} {n : ℕ}
    (hn : 2 ≤ n) {b L : ℝ} (hL : 0 < L)
    (hzero : b ≠ L) (hone : b ≠ (n:ℝ)*L)
    {bs Ls : α → ℝ} (hb : Tendsto bs l (𝓝 b)) (hLs : Tendsto Ls l (𝓝 L)) :
    Tendsto (fun t => kernelPriceSlope n (bs t) (Ls t)) l
      (𝓝 (kernelPriceSlope n b L)) := by
  have hpos := hLs.eventually (eventually_gt_nhds hL)
  by_cases hlo : b < L
  · have hnmem : b ∉ Ioo L ((n:ℝ)*L) := fun hx => hlo.not_gt hx.1
    rw [kernelPriceSlope,indicator_of_notMem hnmem]
    apply tendsto_const_nhds.congr'
    filter_upwards [hb.eventually_lt hLs hlo] with t ht
    exact (indicator_of_notMem (show bs t ∉ Ioo (Ls t) ((n:ℝ)*Ls t) from
      fun hx => ht.not_gt hx.1) _).symm
  have hlb : L < b := lt_of_le_of_ne (le_of_not_gt hlo) hzero.symm
  by_cases hhi : (n:ℝ)*L < b
  · have hnmem : b ∉ Ioo L ((n:ℝ)*L) := fun hx => hhi.not_gt hx.2
    rw [kernelPriceSlope,indicator_of_notMem hnmem]
    apply tendsto_const_nhds.congr'
    filter_upwards [(hLs.const_mul (n:ℝ)).eventually_lt hb hhi] with t ht
    exact (indicator_of_notMem (show bs t ∉ Ioo (Ls t) ((n:ℝ)*Ls t) from
      fun hx => ht.not_gt hx.2) _).symm
  have hbn : b < (n:ℝ)*L := lt_of_le_of_ne (le_of_not_gt hhi) hone
  have hbpos := hL.trans hlb
  have hker : Tendsto (fun t => kernel n (bs t) (Ls t)) l (𝓝 (kernel n b L)) := by
    rw [kernel_eq_scalarDemand_ratio hn hbpos hL]
    have ht := (scalarDemand_continuous n hn 1 (by norm_num)).continuousAt.tendsto.comp
      (hLs.div hb hbpos.ne')
    apply ht.congr'
    filter_upwards [hpos,hb.eventually (eventually_gt_nhds hbpos)] with t htL htb
    exact (kernel_eq_scalarDemand_ratio hn htb htL).symm
  have hHs : Continuous (Hslope n) := by unfold Hslope; fun_prop
  have hs := (tendsto_const_nhds (x := (1:ℝ))).div (hb.mul (hHs.continuousAt.tendsto.comp hker))
    (mul_ne_zero hbpos.ne' (Hslope_pos hn (kernel_bounds hn hL b)).ne')
  rw [kernelPriceSlope,indicator_of_mem (show b ∈ Ioo L ((n:ℝ)*L) from ⟨hlb,hbn⟩)]
  apply hs.congr'
  filter_upwards [hLs.eventually_lt hb hlb,
    hb.eventually_lt (hLs.const_mul (n:ℝ)) hbn] with t htlo hthi
  change sensitivity n (bs t) (kernel n (bs t) (Ls t)) = kernelPriceSlope n (bs t) (Ls t)
  rw [kernelPriceSlope,indicator_of_mem (show bs t ∈ Ioo (Ls t) ((n:ℝ)*Ls t) from ⟨htlo,hthi⟩)]

theorem tendsto_integral_kernelPriceSlope
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L)
    (b : ℕ → Ω → ℝ) (hb : ∀ t, Measurable (b t)) (q : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun t => b t ω) atTop (𝓝 (q ω)))
    (hatoms : ∀ᵐ ω ∂μ, q ω ≠ L ∧ q ω ≠ (n:ℝ)*L)
    {Ls : ℕ → ℝ} (hLs : Tendsto Ls atTop (𝓝 L)) :
    Tendsto (fun t => ∫ ω, kernelPriceSlope n (b t ω) (Ls t) ∂μ) atTop
      (𝓝 (∫ ω, kernelPriceSlope n (q ω) L ∂μ)) := by
  have hh : 0 < L/2 := by positivity
  have hev := hLs.eventually (eventually_gt_nhds (show L/2 < L by linarith))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (n:ℝ)/(L/2))
  · filter_upwards [hev] with t ht
    exact ((measurable_kernelPriceSlope hn (hh.trans ht)).comp (hb t)).aestronglyMeasurable
  · filter_upwards [hev] with t ht
    exact Eventually.of_forall fun ω => by
      have hs := kernelPriceSlope_bounds hn (hh.trans ht) (b t ω)
      rw [Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact hs.2.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hh ht.le)
  · exact integrable_const _
  · filter_upwards [hlim,hatoms] with ω hω ha
    exact tendsto_kernelPriceSlope hn hL ha.1 ha.2 hω hLs

theorem bidStar_avoids_clipping {n : ℕ} (hn : 2 ≤ n) {L w : ℝ} (hL : 0 < L)
    (hw : w ≠ L) :
    Limit.bidStar n L w ≠ L ∧ Limit.bidStar n L w ≠ (n:ℝ)*L := by
  by_cases h : w ≤ L
  · rw [Limit.bidStar_of_le h]
    have hwL : w < L := lt_of_le_of_ne h hw
    have hm : max w 0 < L := max_lt hwL hL
    have hnR : (1:ℝ) < n := Nat.one_lt_cast.mpr hn
    exact ⟨hm.ne,(hm.trans (by nlinarith : L < (n:ℝ)*L)).ne⟩
  · have hwL := lt_of_not_ge h
    have hp : 0 < kernel n (Limit.bidStar n L w) L ∧
        kernel n (Limit.bidStar n L w) L < 1 := by
      rw [Limit.kernel_bidStar hn hL]
      exact ⟨(Limit.pStar_pos_iff hn hL.le).mpr hwL,Limit.pStar_lt_one hn hL hwL⟩
    have hi := (kernel_interior_iff hn hL).mp hp
    exact ⟨hi.1.ne',hi.2.ne⟩

theorem kernelPriceSlope_bidStar {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (w : ℝ) :
    kernelPriceSlope n (Limit.bidStar n L w) L = GaussianParameters.priceDensity n L w := by
  by_cases h : L < w
  · have hp : 0 < kernel n (Limit.bidStar n L w) L ∧
        kernel n (Limit.bidStar n L w) L < 1 := by
      rw [Limit.kernel_bidStar hn hL]
      exact ⟨(Limit.pStar_pos_iff hn hL.le).mpr h,Limit.pStar_lt_one hn hL h⟩
    have hi : Limit.bidStar n L w ∈ Ioo L ((n:ℝ)*L) := (kernel_interior_iff hn hL).mp hp
    rw [kernelPriceSlope,indicator_of_mem hi,Limit.kernel_bidStar hn hL,
      GaussianParameters.priceDensity,indicator_of_mem (show w ∈ Ioi L from h),
      sensitivity,Limit.bidStar_of_lt h]
    field_simp
  · have hle : w ≤ L := le_of_not_gt h
    have hbL : Limit.bidStar n L w ≤ L := by
      rw [Limit.bidStar_of_le hle]; exact max_le hle hL.le
    rw [kernelPriceSlope,indicator_of_notMem (show Limit.bidStar n L w ∉ Ioo L ((n:ℝ)*L) from
      fun hx => hbL.not_gt hx.1),GaussianParameters.priceDensity,
      indicator_of_notMem (show w ∉ Ioi L from h)]

end FCAppendix.PayOnce.OwnImpact
