import FCAppendix.Affine.Uniform06.MixedLaw
import FCAppendix.Affine.Uniform06.EarlyMean
import FCAppendix.Probability.EmpiricalMean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryActiveLimit
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.ClippedResidual
open FCAppendix.Affine.Uniform06
open FCAppendix.Affine.Uniform07
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

lemma continuousAt_exposure_pair {ξ z b : ℝ} (hξ : 0 < ξ) (hz : 0 < z) :
    ContinuousAt (fun x : ℝ × ℝ => exposure ξ x.1 x.2) (z,b) := by
  unfold exposure
  apply continuousAt_const.min
  apply (continuousAt_const.max (continuousAt_snd.sub continuousAt_fst)).div
    (continuousAt_const.mul (continuousAt_snd.max continuousAt_fst))
  exact (mul_pos hξ (hz.trans_le (le_max_right _ _))).ne'

theorem inactive_exposure_tendsto {ξ entryLimit v : ℝ} {b B : ℕ → ℝ}
    (hv : v < entryLimit) (hb : Tendsto b atTop (𝓝 entryLimit)) (hB : ∀ m, B m ≤ v) :
    Tendsto (fun m => exposure ξ (b m) (B m)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hb.eventually (Ioi_mem_nhds hv)] with m hm
  exact (exposure_zero ((hB m).trans hm.le)).symm

def activeExposure (ξ entryLimit : ℝ) (B0 : ℝ → ℝ) (v : ℝ) : ℝ :=
  if entryLimit < v then exposure ξ entryLimit (B0 v) else 0

lemma measurable_activeExposure {ξ entryLimit : ℝ} (hξ : 0 < ξ) (hentryLimit : 0 < entryLimit)
    {B0 : ℝ → ℝ} (hB0 : Measurable B0) : Measurable (activeExposure ξ entryLimit B0) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id)
    ((continuous_exposure hξ hentryLimit).measurable.comp hB0) measurable_const

theorem entry_exposure_tendsto_ae (μ : Measure Ω) (V : Ω → ℝ)
    (B : ℕ → Ω → ℝ) (B0 : ℝ → ℝ) {ξ entryLimit : ℝ}
    (hξ : 0 < ξ) (hentryLimit : 0 < entryLimit) (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 entryLimit))
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hthreshold : ∀ᵐ ω ∂μ, V ω ≠ entryLimit)
    (hactive : ∀ᵐ ω ∂μ, entryLimit < V ω →
      Tendsto (fun m => B m ω) atTop (𝓝 (B0 (V ω)))) :
    ∀ᵐ ω ∂μ, Tendsto (fun m => exposure ξ (b m) (B m ω)) atTop
      (𝓝 (activeExposure ξ entryLimit B0 (V ω))) := by
  filter_upwards [ae_all_iff.mpr hadmissible,hthreshold,hactive] with ω hB hne ha
  by_cases hv : entryLimit < V ω
  · simp only [activeExposure,if_pos hv]
    exact (continuousAt_exposure_pair hξ hentryLimit).tendsto.comp (hb.prodMk_nhds (ha hv))
  · have hvl : V ω < entryLimit := lt_of_le_of_ne (le_of_not_gt hv) hne
    simp only [activeExposure,if_neg hv]
    exact inactive_exposure_tendsto hvl hb hB

lemma activeExposure_bounds {ξ entryLimit : ℝ} (hξ : 0 < ξ) (hentryLimit : 0 < entryLimit)
    (B0 : ℝ → ℝ) (v : ℝ) : activeExposure ξ entryLimit B0 v ∈ Icc (0 : ℝ) 1 := by
  unfold activeExposure
  split_ifs
  · exact ⟨exposure_nonneg hξ hentryLimit,exposure_le_one _ _ _⟩
  · norm_num

theorem integral_entry_test_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (B : ℕ → Ω → ℝ) (B0 : ℝ → ℝ)
    (_hV : Measurable V) (hB : ∀ m, Measurable (B m)) (_hB0 : Measurable B0)
    {ξ entryLimit : ℝ} (hξ : 0 < ξ) (hentryLimit : 0 < entryLimit)
    (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hlp : ∀ m, 0 < l m)
    (hb : Tendsto b atTop (𝓝 entryLimit)) (hl : Tendsto l atTop (𝓝 entryLimit))
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hthreshold : ∀ᵐ ω ∂μ, V ω ≠ entryLimit)
    (hactive : ∀ᵐ ω ∂μ, entryLimit < V ω →
      Tendsto (fun m => B m ω) atTop (𝓝 (B0 (V ω))))
    (f : ℝ × ℝ → ℝ) (hf : Continuous f) (K : ℝ)
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f (x,y)| ≤ K) :
    Tendsto (fun m => ∫ ω, f (exposure ξ (b m) (B m ω),
      exposure ξ (l m) (B m ω)) ∂μ) atTop
      (𝓝 (∫ ω, f (activeExposure ξ entryLimit B0 (V ω),activeExposure ξ entryLimit B0 (V ω)) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => K)
  · intro m
    exact (hf.measurable.comp
      (((continuous_exposure hξ (hbp m)).measurable.comp (hB m)).prodMk
        ((continuous_exposure hξ (hlp m)).measurable.comp (hB m)))).aestronglyMeasurable
  · exact integrable_const _
  · intro m
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact hK _ ⟨exposure_nonneg hξ (hbp m),exposure_le_one _ _ _⟩
        _ ⟨exposure_nonneg hξ (hlp m),exposure_le_one _ _ _⟩
  · filter_upwards [entry_exposure_tendsto_ae μ V B B0 hξ hentryLimit b hb hadmissible hthreshold hactive,
      entry_exposure_tendsto_ae μ V B B0 hξ hentryLimit l hl hadmissible hthreshold hactive]
      with ω hx hy
    exact hf.continuousAt.tendsto.comp (hx.prodMk_nhds hy)

theorem tilted_integral_tendsto_fixed_carrier (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ) (Y0 : Ω → ℝ)
    (hX : ∀ m, Measurable (X m)) (hY : ∀ m, Measurable (Y m))
    (hXb : ∀ m, ∀ᵐ ω ∂μ, X m ω ∈ Icc (0 : ℝ) 1)
    {A : ℝ} (_hA : 0 ≤ A) (hYb : ∀ m, ∀ᵐ ω ∂μ, |Y m ω| ≤ A)
    (hYlim : ∀ᵐ ω ∂μ, Tendsto (fun m => Y m ω) atTop (𝓝 (Y0 ω)))
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, Y m ω ∂μ.tilted (fun ω => u m*X m ω))
      atTop (𝓝 (∫ ω, Y0 ω ∂μ)) := by
  have hsmall : ∀ᶠ m in atTop, |u m| ≤ 1 :=
    (hu.norm.eventually (Iio_mem_nhds (by norm_num : ‖(0 : ℝ)‖<1))).mono fun _ h => by simpa using h.le
  have hzero : ∀ᵐ ω ∂μ, Tendsto (fun m => u m*X m ω) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.mpr hXb] with ω hω
    apply squeeze_zero_norm (fun m => ?_) (by simpa only [norm_zero] using hu.norm)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hω m).1]
    exact (mul_le_mul_of_nonneg_left (hω m).2 (abs_nonneg _)).trans_eq (mul_one _)
  have hden : Tendsto (fun m => ∫ ω, Real.exp (u m*X m ω) ∂μ) atTop (𝓝 1) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (f := fun _ : Ω => (1 : ℝ))
      (fun _ : Ω => Real.exp 1)
      (Eventually.of_forall fun m => ((hX m).const_mul (u m)).exp.aestronglyMeasurable)
      (show ∀ᶠ m in atTop, ∀ᵐ ω ∂μ, ‖Real.exp (u m*X m ω)‖ ≤ Real.exp 1 from by
        filter_upwards [hsmall] with m hm
        filter_upwards [hXb m] with ω hω
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right (le_abs_self (u m)) hω.1
        nlinarith [hω.1,hω.2])
      (integrable_const _) (hzero.mono fun ω hω => by
        convert! (Real.continuous_exp.tendsto 0).comp hω using 1
        norm_num)
    simpa using hh
  have hnum : Tendsto (fun m => ∫ ω, Real.exp (u m*X m ω)*Y m ω ∂μ)
      atTop (𝓝 (∫ ω, Y0 ω ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => Real.exp 1*A)
    · exact Eventually.of_forall fun m =>
        ((((hX m).const_mul (u m)).exp).mul (hY m)).aestronglyMeasurable
    · filter_upwards [hsmall] with m hm
      filter_upwards [hXb m,hYb m] with ω hω hYω
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul _ hYω (abs_nonneg _) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (le_abs_self (u m)) hω.1
      nlinarith [hω.1,hω.2]
    · exact integrable_const _
    · filter_upwards [hzero,hYlim] with ω hx hy
      have he : Tendsto (fun m => Real.exp (u m*X m ω)) atTop (𝓝 1) := by
        convert! (Real.continuous_exp.tendsto 0).comp hx using 1
        norm_num
      simpa only [one_mul] using he.mul hy
  have he (m : ℕ) : (∫ ω, Y m ω ∂μ.tilted (fun ω => u m*X m ω))=
      (∫ ω, Real.exp (u m*X m ω)*Y m ω ∂μ)/(∫ ω, Real.exp (u m*X m ω) ∂μ) := by
    rw [integral_tilted,← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by simp only [smul_eq_mul]; ring
  simp_rw [he]
  convert! hnum.div hden (by norm_num : (1 : ℝ)≠0) using 1
  simp only [div_one]

def eligibility (r x : ℝ) : ℝ := min 1 (max 0 (4*x/r-1))

lemma continuous_eligibility (r : ℝ) : Continuous (eligibility r) := by
  unfold eligibility
  fun_prop

lemma eligibility_bounds (r x : ℝ) : eligibility r x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

lemma eligibility_zero {r x : ℝ} (hr : 0 < r) (hx : x ≤ r/4) :
    eligibility r x=0 := by
  have h : 4*x/r-1 ≤ 0 := by apply sub_nonpos.mpr; apply (div_le_one hr).mpr; nlinarith
  simp [eligibility,max_eq_left h]

lemma eligibility_one {r x : ℝ} (hr : 0 < r) (hx : r/2 ≤ x) :
    eligibility r x=1 := by
  have h : 1 ≤ 4*x/r-1 := by
    have hh : 2 ≤ 4*x/r := (le_div_iff₀ hr).mpr (by nlinarith)
    linarith
  exact min_eq_left (h.trans (le_max_right _ _))

lemma eligibility_majorizes (r : ℝ) (hr : 0 < r) (hr2 : r < 2)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    x ≤ r/2+(1-r/2)*eligibility r x := by
  by_cases h : r/2 ≤ x
  · rw [eligibility_one hr h]
    linarith [hx.2]
  · have hp := mul_nonneg (show 0 ≤ 1-r/2 by linarith) (eligibility_bounds r x).1
    linarith [le_of_not_ge h]

theorem eligible_mass_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1)
    {r : ℝ} (hr : 0 < r) (hr2 : r < 2) (hmean : ∫ ω, X ω ∂μ=r) :
    r/(2-r) ≤ ∫ ω, eligibility r (X ω) ∂μ := by
  have hI : Integrable X μ := Integrable.of_mem_Icc 0 1 hX.aemeasurable hXb
  have hJ : Integrable (fun ω => eligibility r (X ω)) μ :=
    Integrable.of_mem_Icc 0 1 ((continuous_eligibility r).measurable.comp hX).aemeasurable
      (Eventually.of_forall fun ω => eligibility_bounds r (X ω))
  have hb := integral_mono_ae hI
    ((integrable_const (r/2)).add (hJ.const_mul (1-r/2)))
    (hXb.mono fun ω hω => eligibility_majorizes r hr hr2 hω)
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const _) (hJ.const_mul _),integral_const_mul,
    integral_const,probReal_univ,one_smul,hmean] at hb
  apply (div_le_iff₀ (sub_pos.mpr hr2)).mpr
  nlinarith

theorem weighted_ratio_positive (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w h : Ω → ℝ) (hw : Measurable w) (hh : Measurable h)
    {a A : ℝ} (_ha : 0 < a) (hA : 0 ≤ A)
    (hwb : ∀ᵐ ω ∂μ, w ω ∈ Icc (0 : ℝ) 1)
    (hhb : ∀ᵐ ω ∂μ, |h ω| ≤ A)
    (helig : ∀ᵐ ω ∂μ, 0 < w ω → a ≤ h ω)
    (hwpos : 0 < ∫ ω, w ω ∂μ) :
    a ≤ (∫ ω, w ω*h ω ∂μ)/(∫ ω, w ω ∂μ) := by
  have hwI : Integrable w μ := Integrable.of_mem_Icc 0 1 hw.aemeasurable hwb
  have hwh : Integrable (fun ω => w ω*h ω) μ := by
    apply Integrable.of_bound (hw.mul hh).aestronglyMeasurable A
    filter_upwards [hwb,hhb] with ω hwω hhω
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hwω.1]
    exact (mul_le_mul_of_nonneg_left hhω hwω.1).trans
      (by nlinarith [hwω.2])
  have hb := integral_mono_ae (hwI.const_mul a) hwh (by
    filter_upwards [hwb,helig] with ω hwω hω
    by_cases hz : w ω=0
    · simp [hz]
    · have hp : 0 < w ω := lt_of_le_of_ne hwω.1 (Ne.symm hz)
      nlinarith [hω hp])
  rw [integral_const_mul] at hb
  exact (le_div_iff₀ hwpos).mpr hb

end FCAppendix.Affine.Uniform06.EntryActiveLimit
