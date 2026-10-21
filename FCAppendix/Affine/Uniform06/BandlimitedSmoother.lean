import Mathlib

set_option autoImplicit false
noncomputable section

namespace FCAppendix.Affine.Uniform06.BandlimitedSmoother

open MeasureTheory Set Filter
open scoped FourierTransform

def bump : ContDiffBump (0:ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def bumpSchwartz : SchwartzMap ℝ ℝ :=
  bump.hasCompactSupport.toSchwartzMap bump.contDiff

def g : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM bumpSchwartz

@[simp] theorem g_apply (w : ℝ) : g w = (bump w : ℂ) := by
  simp [g, bumpSchwartz]

@[simp] theorem g_neg (w : ℝ) : g (-w) = g w := by
  simp only [g_apply, bump.neg]

theorem g_zero_outside {w : ℝ} (hw : 2 ≤ |w|) : g w = 0 := by
  rw [g_apply]
  have hz := bump.zero_of_le_dist (x := w)
    (by simpa [bump, Real.dist_eq, abs_sub_comm] using hw)
  simp [hz]

def H : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) g g

theorem H_integral (w : ℝ) : H w = ∫ u, g u*g (w-u) := by
  rw [H, SchwartzMap.convolution_apply]
  rfl

theorem H_zero_outside {w : ℝ} (hw : 4 ≤ |w|) : H w = 0 := by
  rw [H_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  by_cases hu : 2 ≤ |u|
  · simp [g_zero_outside hu]
  · have hv : 2 ≤ |w-u| := by
      have htri : |w| ≤ |u|+|w-u| := by
        convert! abs_add_le u (w-u) using 1
        congr 1
        ring
      linarith
    simp [g_zero_outside hv]

theorem fourier_g_neg (w : ℝ) : (𝓕 g) (-w) = (𝓕 g) w := by
  have hn : (fun u : ℝ => g (-u)) = (fun u => g u) := funext g_neg
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ)
    (fun u : ℝ => g u) w
  change (𝓕 (fun u : ℝ => g (-u))) w = (𝓕 (fun u : ℝ => g u)) (-w) at h
  rw [hn] at h
  exact h.symm

theorem fourier_g_conj (w : ℝ) :
    star ((𝓕 g) w) = (𝓕 g) (-w) := by
  change star (𝓕 (fun u : ℝ => g u) w) = 𝓕 (fun u : ℝ => g u) (-w)
  rw [Complex.star_def, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [smul_eq_mul, map_mul, g_apply, Complex.conj_ofReal,
    ← Complex.exp_conj, map_mul, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem fourier_g_im_zero (w : ℝ) : ((𝓕 g) w).im = 0 := by
  have h := congrArg Complex.im ((fourier_g_conj w).trans (fourier_g_neg w))
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

theorem fourier_H_square (w : ℝ) : (𝓕 H) w = ((𝓕 g) w)^2 := by
  rw [H, SchwartzMap.fourier_convolution]
  simp [SchwartzMap.pairing_apply_apply, pow_two]

def base : SchwartzMap ℝ ℝ := SchwartzMap.postcompCLM Complex.reCLM (𝓕 H)

theorem base_eq_re_square (w : ℝ) : base w = ((𝓕 g) w).re^2 := by
  simp only [base, SchwartzMap.postcompCLM_apply, Complex.reCLM_apply,
    fourier_H_square, pow_two, Complex.mul_re, fourier_g_im_zero,
    mul_zero, sub_zero]

theorem base_nonneg (w : ℝ) : 0 ≤ base w := by
  rw [base_eq_re_square]
  positivity

theorem ofReal_base (w : ℝ) : (base w : ℂ) = (𝓕 H) w := by
  apply Complex.ext
  · simp [base]
  · rw [fourier_H_square]
    simp [pow_two, fourier_g_im_zero]

theorem base_eq_norm_sq (w : ℝ) : base w = ‖(𝓕 g) w‖^2 := by
  rw [base_eq_re_square]
  have h := congrArg Complex.re (Complex.mul_conj' ((𝓕 g) w))
  simpa [Complex.mul_re, fourier_g_im_zero, pow_two] using h

theorem bump_integral_pos : 0 < ∫ u, bump u := by
  apply (integral_pos_iff_support_of_nonneg (fun u => bump.nonneg)
    bumpSchwartz.integrable).mpr
  rw [bump.support_eq]
  exact Metric.measure_ball_pos volume (0:ℝ) (by norm_num [bump])

theorem fourier_g_zero : (𝓕 g) 0 = ((∫ u, bump u : ℝ) : ℂ) := by
  change 𝓕 (fun u : ℝ => g u) 0 = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    g_apply, integral_complex_ofReal]

theorem base_zero_pos : 0 < base 0 := by
  rw [base_eq_re_square, fourier_g_zero, Complex.ofReal_re]
  exact sq_pos_of_pos bump_integral_pos

theorem base_positive_near_zero :
    ∃ δ > (0:ℝ), ∀ w, |w| ≤ δ → base 0/2 ≤ base w := by
  have hnear : {w : ℝ | base 0/2 < base w} ∈ nhds 0 :=
    base.continuous.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by linarith [base_zero_pos]))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ/2, by linarith, ?_⟩
  intro w hw
  have hw' : w ∈ Metric.ball (0:ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith
  exact (hball hw').le

def Z : ℝ := ∫ u, base u

theorem Z_pos : 0 < Z := by
  obtain ⟨δ, hδ, hbase⟩ := base_positive_near_zero
  apply (integral_pos_iff_support_of_nonneg base_nonneg base.integrable).mpr
  have hs : Ioo (-δ) δ ⊆ Function.support (fun u : ℝ => base u) := by
    intro u hu
    apply ne_of_gt
    have hb := hbase u (abs_le.mpr ⟨hu.1.le, hu.2.le⟩)
    linarith [base_zero_pos]
  have hi : 0 < volume (Ioo (-δ) δ) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact hi.trans_le (measure_mono hs)

def K : SchwartzMap ℝ ℝ := Z⁻¹ • base

@[simp] theorem K_apply (w : ℝ) : K w = base w/Z := by
  simp [K, div_eq_mul_inv, mul_comm]

theorem K_nonneg (w : ℝ) : 0 ≤ K w := by
  rw [K_apply]
  exact div_nonneg (base_nonneg w) Z_pos.le

theorem K_integrable : Integrable (fun w : ℝ => K w) := K.integrable

theorem K_mass : (∫ w : ℝ, K w) = 1 := by
  simp only [K, smul_apply, smul_eq_mul, integral_const_mul]
  change Z⁻¹*Z=1
  exact inv_mul_cancel₀ Z_pos.ne'

theorem K_first_moment_integrable : Integrable (fun w : ℝ => K w*|w|) := by
  have h := K.integrable_pow_mul volume 1
  simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (K_nonneg _),
    mul_comm] using h

theorem K_positive_near_zero :
    ∃ δ > (0:ℝ), ∃ c > (0:ℝ), ∀ w, |w| ≤ δ → c ≤ K w := by
  obtain ⟨δ,hδ,hbase⟩ := base_positive_near_zero
  have hb0 := base_zero_pos
  have hZ := Z_pos
  refine ⟨δ,hδ,base 0/(2*Z),by positivity,?_⟩
  intro w hw
  rw [K_apply]
  have h := (div_le_div_iff_of_pos_right Z_pos).mpr (hbase w hw)
  convert! h using 1
  field_simp

def amplitude (s : ℝ) : ℂ := H (-s)/(Z:ℂ)

theorem amplitude_continuous : Continuous amplitude := by
  unfold amplitude
  fun_prop

theorem amplitude_integrable : Integrable amplitude := by
  exact (H.integrable.comp_neg).div_const (Z:ℂ)

theorem amplitude_zero_outside {s : ℝ} (hs : 4 ≤ |s|) : amplitude s = 0 := by
  have hz := H_zero_outside (w := -s) (by simpa using hs)
  simp [amplitude, hz]

theorem amplitude_uniform_bound :
    ∃ B > (0:ℝ), ∀ s : ℝ, ‖amplitude s‖ ≤ B := by
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-4:ℝ) 4)).bddAbove_image
    amplitude_continuous.norm.continuousOn
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro s
  by_cases hs : s ∈ Icc (-4:ℝ) 4
  · exact (hB ⟨s,hs,rfl⟩).trans (le_max_left B 1)
  · have hs' : 4 ≤ |s| := by
      by_contra h
      have hlt : |s| < 4 := lt_of_not_ge h
      exact hs ⟨(abs_lt.mp hlt).1.le,(abs_lt.mp hlt).2.le⟩
    rw [amplitude_zero_outside hs', norm_zero]
    exact (show (0:ℝ) ≤ 1 by norm_num).trans (le_max_right B 1)

theorem K_inverse_representation (w : ℝ) :
    (K w : ℂ) = 𝓕⁻ amplitude w := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  simp only [amplitude, neg_neg]
  rw [K_apply, Complex.ofReal_div, ofReal_base]
  change 𝓕 (fun s : ℝ => H s) w / (Z:ℂ) = _
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with s
  simp [smul_eq_mul, mul_div_assoc]

theorem K_integral_representation (w : ℝ) :
    (K w : ℂ) =
      ∫ s : ℝ, Complex.exp (((2*Real.pi*s*w:ℝ):ℂ)*Complex.I)*amplitude s := by
  rw [K_inverse_representation, Real.fourierInv_eq']
  simp only [smul_eq_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    simp only [Real.inner_apply]
    congr 2
    push_cast
    ring

theorem Z_eq_original_square : Z = ∫ u, ‖g u‖^2 := by
  unfold Z
  simp_rw [base_eq_norm_sq]
  exact SchwartzMap.integral_norm_sq_fourier g

theorem H_zero_eq_Z : H 0 = (Z:ℂ) := by
  rw [H_integral]
  simp_rw [zero_sub, g_neg, g_apply, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  rw [Z_eq_original_square]
  apply integral_congr_ae
  filter_upwards [] with u
  simp [g_apply, Complex.norm_real, Real.norm_eq_abs, pow_two]

theorem amplitude_zero : amplitude 0 = 1 := by
  have hZ : (Z:ℂ) ≠ 0 := by exact_mod_cast Z_pos.ne'
  simp [amplitude, H_zero_eq_Z, hZ]

def scaledK (T w : ℝ) : ℝ := T*K (T*w)

def rawAmplitude (T s : ℝ) : ℂ := amplitude (s/(2*Real.pi*T))

theorem rawAmplitude_uniform_bound :
    ∃ B > (0:ℝ), ∀ T s : ℝ, ‖rawAmplitude T s‖ ≤ B := by
  obtain ⟨B,hB,hamp⟩ := amplitude_uniform_bound
  exact ⟨B,hB,fun T s => hamp (s/(2*Real.pi*T))⟩

theorem scaledK_nonneg {T : ℝ} (hT : 0 < T) (w : ℝ) : 0 ≤ scaledK T w :=
  mul_nonneg hT.le (K_nonneg _)

theorem scaledK_continuous (T : ℝ) : Continuous (scaledK T) := by
  unfold scaledK
  fun_prop

theorem scaledK_integrable {T : ℝ} (hT : 0 < T) : Integrable (scaledK T) :=
  (K_integrable.comp_mul_left' hT.ne').const_mul T

theorem scaledK_mass {T : ℝ} (hT : 0 < T) : (∫ w, scaledK T w) = 1 := by
  simp only [scaledK]
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hT), smul_eq_mul, K_mass]
  field_simp [hT.ne']

theorem scaledK_first_moment_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (fun w => scaledK T w*|w|) := by
  have h := K_first_moment_integrable.comp_mul_left' hT.ne'
  convert! h using 1
  funext w
  simp only [scaledK, abs_mul, abs_of_pos hT]
  ring

theorem scaledK_first_moment {T : ℝ} (hT : 0 < T) :
    (∫ w, scaledK T w*|w|) = (∫ u, K u*|u|)/T := by
  have hid : (fun w => scaledK T w*|w|) =
      (fun w => K (T*w)*|T*w|) := by
    funext w
    simp only [scaledK, abs_mul, abs_of_pos hT]
    ring
  rw [hid]
  rw [Measure.integral_comp_mul_left (fun u : ℝ => K u * |u|) T]
  simp [abs_of_pos (inv_pos.mpr hT), smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem scaledK_positive_near_zero :
    ∃ δ > (0:ℝ), ∃ c > (0:ℝ), ∀ T > (0:ℝ), ∀ w,
      |w| ≤ δ/T → c*T ≤ scaledK T w := by
  obtain ⟨δ,hδ,c,hc,hK⟩ := K_positive_near_zero
  refine ⟨δ,hδ,c,hc,?_⟩
  intro T hT w hw
  have hTw : |T*w| ≤ δ := by
    rw [abs_mul, abs_of_pos hT]
    have h := (le_div_iff₀ hT).mp hw
    nlinarith
  have h := mul_le_mul_of_nonneg_left (hK _ hTw) hT.le
  simpa [scaledK, mul_comm] using h

theorem rawAmplitude_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (rawAmplitude T) :=
  amplitude_integrable.comp_div (by positivity)

theorem rawAmplitude_continuous (T : ℝ) : Continuous (rawAmplitude T) := by
  exact amplitude_continuous.comp (continuous_id.div_const _)

theorem rawAmplitude_zero (T : ℝ) : rawAmplitude T 0 = 1 := by
  simp [rawAmplitude, amplitude_zero]

theorem rawAmplitude_zero_outside {T s : ℝ} (hT : 0 < T)
    (hs : 8*Real.pi*T ≤ |s|) : rawAmplitude T s = 0 := by
  apply amplitude_zero_outside
  rw [abs_div, abs_of_pos (show 0 < 2*Real.pi*T by positivity)]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem scaledK_raw_inverse {T : ℝ} (hT : 0 < T) (w : ℝ) :
    (scaledK T w : ℂ) = (2*Real.pi:ℂ)⁻¹ *
      ∫ s : ℝ, rawAmplitude T s*Complex.exp ((s*w:ℝ)*Complex.I) := by
  let c : ℝ := 2*Real.pi*T
  have hc : 0 < c := by dsimp [c]; positivity
  have hchange := Measure.integral_comp_div
    (fun u : ℝ => amplitude u * Complex.exp (((c*u*w:ℝ):ℂ)*Complex.I)) c
  have hfun : (fun s : ℝ =>
      amplitude (s/c)*Complex.exp (((c*(s/c)*w:ℝ):ℂ)*Complex.I)) =
      (fun s => rawAmplitude T s*Complex.exp ((s*w:ℝ)*Complex.I)) := by
    funext s
    dsimp [rawAmplitude, c]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero, hT.ne']
  rw [hfun, abs_of_pos hc] at hchange
  rw [hchange]
  have hrep := K_integral_representation (T*w)
  rw [scaledK, Complex.ofReal_mul, hrep]
  have hint : (∫ s : ℝ,
      Complex.exp (((2*Real.pi*s*(T*w):ℝ):ℂ)*Complex.I)*amplitude s) =
      ∫ s : ℝ, amplitude s*Complex.exp (((c*s*w:ℝ):ℂ)*Complex.I) := by
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp [c]
    calc
      _ = amplitude s*Complex.exp
          (((2*Real.pi*s*(T*w):ℝ):ℂ)*Complex.I) := mul_comm _ _
      _ = _ := by
        congr 2
        push_cast
        ring
  rw [hint]
  rw [Complex.real_smul]
  have hscalar : (2*Real.pi:ℂ)⁻¹*(c:ℂ)=(T:ℂ) := by
    dsimp [c]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hscalar]

theorem first_moment_tendsto_zero :
    Tendsto (fun n : ℕ => ∫ w, scaledK ((n:ℝ)+1) w*|w|) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hz := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ u, K u*|u|) atTop
    (nhds (∫ u, K u*|u|))).div_atTop ht
  have he (n : ℕ) : (∫ w, scaledK ((n:ℝ)+1) w*|w|) = (∫ u, K u*|u|)/((n:ℝ)+1) :=
    scaledK_first_moment (by positivity : 0 < (n:ℝ)+1)
  simp only [he]
  exact hz

end FCAppendix.Affine.Uniform06.BandlimitedSmoother
