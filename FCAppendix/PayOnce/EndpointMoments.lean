import FCAppendix.PayOnce.SharpEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace FCAppendix.PayOnce.EndpointMoments

open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem integral_pow_eq_tail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ) (hfnn : 0 ≤ᵐ[μ] f) (j : ℕ) :
    (∫ x, f x ^ (j + 1) ∂μ) =
      (j + 1 : ℝ) * ∫ u in Ioi (0 : ℝ), μ.real {x | u < f x} * u ^ j := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have key := lintegral_rpow_eq_lintegral_meas_lt_mul μ hfnn hf hj
  have hpow : (fun x => ENNReal.ofReal (f x ^ ((j : ℝ) + 1))) =
      (fun x => ENNReal.ofReal (f x ^ (j + 1))) := by
    funext x
    rw [← Nat.cast_add_one, Real.rpow_natCast]
  rw [hpow] at key
  simp only [add_sub_cancel_right, Real.rpow_natCast] at key
  have htail : Measurable (fun u : ℝ => μ {x | u < f x}) :=
    Antitone.measurable (fun _ _ h => measure_mono (fun _ hx => h.trans_lt hx))
  have htailR : Measurable (fun u : ℝ => μ.real {x | u < f x}) := htail.ennreal_toReal
  have hnn : 0 ≤ᵐ[μ] fun x => f x ^ (j + 1) := hfnn.mono (fun _ h => pow_nonneg h _)
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hf.pow_const _).aestronglyMeasurable]
  rw [key, ENNReal.toReal_mul, ENNReal.toReal_ofReal hj.le]
  congr 1
  have hrnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun u => μ.real {x | u < f x} * u ^ j) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact mul_nonneg measureReal_nonneg (pow_nonneg (le_of_lt hu) _)
  rw [integral_eq_lintegral_of_nonneg_ae hrnn ((htailR.mul (measurable_id.pow_const j)).aestronglyMeasurable)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem integral_pow_eq_tail_interval {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ) (hfnn : 0 ≤ᵐ[μ] f)
    {d : ℝ} (hd : 0 ≤ d) (hfd : f ≤ᵐ[μ] fun _ => d) (j : ℕ) :
    (∫ x, f x ^ (j + 1) ∂μ) =
      (j + 1 : ℝ) * ∫ u in 0..d, μ.real {x | u < f x} * u ^ j := by
  rw [integral_pow_eq_tail μ hf hfnn j, intervalIntegral.integral_of_le hd]
  congr 1
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi Ioc_subset_Ioi_self
  apply Eventually.of_forall
  intro u hu
  have hdu : d < u := by
    simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hu
    exact hu.2 hu.1
  have hzero : μ {x | u < f x} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hfd] with x hx
    exact not_lt.mpr (hx.trans hdu.le)
  simp [measureReal_def, hzero]

theorem excess_moment_tail (μ : Measure ℝ) [IsFiniteMeasure μ]
    {M t : ℝ} (htM : t ≤ M) (hle : ∀ᵐ w ∂μ, w ≤ M) (j : ℕ) :
    (∫ w, max (w - t) 0 ^ (j + 1) ∂μ) =
      (j + 1 : ℝ) * ∫ u in 0..(M - t), μ.real (Ioi (t + u)) * u ^ j := by
  have hd : 0 ≤ M - t := sub_nonneg.mpr htM
  rw [integral_pow_eq_tail_interval μ (f := fun w => max (w - t) 0)
    ((measurable_id.sub_const t).max measurable_const).aemeasurable
    (Eventually.of_forall (fun _ => le_max_right _ _)) hd
    (hle.mono (fun w hw => max_le (by linarith) hd)) j]
  congr 1
  rw [intervalIntegral.integral_of_le hd, intervalIntegral.integral_of_le hd]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hset : {w : ℝ | u < max (w - t) 0} = Ioi (t + u) := by
    ext w
    simp only [mem_setOf_eq, mem_Ioi, lt_max_iff]
    constructor
    · intro h
      rcases h with h | h
      · linarith
      · linarith [hu.1]
    · intro h
      exact Or.inl (by linarith)
  dsimp only
  rw [hset]

theorem tendsto_rescaled_tail_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    {M γ c : ℝ} (hγ : 0 < γ) (hc : 0 < c)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) (j : ℕ) :
    Tendsto (fun d : ℝ => ∫ z in (0 : ℝ)..1,
      μ.real (Ioi (M - d * (1 - z))) / d ^ γ * z ^ j) (𝓝[>] 0)
      (𝓝 (c * ∫ z in (0 : ℝ)..1, (1 - z) ^ γ * z ^ j)) := by
  let T : ℝ → ℝ := fun u => μ.real (Ioi (M - u))
  have hTnn (u : ℝ) : 0 ≤ T u := measureReal_nonneg
  have hTm : Measurable T := by
    apply Monotone.measurable
    intro u v huv
    exact measureReal_mono (Ioi_subset_Ioi (by linarith))
  have hevent : ∀ᶠ u in 𝓝[>] (0 : ℝ), T u / u ^ γ < c + 1 :=
    htail.eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hδbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  have hfactor {d z : ℝ} (hd : 0 < d) (hz : z ∈ Ioo (0 : ℝ) 1) :
      T (d * (1 - z)) / d ^ γ * z ^ j =
        (T (d * (1 - z)) / (d * (1 - z)) ^ γ) * ((1 - z) ^ γ * z ^ j) := by
    have ha : 0 < 1 - z := sub_pos.mpr hz.2
    rw [Real.mul_rpow hd.le ha.le]
    have hdγ := Real.rpow_pos_of_pos hd γ
    have haγ := Real.rpow_pos_of_pos ha γ
    field_simp
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (l := 𝓝[>] (0 : ℝ))
    (F := fun d z => T (d * (1 - z)) / d ^ γ * z ^ j)
    (f := fun z => c * ((1 - z) ^ γ * z ^ j)) (fun _ => c + 1)
    (Eventually.of_forall (fun d =>
      ((hTm.comp (measurable_const.mul (measurable_const.sub measurable_id))).div_const
        (d ^ γ) |>.mul (measurable_id.pow_const j)).aestronglyMeasurable)) ?_
    (integrable_const _) ?_
  · simp only [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one] at hlim
    simpa only [intervalIntegral.integral_const_mul] using hlim
  · filter_upwards [Ioo_mem_nhdsGT hδ] with d hd
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with z hz
    have ha : 0 < 1 - z := sub_pos.mpr hz.2
    have hnonneg : 0 ≤ T (d * (1 - z)) / (d * (1 - z)) ^ γ * ((1 - z) ^ γ * z ^ j) :=
      mul_nonneg (div_nonneg (hTnn _) (Real.rpow_nonneg (mul_pos hd.1 ha).le _))
        (mul_nonneg (Real.rpow_nonneg ha.le _) (pow_nonneg hz.1.le _))
    rw [hfactor hd.1 hz, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have ha : 0 < 1 - z := sub_pos.mpr hz.2
    have hz1 : z ^ j ≤ 1 := pow_le_one₀ hz.1.le hz.2.le
    have ha1 : (1 - z) ^ γ ≤ 1 := Real.rpow_le_one ha.le (by linarith [hz.1]) hγ.le
    have hdsub : d * (1 - z) ∈ Ioo (0 : ℝ) δ :=
      ⟨mul_pos hd.1 ha, (mul_lt_of_lt_one_right hd.1 (by linarith [hz.1])).trans hd.2⟩
    have hb := (show T (d * (1 - z)) / (d * (1 - z)) ^ γ < c + 1 from hδbound hdsub).le
    have hw : 0 ≤ (1 - z) ^ γ * z ^ j := mul_nonneg (Real.rpow_nonneg ha.le _) (pow_nonneg hz.1.le _)
    have hw1 : (1 - z) ^ γ * z ^ j ≤ 1 := mul_le_one₀ ha1 (pow_nonneg hz.1.le _) hz1
    exact (mul_le_mul_of_nonneg_right hb hw).trans (mul_le_of_le_one_right (by linarith) hw1)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with z hz
    have ha : 0 < 1 - z := sub_pos.mpr hz.2
    have harg : Tendsto (fun d : ℝ => d * (1 - z)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using ((tendsto_id : Tendsto (fun d : ℝ => d) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const (1 - z)
      · filter_upwards [self_mem_nhdsWithin] with d hd
        exact mul_pos hd ha
    have hh := (htail.comp harg).mul_const ((1 - z) ^ γ * z ^ j)
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact (hfactor hd hz).symm

theorem excess_moment_rescale (μ : Measure ℝ) [IsFiniteMeasure μ]
    {M d γ : ℝ} (hd : 0 < d) (hle : ∀ᵐ w ∂μ, w ≤ M) (j : ℕ) :
    (∫ w, max (w - (M - d)) 0 ^ (j + 1) ∂μ) / d ^ (γ + (j + 1 : ℕ)) =
      (j + 1 : ℝ) * ∫ z in (0 : ℝ)..1,
        μ.real (Ioi (M - d * (1 - z))) / d ^ γ * z ^ j := by
  rw [excess_moment_tail μ (by linarith) hle j]
  simp only [sub_sub_cancel]
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun u => μ.real (Ioi (M - d + u)) * u ^ j) d
  simp only [smul_eq_mul, mul_zero, mul_one] at hscale
  rw [← hscale]
  have hint : (∫ x in (0 : ℝ)..1, μ.real (Ioi (M - d + d * x)) * (d * x) ^ j) =
      d ^ j * ∫ x in (0 : ℝ)..1, μ.real (Ioi (M - d * (1 - x))) * x ^ j := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    have he : M - d + d * x = M - d * (1 - x) := by ring
    dsimp only
    rw [he, mul_pow]
    ring
  rw [hint]
  have hrpow : d ^ (γ + (j + 1 : ℕ)) = d ^ γ * d ^ (j + 1) := by
    rw [Real.rpow_add hd, Real.rpow_natCast]
  rw [hrpow, pow_succ]
  have hdiv : (∫ x in (0 : ℝ)..1, μ.real (Ioi (M - d * (1 - x))) / d ^ γ * x ^ j) =
      (∫ x in (0 : ℝ)..1, μ.real (Ioi (M - d * (1 - x))) * x ^ j) / d ^ γ := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hdiv]
  have hdγ := Real.rpow_pos_of_pos hd γ
  field_simp

theorem tendsto_excess_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {M γ c : ℝ} (hγ : 0 < γ) (hc : 0 < c) (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) (j : ℕ) :
    Tendsto (fun d : ℝ =>
      (∫ w, max (w - (M - d)) 0 ^ (j + 1) ∂μ) / d ^ (γ + (j + 1 : ℕ)))
      (𝓝[>] 0) (𝓝 ((j + 1 : ℝ) * c * ∫ z in (0 : ℝ)..1, (1 - z) ^ γ * z ^ j)) := by
  have hh := (tendsto_rescaled_tail_integral μ hγ hc htail j).const_mul (j + 1 : ℝ)
  rw [← mul_assoc] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (excess_moment_rescale μ hd hle j).symm

open ManyProposers BoundedEndpoint SharpEndpoint

theorem integrable_excess_pow (μ : Measure ℝ) [IsFiniteMeasure μ]
    {M t : ℝ} (htM : t ≤ M) (hle : ∀ᵐ w ∂μ, w ≤ M) (j : ℕ) :
    Integrable (fun w => max (w - t) 0 ^ j) μ := by
  refine Integrable.mono' (integrable_const ((M - t) ^ j))
    (((continuous_id.sub continuous_const).max continuous_const).pow j).aestronglyMeasurable ?_
  filter_upwards [hle] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right _ _) _)]
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) (sub_nonneg.mpr htM)) j

theorem pStar_moment_envelope (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M t : ℝ} (ht : 0 < t) (htM : t ≤ M)
    (hle : ∀ᵐ w ∂μ, w ≤ M) (j : ℕ) :
    (∫ w, max (w - t) 0 ^ j ∂μ) / (M * ((n : ℝ) - 1) + (M - t)) ^ j ≤
        (∫ w, pStar n t w ^ j ∂μ) ∧
      (∫ w, pStar n t w ^ j ∂μ) ≤
        (∫ w, max (w - t) 0 ^ j ∂μ) / (t * ((n : ℝ) - 1)) ^ j := by
  have ha := nat_sub_one_pos hn
  have hM := ht.trans_le htM
  have hl : 0 < M * ((n : ℝ) - 1) + (M - t) :=
    add_pos_of_pos_of_nonneg (mul_pos hM ha) (sub_nonneg.mpr htM)
  have hE := integrable_excess_pow μ htM hle j
  have hP := integrable_pStar_pow μ hn ht j
  have hlow := integral_mono_ae (hE.div_const ((M * ((n : ℝ) - 1) + (M - t)) ^ j)) hP
    (hle.mono (fun w hw => by
      have hh := pow_le_pow_left₀ (div_nonneg (le_max_right _ _) hl.le)
        (pStar_gap_envelope hn ht hw).1 j
      simpa only [div_pow] using hh))
  have hup := integral_mono_ae hP (hE.div_const ((t * ((n : ℝ) - 1)) ^ j))
    (hle.mono (fun w hw => by
      have hh := pow_le_pow_left₀ (pStar_nonneg n t w) (pStar_gap_envelope hn ht hw).2 j
      simpa only [div_pow] using hh))
  rw [integral_div] at hlow hup
  exact ⟨hlow, hup⟩

theorem tendsto_pStar_moment_beta_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) (j : ℕ) :
    Tendsto (fun d : ℝ =>
      (∫ w, pStar n (M - d) w ^ (j + 1) ∂μ) / d ^ (γ + (j + 1 : ℕ)))
      (𝓝[>] 0) (𝓝 (((j + 1 : ℝ) * c * ∫ z in (0 : ℝ)..1, (1 - z) ^ γ * z ^ j) /
        (M * ((n : ℝ) - 1)) ^ (j + 1))) := by
  have hE := tendsto_excess_moment μ hγ hc hle htail j
  have ha := nat_sub_one_pos hn
  have hK : (M * ((n : ℝ) - 1)) ^ (j + 1) ≠ 0 := pow_ne_zero _ (mul_pos hM ha).ne'
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlow := hE.div (((tendsto_const_nhds (x := M * ((n : ℝ) - 1))).add hd).pow (j + 1)) (by simpa using hK)
  have hup := hE.div ((((tendsto_const_nhds (x := M)).sub hd).mul_const ((n : ℝ) - 1)).pow (j + 1))
    (by simpa using hK)
  simp only [add_zero, sub_zero] at hlow hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  all_goals
    filter_upwards [Ioo_mem_nhdsGT hM] with d hd'
    have hden : 0 < d ^ (γ + (j + 1 : ℕ)) := Real.rpow_pos_of_pos hd'.1 _
    have hb := pStar_moment_envelope μ hn (sub_pos.mpr hd'.2)
      (sub_le_self _ hd'.1.le) hle (j + 1)
    simp only [sub_sub_cancel] at hb
  · simpa only [Pi.div_apply, div_right_comm] using div_le_div_of_nonneg_right hb.1 hden.le
  · simpa only [Pi.div_apply, div_right_comm] using div_le_div_of_nonneg_right hb.2 hden.le

theorem integral_beta_eq_gamma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  calc
    ((∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) =
        Complex.betaIntegral (a : ℂ) (b : ℂ) := by
      rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      dsimp only
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1,
        Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
      push_cast
      rfl
    _ = Complex.Gamma (a : ℂ) * Complex.Gamma (b : ℂ) / Complex.Gamma ((a : ℂ) + b) :=
      Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa) (by simpa)
    _ = ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
      push_cast
      rfl

theorem moment_beta_constant {γ : ℝ} (hγ : 0 < γ) (j : ℕ) :
    (j + 1 : ℝ) * (∫ z in (0 : ℝ)..1, (1 - z) ^ γ * z ^ j) =
      Real.Gamma (γ + 1) * Real.Gamma ((j + 1 : ℕ) + 1) /
        Real.Gamma (γ + (j + 1 : ℕ) + 1) := by
  have hint : (∫ z in (0 : ℝ)..1, (1 - z) ^ γ * z ^ j) =
      Real.Gamma ((j : ℝ) + 1) * Real.Gamma (γ + 1) /
        Real.Gamma (((j : ℝ) + 1) + (γ + 1)) := by
    have hh := integral_beta_eq_gamma (a := (j : ℝ) + 1) (b := γ + 1) (by positivity) (by linarith)
    simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using hh
  rw [hint]
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Real.Gamma_add_one hj]
  have he : ((j : ℝ) + 1) + (γ + 1) = γ + (j + 1 : ℕ) + 1 := by push_cast; ring
  rw [he]
  push_cast
  ring

theorem tendsto_pStar_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) (j : ℕ) :
    Tendsto (fun d : ℝ =>
      (∫ w, pStar n (M - d) w ^ (j + 1) ∂μ) / d ^ (γ + (j + 1 : ℕ)))
      (𝓝[>] 0) (𝓝 ((c * Real.Gamma (γ + 1) * Real.Gamma ((j + 1 : ℕ) + 1) /
        Real.Gamma (γ + (j + 1 : ℕ) + 1)) / (M * ((n : ℝ) - 1)) ^ (j + 1))) := by
  have hh := tendsto_pStar_moment_beta_integral μ hn hM hγ hc hle htail j
  have he : (j + 1 : ℝ) * c * (∫ z in (0 : ℝ)..1, (1 - z) ^ γ * z ^ j) =
      c * Real.Gamma (γ + 1) * Real.Gamma ((j + 1 : ℕ) + 1) /
        Real.Gamma (γ + (j + 1 : ℕ) + 1) := by
    calc
      _ = c * ((j + 1 : ℝ) * (∫ z in (0 : ℝ)..1, (1 - z) ^ γ * z ^ j)) := by ring
      _ = _ := by rw [moment_beta_constant hγ j]; ring
  rwa [he] at hh

end FCAppendix.PayOnce.EndpointMoments
