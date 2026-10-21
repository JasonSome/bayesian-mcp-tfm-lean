import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

noncomputable section
namespace FCAppendix.Affine.Uniform06.IntervalRecovery

open MeasureTheory Set Filter

def intervalIndicator (a b : ℝ) : ℝ → ℝ :=
  (Icc a b).indicator (fun _ => 1)

def intervalMass (ν : Measure ℝ) (a b : ℝ) : ℝ :=
  ∫ w, intervalIndicator a b w ∂ν

def blurredMass (ν : Measure ℝ) (K : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ u, K u * intervalMass ν (a + u) (b + u)

theorem intervalIndicator_bounds (a b w : ℝ) :
    0 ≤ intervalIndicator a b w ∧ intervalIndicator a b w ≤ 1 := by
  unfold intervalIndicator
  by_cases h : w ∈ Icc a b <;> simp [h]

theorem intervalIndicator_measurable (a b : ℝ) :
    Measurable (intervalIndicator a b) :=
  measurable_const.indicator measurableSet_Icc

theorem intervalIndicator_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b : ℝ) : Integrable (intervalIndicator a b) ν :=
  (integrable_const (1 : ℝ)).indicator measurableSet_Icc

theorem intervalMass_eq_measure (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b : ℝ) : intervalMass ν a b = ν.real (Icc a b) :=
  integral_indicator_one measurableSet_Icc

theorem intervalMass_nonneg (ν : Measure ℝ) (a b : ℝ) :
    0 ≤ intervalMass ν a b :=
  integral_nonneg fun w => (intervalIndicator_bounds a b w).1

theorem intervalMass_le_total (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b : ℝ) : intervalMass ν a b ≤ ∫ _ : ℝ, (1 : ℝ) ∂ν := by
  exact integral_mono (intervalIndicator_integrable ν a b) (integrable_const 1)
    fun w => (intervalIndicator_bounds a b w).2

theorem intervalIndicator_shift_bound (a b u w : ℝ) :
    |intervalIndicator a b w - intervalIndicator (a + u) (b + u) w| ≤
      intervalIndicator (min a (a + u)) (max a (a + u)) w +
      intervalIndicator (min b (b + u)) (max b (b + u)) w := by
  by_cases h : a ≤ w ∧ w ≤ b
  · by_cases h' : a + u ≤ w ∧ w ≤ b + u
    · have h0 := add_nonneg
        (intervalIndicator_bounds (min a (a + u)) (max a (a + u)) w).1
        (intervalIndicator_bounds (min b (b + u)) (max b (b + u)) w).1
      simpa [intervalIndicator, h, h'] using h0
    · have hstrip :
          (min a (a + u) ≤ w ∧ w ≤ max a (a + u)) ∨
          (min b (b + u) ≤ w ∧ w ≤ max b (b + u)) := by
        rcases lt_or_ge w (a + u) with hw | hw
        · exact Or.inl ⟨(min_le_left _ _).trans h.1,
            hw.le.trans (le_max_right _ _)⟩
        · have hb : b + u < w := lt_of_not_ge fun hb => h' ⟨hw, hb⟩
          exact Or.inr ⟨(min_le_right _ _).trans hb.le,
            h.2.trans (le_max_left _ _)⟩
      rcases hstrip with hs | hs
      · simp only [intervalIndicator, Set.indicator, Set.mem_Icc,
          if_pos h, if_neg h', if_pos hs]
        split_ifs <;> norm_num
      · simp only [intervalIndicator, Set.indicator, Set.mem_Icc,
          if_pos h, if_neg h', if_pos hs]
        split_ifs <;> norm_num
  · by_cases h' : a + u ≤ w ∧ w ≤ b + u
    · have hstrip :
          (min a (a + u) ≤ w ∧ w ≤ max a (a + u)) ∨
          (min b (b + u) ≤ w ∧ w ≤ max b (b + u)) := by
        rcases lt_or_ge w a with hw | hw
        · exact Or.inl ⟨(min_le_right _ _).trans h'.1,
            hw.le.trans (le_max_left _ _)⟩
        · have hb : b < w := lt_of_not_ge fun hb => h ⟨hw, hb⟩
          exact Or.inr ⟨(min_le_left _ _).trans hb.le,
            h'.2.trans (le_max_right _ _)⟩
      rcases hstrip with hs | hs
      · simp only [intervalIndicator, Set.indicator, Set.mem_Icc,
          if_neg h, if_pos h', if_pos hs]
        split_ifs <;> norm_num
      · simp only [intervalIndicator, Set.indicator, Set.mem_Icc,
          if_neg h, if_pos h', if_pos hs]
        split_ifs <;> norm_num
    · have h0 := add_nonneg
        (intervalIndicator_bounds (min a (a + u)) (max a (a + u)) w).1
        (intervalIndicator_bounds (min b (b + u)) (max b (b + u)) w).1
      simpa [intervalIndicator, h, h'] using h0

theorem intervalMass_shift_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b u : ℝ) :
    |intervalMass ν a b - intervalMass ν (a + u) (b + u)| ≤
      intervalMass ν (min a (a + u)) (max a (a + u)) +
      intervalMass ν (min b (b + u)) (max b (b + u)) := by
  have h1 := intervalIndicator_integrable ν a b
  have h2 := intervalIndicator_integrable ν (a + u) (b + u)
  have hL := intervalIndicator_integrable ν (min a (a + u)) (max a (a + u))
  have hR := intervalIndicator_integrable ν (min b (b + u)) (max b (b + u))
  calc
    _ = |∫ w, intervalIndicator a b w - intervalIndicator (a + u) (b + u) w ∂ν| := by
      rw [integral_sub h1 h2]
      rfl
    _ ≤ ∫ w, |intervalIndicator a b w - intervalIndicator (a + u) (b + u) w| ∂ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ w, intervalIndicator (min a (a + u)) (max a (a + u)) w +
          intervalIndicator (min b (b + u)) (max b (b + u)) w ∂ν :=
      integral_mono (h1.sub h2).abs (hL.add hR) (intervalIndicator_shift_bound a b u)
    _ = _ := by rw [integral_add hL hR]; rfl

theorem translated_strip_length (a u : ℝ) :
    max a (a + u) - min a (a + u) = |u| := by
  rcases le_total 0 u with hu | hu
  · have ha : a ≤ a + u := by linarith
    rw [max_eq_right ha, min_eq_left ha, abs_of_nonneg hu]
    ring
  · have ha : a + u ≤ a := by linarith
    rw [max_eq_left ha, min_eq_right ha, abs_of_nonpos hu]
    ring

theorem intervalMass_shift_bound_of_concentration (ν : Measure ℝ)
    [IsFiniteMeasure ν] (c r : ℝ)
    (hcell : ∀ a b : ℝ, a ≤ b → intervalMass ν a b ≤ c * (b - a + r))
    (a b u : ℝ) :
    |intervalMass ν a b - intervalMass ν (a + u) (b + u)| ≤
      2 * c * (|u| + r) := by
  have hL := hcell (min a (a + u)) (max a (a + u)) min_le_max
  have hR := hcell (min b (b + u)) (max b (b + u)) min_le_max
  rw [translated_strip_length] at hL hR
  calc
    _ ≤ _ := intervalMass_shift_bound ν a b u
    _ ≤ c * (|u| + r) + c * (|u| + r) := add_le_add hL hR
    _ = _ := by ring

theorem measurable_shifted_intervalMass (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b : ℝ) : Measurable (fun u => intervalMass ν (a + u) (b + u)) := by
  have hs : MeasurableSet {z : ℝ × ℝ | a + z.1 ≤ z.2 ∧ z.2 ≤ b + z.1} :=
    (measurableSet_le (measurable_const.add measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_const.add measurable_fst))
  have hm : Measurable (fun z : ℝ × ℝ =>
      intervalIndicator (a + z.1) (b + z.1) z.2) := by
    exact Measurable.ite hs measurable_const measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_blurred_integrand (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : ℝ → ℝ} (hK : Integrable K) (a b : ℝ) :
    Integrable (fun u => K u * intervalMass ν (a + u) (b + u)) := by
  have hm := hK.aestronglyMeasurable.mul
    (measurable_shifted_intervalMass ν a b).aestronglyMeasurable
  apply (hK.abs.mul_const (∫ _ : ℝ, (1 : ℝ) ∂ν)).mono' hm
  filter_upwards [] with u
  change |K u * intervalMass ν (a+u) (b+u)| ≤ _
  rw [abs_mul, abs_of_nonneg (intervalMass_nonneg ν _ _)]
  exact mul_le_mul_of_nonneg_left (intervalMass_le_total ν _ _) (abs_nonneg _)

theorem interval_recovery_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : ℝ → ℝ} (hK : Integrable K) (hK0 : ∀ u, 0 ≤ K u)
    (hK1 : (∫ u, K u) = 1) (hKmoment : Integrable (fun u => K u * |u|))
    (c r a b : ℝ)
    (hcell : ∀ l h : ℝ, l ≤ h → intervalMass ν l h ≤ c * (h - l + r)) :
    |intervalMass ν a b - blurredMass ν K a b| ≤
      2 * c * ((∫ u, K u * |u|) + r) := by
  have hb := integrable_blurred_integrand ν hK a b
  have he : Integrable (fun u => K u *
      (intervalMass ν a b - intervalMass ν (a + u) (b + u))) := by
    convert! (hK.mul_const (intervalMass ν a b)).sub hb using 1
    funext u
    simp only [Pi.sub_apply]
    ring
  have hd : Integrable (fun u => K u * (2 * c * (|u| + r))) := by
    convert! (hKmoment.add (hK.mul_const r)).const_mul (2 * c) using 1
    funext u
    simp only [Pi.add_apply]
    ring
  have hid : intervalMass ν a b - blurredMass ν K a b =
      ∫ u, K u * (intervalMass ν a b - intervalMass ν (a + u) (b + u)) := by
    rw [show (fun u => K u *
      (intervalMass ν a b - intervalMass ν (a + u) (b + u))) =
      (fun u => K u * intervalMass ν a b -
        K u * intervalMass ν (a + u) (b + u)) by funext u; ring]
    rw [integral_sub (hK.mul_const _) hb, integral_mul_const, hK1, one_mul]
    rfl
  calc
    _ = |∫ u, K u *
        (intervalMass ν a b - intervalMass ν (a + u) (b + u))| := congrArg abs hid
    _ ≤ ∫ u, |K u *
        (intervalMass ν a b - intervalMass ν (a + u) (b + u))| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u, K u * (2 * c * (|u| + r)) := by
      apply integral_mono he.abs hd
      intro u
      change |K u * (intervalMass ν a b - intervalMass ν (a+u) (b+u))| ≤ _
      rw [abs_mul, abs_of_nonneg (hK0 u)]
      exact mul_le_mul_of_nonneg_left
        (intervalMass_shift_bound_of_concentration ν c r hcell a b u) (hK0 u)
    _ = _ := by
      rw [show (fun u => K u * (2 * c * (|u| + r))) =
          (fun u => 2 * c * (K u * |u| + K u * r)) by funext u; ring]
      rw [integral_const_mul, integral_add hKmoment (hK.mul_const r),
        integral_mul_const, hK1, one_mul]

theorem tendsto_of_uniform_smoothing {f : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {error : ℕ → ℝ} {L : ℝ}
    (herror : Tendsto error atTop (nhds 0))
    (hgap : ∀ j : ℕ, ∀ᶠ n in atTop, |f n - g j n| ≤ error j)
    (hsmoothed : ∀ j : ℕ, Tendsto (g j) atTop (nhds L)) :
    Tendsto f atTop (nhds L) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨j, hj⟩ := ((Metric.tendsto_nhds.mp herror)
    (epsilon / 2) (by linarith)).exists
  have herr : error j < epsilon / 2 := by
    have hj' : |error j| < epsilon / 2 := by simpa [Real.dist_eq] using hj
    exact (le_abs_self _).trans_lt hj'
  filter_upwards [hgap j, (Metric.tendsto_nhds.mp (hsmoothed j))
    (epsilon / 2) (by linarith)] with n hn hsm
  have hsm' : |g j n - L| < epsilon / 2 := by simpa [Real.dist_eq] using hsm
  rw [Real.dist_eq]
  calc
    |f n - L| = |(f n - g j n) + (g j n - L)| := by congr 1; ring
    _ ≤ |f n - g j n| + |g j n - L| := abs_add_le _ _
    _ < epsilon := by linarith

theorem recover_interval_limit (ν : ℕ → Measure ℝ)
    [∀ n, IsFiniteMeasure (ν n)] (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 0 < scale n) (K : ℕ → ℝ → ℝ)
    (hK : ∀ j, Integrable (K j)) (hK0 : ∀ j u, 0 ≤ K j u)
    (hK1 : ∀ j, (∫ u, K j u) = 1)
    (hKmoment : ∀ j, Integrable (fun u => K j u * |u|))
    (r : ℕ → ℝ) (C a b L : ℝ)
    (hsmall : Tendsto (fun j => (∫ u, K j u * |u|) + r j) atTop (nhds 0))
    (hcell : ∀ j, ∀ᶠ n in atTop, ∀ l h : ℝ, l ≤ h →
      intervalMass (ν n) l h ≤ (C / scale n) * (h - l + r j))
    (hsmoothed : ∀ j, Tendsto
      (fun n => scale n * blurredMass (ν n) (K j) a b) atTop (nhds L)) :
    Tendsto (fun n => scale n * intervalMass (ν n) a b) atTop (nhds L) := by
  apply tendsto_of_uniform_smoothing
    (error := fun j => 2 * C * ((∫ u, K j u * |u|) + r j))
  · simpa using hsmall.const_mul (2 * C)
  · intro j
    filter_upwards [hscale, hcell j] with n hs hc
    have hbound := interval_recovery_bound (ν n) (hK j) (hK0 j) (hK1 j)
      (hKmoment j) (C / scale n) (r j) a b hc
    calc
      _ = scale n * |intervalMass (ν n) a b - blurredMass (ν n) (K j) a b| := by
        rw [← mul_sub, abs_mul, abs_of_pos hs]
      _ ≤ scale n * (2 * (C / scale n) * ((∫ u, K j u * |u|) + r j)) :=
        mul_le_mul_of_nonneg_left hbound hs.le
      _ = _ := by field_simp [hs.ne']
  · exact hsmoothed

end FCAppendix.Affine.Uniform06.IntervalRecovery
