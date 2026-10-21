import FCAppendix.Affine.Multiple07.Source
import FCAppendix.Probability.FiniteAveraging

noncomputable section
namespace FCAppendix.Affine.Multiple07

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

def activeFraction (r : Partition) : ℝ := (rho - upperMass r / 2) / activeMass r

theorem activeFraction_values :
    activeFraction .row335 = 34 / 67 ∧ activeFraction .row665 = 67 / 133 := by
  norm_num [activeFraction, rho, upperMass, activeMass]

theorem activeFraction_mem (r : Partition) : activeFraction r ∈ Ioo (0 : ℝ) 1 := by
  cases r <;> norm_num [activeFraction, rho, upperMass, activeMass]

theorem activeLower_pos (r : Partition) : 0 < activeLower r := by
  norm_num [activeLower]

theorem activeUpper_pos (r : Partition) : 0 < activeUpper r := by
  cases r <;> norm_num [activeUpper]

def reciprocalMean (r : Partition) : ℝ := ∫ v, v⁻¹ ∂activeValueLaw r

theorem integrable_active_reciprocal (r : Partition) :
    Integrable (fun v : ℝ => v⁻¹) (activeValueLaw r) := by
  apply Integrable.of_bound measurable_id.inv.aestronglyMeasurable (1 / activeLower r)
  filter_upwards [activeValueLaw_support r] with v hv
  have hv0 := (activeLower_pos r).trans_le hv.1
  change ‖v⁻¹‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hv0.le)]
  simpa only [one_div] using one_div_le_one_div_of_le (activeLower_pos r) hv.1

theorem reciprocalMean_bounds (r : Partition) :
    1 / activeUpper r ≤ reciprocalMean r ∧
      reciprocalMean r ≤ 1 / activeLower r := by
  constructor
  · have h := integral_mono_ae (integrable_const (1 / activeUpper r))
      (integrable_active_reciprocal r) (by
        filter_upwards [activeValueLaw_support r] with v hv
        have hv0 := (activeLower_pos r).trans_le hv.1
        simpa only [one_div] using one_div_le_one_div_of_le hv0 hv.2)
    simpa only [integral_const, probReal_univ, one_smul, reciprocalMean] using h
  · have h := integral_mono_ae (integrable_active_reciprocal r)
      (integrable_const (1 / activeLower r)) (by
        filter_upwards [activeValueLaw_support r] with v hv
        simpa only [one_div] using one_div_le_one_div_of_le (activeLower_pos r) hv.1)
    simpa only [integral_const, probReal_univ, one_smul, reciprocalMean] using h

theorem reciprocalMean_pos (r : Partition) : 0 < reciprocalMean r :=
  (one_div_pos.mpr (activeUpper_pos r)).trans_le (reciprocalMean_bounds r).1

def multiplier (r : Partition) : ℝ := (1 - activeFraction r) / reciprocalMean r

theorem multiplier_bounds (r : Partition) :
    0 < multiplier r ∧ multiplier r < activeLower r := by
  have hr := activeFraction_mem r
  have h0 : 0 < multiplier r := div_pos (sub_pos.mpr hr.2) (reciprocalMean_pos r)
  have h1 : multiplier r ≤ (1 - activeFraction r) * activeUpper r := by
    calc
      _ ≤ (1 - activeFraction r) / (1 / activeUpper r) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hr.2.le)
          (one_div_pos.mpr (activeUpper_pos r)) (reciprocalMean_bounds r).1
      _ = _ := by field_simp
  refine ⟨h0, h1.trans_lt ?_⟩
  cases r <;>
    norm_num [activeFraction, rho, upperMass, activeMass, activeUpper, activeLower]

def exposure (r : Partition) (v : ℝ) : ℝ := 1 - multiplier r / v

theorem measurable_exposure (r : Partition) : Measurable (exposure r) :=
  measurable_const.sub (measurable_const.div measurable_id)

theorem exposure_bounds_of_lower (r : Partition) {v : ℝ}
    (hv : activeLower r ≤ v) : exposure r v ∈ Ioo (0 : ℝ) 1 := by
  have hv0 := (activeLower_pos r).trans_le hv
  have hm := multiplier_bounds r
  have hlo : 0 < multiplier r / v := div_pos hm.1 hv0
  have hhi : multiplier r / v < 1 := (div_lt_one hv0).mpr (hm.2.trans_le hv)
  constructor <;> dsimp [exposure] <;> linarith

theorem positiveBand_lower (r : Partition) (b : Band) (hb : b ≠ .low) :
    activeLower r ≤ bandLower b := by
  cases b <;> norm_num [activeLower, bandLower] at *

theorem integrable_band_exposure_pow (r : Partition) (b : Band)
    (hb : b ≠ .low) (k : ℕ) :
    Integrable (fun v => (exposure r v) ^ k) (bandLaw b) := by
  apply Integrable.of_bound ((measurable_exposure r).pow_const k).aestronglyMeasurable 1
  filter_upwards [bandLaw_support b] with v hv
  have hp := exposure_bounds_of_lower r ((positiveBand_lower r b hb).trans hv.1)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hp.1.le _)]
  exact pow_le_one₀ hp.1.le hp.2.le

theorem active_exposure_integral (r : Partition) :
    (∫ v, exposure r v ∂activeValueLaw r) = activeFraction r := by
  have he : exposure r = (fun v : ℝ => 1 - multiplier r * v⁻¹) := by
    funext v
    simp only [exposure, div_eq_mul_inv]
  rw [he, integral_sub (integrable_const _)
    ((integrable_active_reciprocal r).const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  change 1 - multiplier r * reciprocalMean r = _
  rw [multiplier, div_mul_cancel₀ _ (reciprocalMean_pos r).ne']
  ring

def bandReciprocal (b : Band) : ℝ :=
  Real.log (bandUpper b / bandLower b) / (bandUpper b - bandLower b)

theorem band_reciprocal_integral (b : Band) (hb : b ≠ .low) :
    (∫ v : ℝ, v⁻¹ ∂bandLaw b) = bandReciprocal b := by
  have hl : 0 < bandLower b := (activeLower_pos .row335).trans_le
    (positiveBand_lower .row335 b hb)
  have hlu : bandLower b ≤ bandUpper b := (sub_pos.mp (band_width_pos b)).le
  have hu : 0 < bandUpper b := hl.trans_le hlu
  rw [band_integral]
  have hi := Uniform07.integral_invpow 1 hl hlu
  simp only [pow_one, Uniform07.invMoment] at hi
  rw [hi, bandReciprocal, Real.log_div hu.ne' hl.ne']

theorem reciprocalMean_logarithmic (r : Partition) :
    reciprocalMean r =
      match r with
      | .row335 => bandReciprocal .first
      | .row665 => (67 / 133 : ℝ) * bandReciprocal .first +
          (66 / 133 : ℝ) * bandReciprocal .second := by
  have hi (b : Band) (hb : b ≠ .low) :
      Integrable (fun v : ℝ => v⁻¹) (bandLaw b) := by
    apply Integrable.of_bound measurable_id.inv.aestronglyMeasurable (2000 / 1899)
    filter_upwards [bandLaw_support b] with v hv
    have hlo : (1899 / 2000 : ℝ) ≤ v := (positiveBand_lower .row335 b hb).trans hv.1
    have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hlo
    change ‖v⁻¹‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hv0.le)]
    convert! one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1899 / 2000) hlo using 1 <;> norm_num
  cases r
  · exact band_reciprocal_integral .first (by decide)
  · rw [reciprocalMean, activeValueLaw, integral_add_measure
      ((hi .first (by decide)).smul_measure ENNReal.ofReal_ne_top)
      ((hi .second (by decide)).smul_measure ENNReal.ofReal_ne_top)]
    norm_num only [integral_smul_measure, ENNReal.toReal_ofReal, smul_eq_mul]
    rw [band_reciprocal_integral .first (by decide),
      band_reciprocal_integral .second (by decide)]

def bandDuplicateMoment (lam : ℝ) (b : Band) : ℝ :=
  1 - 2 * lam * bandReciprocal b +
    lam ^ 2 / (bandLower b * bandUpper b)

theorem band_duplicate_integral (r : Partition) (b : Band) (hb : b ≠ .low) :
    (∫ v, (exposure r v) ^ 2 ∂bandLaw b) =
      bandDuplicateMoment (multiplier r) b := by
  have hl : 0 < bandLower b := (activeLower_pos r).trans_le (positiveBand_lower r b hb)
  have hlu : bandLower b ≤ bandUpper b := (sub_pos.mp (band_width_pos b)).le
  have hu : 0 < bandUpper b := hl.trans_le hlu
  rw [band_integral]
  simp only [exposure]
  rw [Uniform07.integral_moment 1 (multiplier r) 2 hl hlu]
  simp only [bandDuplicateMoment, bandReciprocal, Real.log_div hu.ne' hl.ne']
  norm_num [Uniform07.moment, Finset.sum_range_succ, Uniform07.invMoment]
  field_simp [hl.ne', hu.ne', (band_width_pos b).ne']
  ring

def limitingDuplicates (r : Partition) : ℝ :=
  match r with
  | .row335 => (67 / 200 : ℝ) * bandDuplicateMoment (multiplier r) .first
  | .row665 => (67 / 200 : ℝ) * bandDuplicateMoment (multiplier r) .first +
      (33 / 100 : ℝ) * bandDuplicateMoment (multiplier r) .second

def limitingCoverage (r : Partition) : ℝ := (99 / 100 : ℝ) - limitingDuplicates r
def limitingMultiplicity (r : Partition) : ℝ := (99 / 100 : ℝ) / limitingCoverage r

theorem active_duplicate_integral (r : Partition) :
    activeMass r * (∫ v, (exposure r v) ^ 2 ∂activeValueLaw r) =
      limitingDuplicates r := by
  cases r
  · rw [activeValueLaw, band_duplicate_integral _ .first (by decide)]
    rfl
  · rw [activeValueLaw, integral_add_measure
      ((integrable_band_exposure_pow _ .first (by decide) 2).smul_measure
        ENNReal.ofReal_ne_top)
      ((integrable_band_exposure_pow _ .second (by decide) 2).smul_measure
        ENNReal.ofReal_ne_top)]
    norm_num only [integral_smul_measure, ENNReal.toReal_ofReal, smul_eq_mul]
    rw [band_duplicate_integral _ .first (by decide),
      band_duplicate_integral _ .second (by decide)]
    norm_num [activeMass, limitingDuplicates]
    ring

def activeSet (r : Partition) : Set ℝ := Icc (activeLower r) (activeUpper r)
def upperSet (r : Partition) : Set ℝ := Icc (upperLower r) (2301 / 2000)

def limitingLaw (r : Partition) (v : ℝ) : CountLaw 2 := by
  classical
  exact if hv : v ∈ activeSet r then
    IndependentCounts.binomial 2 (exposure r v)
      (exposure_bounds_of_lower r hv.1).1.le
      (exposure_bounds_of_lower r hv.1).2.le
  else if v ∈ upperSet r then FiniteLaw.dirac 1 else FiniteLaw.dirac 0

theorem limitingLaw_active (r : Partition) {v : ℝ} (hv : v ∈ activeSet r) :
    limitingLaw r v = IndependentCounts.binomial 2 (exposure r v)
      (exposure_bounds_of_lower r hv.1).1.le
      (exposure_bounds_of_lower r hv.1).2.le := by
  simp only [limitingLaw, dif_pos hv]

theorem limitingLaw_upper (r : Partition) {v : ℝ} (hv : v ∈ upperSet r) :
    limitingLaw r v = FiniteLaw.dirac 1 := by
  have hsep : activeUpper r < upperLower r := by cases r <;> norm_num [activeUpper, upperLower]
  have hn : v ∉ activeSet r := by
    intro ha
    exact (not_lt_of_ge (hv.1.trans ha.2)) hsep
  simp only [limitingLaw, dif_neg hn, if_pos hv]

theorem limitingLaw_low {r : Partition} {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (1 / 100)) : limitingLaw r v = FiniteLaw.dirac 0 := by
  have hna : v ∉ activeSet r := by
    intro ha
    have h := ha.1
    dsimp [activeSet, activeLower] at h
    linarith [hv.2]
  have hnu : v ∉ upperSet r := by
    intro hu
    have h := hu.1
    cases r <;> norm_num [upperSet, upperLower] at h <;> linarith [hv.2]
  simp only [limitingLaw, dif_neg hna, if_neg hnu]

private theorem pair_expect (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Fin 3 → ℝ) :
    (IndependentCounts.binomial 2 p hp0 hp1).expect f =
      (1 - p) ^ 2 * f 0 + 2 * p * (1 - p) * f 1 + p ^ 2 * f 2 := by
  rw [IndependentCounts.expect_binomial_succ]
  simp only [IndependentCounts.expect_binomial_succ]
  norm_num [IndependentCounts.binomial, IndependentCounts.independentCount,
    FiniteLaw.expect_dirac, IndependentCounts.addCount]
  ring_nf
  rfl

theorem measurable_limitingLaw_expect (r : Partition) (f : Fin 3 → ℝ) :
    Measurable (fun v => (limitingLaw r v).expect f) := by
  classical
  have he : (fun v => (limitingLaw r v).expect f) =
      fun v => if v ∈ activeSet r then
        (1 - exposure r v) ^ 2 * f 0 +
          2 * exposure r v * (1 - exposure r v) * f 1 +
          (exposure r v) ^ 2 * f 2
        else if v ∈ upperSet r then f 1 else f 0 := by
    funext v
    unfold limitingLaw
    split_ifs <;> simp only [pair_expect, FiniteLaw.expect_dirac]
  rw [he]
  apply Measurable.ite measurableSet_Icc
  · have h := measurable_exposure r
    fun_prop
  · exact Measurable.ite measurableSet_Icc measurable_const measurable_const

theorem integrable_limitingLaw_expect (r : Partition) (F : Measure ℝ)
    [IsFiniteMeasure F] (f : Fin 3 → ℝ) :
    Integrable (fun v => (limitingLaw r v).expect f) F :=
  Integrable.of_bound (measurable_limitingLaw_expect r f).aestronglyMeasurable
    (∑ j, ‖f j‖) (Eventually.of_forall fun v =>
      (limitingLaw r v).norm_expect_le_sum_norm f)

private theorem source_integral_classes (r : Partition) (f : Fin 3 → ℝ) :
    (∫ v, (limitingLaw r v).expect f ∂sourceValueLaw) =
      (3 / 200 : ℝ) * (∫ v, (limitingLaw r v).expect f ∂bandLaw .low) +
      activeMass r * (∫ v, (limitingLaw r v).expect f ∂activeValueLaw r) +
      upperMass r * (∫ v, (limitingLaw r v).expect f ∂upperValueLaw r) := by
  have h0 := (integrable_limitingLaw_expect r (bandLaw .low) f).smul_measure
    (c := ENNReal.ofReal (3 / 200 : ℝ)) ENNReal.ofReal_ne_top
  have h1 := (integrable_limitingLaw_expect r (activeValueLaw r) f).smul_measure
    (c := ENNReal.ofReal (activeMass r)) ENNReal.ofReal_ne_top
  have h2 := (integrable_limitingLaw_expect r (upperValueLaw r) f).smul_measure
    (c := ENNReal.ofReal (upperMass r)) ENNReal.ofReal_ne_top
  rw [sourceValueLaw_decomposition r,
    integral_add_measure (h0.add_measure h1) h2, integral_add_measure h0 h1]
  cases r <;> norm_num [integral_smul_measure, activeMass, upperMass]

private theorem integral_low_profile (r : Partition) (f : Fin 3 → ℝ) :
    (∫ v, (limitingLaw r v).expect f ∂bandLaw .low) = f 0 := by
  calc
    _ = ∫ _v, f 0 ∂bandLaw .low := by
      apply integral_congr_ae
      filter_upwards [bandLaw_support .low] with v hv
      rw [limitingLaw_low (by simpa [bandLower, bandUpper] using hv)]
      exact FiniteLaw.expect_dirac _ _
    _ = _ := by simp

private theorem integral_upper_profile (r : Partition) (f : Fin 3 → ℝ) :
    (∫ v, (limitingLaw r v).expect f ∂upperValueLaw r) = f 1 := by
  calc
    _ = ∫ _v, f 1 ∂upperValueLaw r := by
      apply integral_congr_ae
      filter_upwards [upperValueLaw_support r] with v hv
      rw [limitingLaw_upper r hv]
      exact FiniteLaw.expect_dirac _ _
    _ = _ := by simp

theorem source_profile_integrals (r : Partition) :
    (∫ v, (limitingLaw r v).load ∂sourceValueLaw) = 99 / 100 ∧
      (∫ v, (limitingLaw r v).duplicates ∂sourceValueLaw) = limitingDuplicates r ∧
      (∫ v, (limitingLaw r v).success ∂sourceValueLaw) = limitingCoverage r := by
  have hl : (∫ v, (limitingLaw r v).load ∂sourceValueLaw) = 99 / 100 := by
    change (∫ v, (limitingLaw r v).expect (fun j => (j.val : ℝ)) ∂sourceValueLaw) = _
    rw [source_integral_classes, integral_low_profile, integral_upper_profile]
    norm_num only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, mul_zero, zero_add, mul_one]
    have ha : (∫ v, (limitingLaw r v).expect (fun j => (j.val : ℝ)) ∂activeValueLaw r) =
        2 * activeFraction r := by
      calc
        _ = ∫ v, 2 * exposure r v ∂activeValueLaw r := by
          apply integral_congr_ae
          filter_upwards [activeValueLaw_support r] with v hv
          change (limitingLaw r v).load = _
          rw [limitingLaw_active r hv, IndependentCounts.binomial_load]
          norm_num
        _ = _ := by rw [integral_const_mul, active_exposure_integral]
    rw [ha]
    cases r <;> norm_num [activeMass, upperMass, activeFraction, rho]
  have hd : (∫ v, (limitingLaw r v).duplicates ∂sourceValueLaw) = limitingDuplicates r := by
    simp_rw [CountLaw.duplicates_eq_expect]
    rw [source_integral_classes, integral_low_profile, integral_upper_profile]
    norm_num [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
      successIndicator, sub_self, mul_zero, zero_add, add_zero]
    rw [← active_duplicate_integral r]
    congr 1
    apply integral_congr_ae
    filter_upwards [activeValueLaw_support r] with v hv
    have hmass : (FiniteLaw.expect (limitingLaw r v) fun j =>
        (j.val:ℝ) - if j=0 then 0 else 1) = (limitingLaw r v).duplicates := by
      rw [CountLaw.duplicates_eq_expect]
      apply FiniteLaw.expect_congr
      intro j
      simp only [successIndicator,Fin.ext_iff,Fin.val_zero]
    rw [hmass]
    rw [limitingLaw_active r hv,
      CountLaw.duplicates, IndependentCounts.binomial_load, IndependentCounts.binomial_success]
    norm_num
    ring
  refine ⟨hl, hd, ?_⟩
  have hdiff : (∫ v, (limitingLaw r v).duplicates ∂sourceValueLaw) =
      (∫ v, (limitingLaw r v).load ∂sourceValueLaw) -
        (∫ v, (limitingLaw r v).success ∂sourceValueLaw) := by
    exact integral_sub (integrable_limitingLaw_expect r sourceValueLaw _)
      (integrable_limitingLaw_expect r sourceValueLaw _)
  rw [hl, hd] at hdiff
  dsimp [limitingCoverage]
  linarith

theorem limitingCoverage_pos (r : Partition) : 0 < limitingCoverage r := by
  have h := integral_mono_ae (integrable_limitingLaw_expect r sourceValueLaw
      (fun j => (j.val : ℝ)))
    ((integrable_limitingLaw_expect r sourceValueLaw
      (fun j => successIndicator j.val)).const_mul 2)
    (Eventually.of_forall fun v => (limitingLaw r v).load_le_mul_success)
  rw [integral_const_mul] at h
  change (∫ v, (limitingLaw r v).load ∂sourceValueLaw) ≤
    2 * (∫ v, (limitingLaw r v).success ∂sourceValueLaw) at h
  rw [(source_profile_integrals r).1,
    (source_profile_integrals r).2.2] at h
  norm_num at h
  linarith

end FCAppendix.Affine.Multiple07
