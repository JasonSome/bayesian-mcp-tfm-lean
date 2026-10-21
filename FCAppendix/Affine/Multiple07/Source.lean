import FCAppendix.Affine.Uniform07.ExactIntegral
import FCAppendix.Game.PosteriorBeliefs
import FCAppendix.Finite.ReceiptBounds
import FCAppendix.Probability.IndependentCounts
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace FCAppendix.Affine.Multiple07

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

inductive Band where
  | low | first | second | third
  deriving DecidableEq, Fintype

inductive Partition where
  | row335 | row665
  deriving DecidableEq, Fintype

def bandLower : Band → ℝ
  | .low => 0
  | .first => 1899 / 2000
  | .second => 2099 / 2000
  | .third => 2299 / 2000

def bandUpper : Band → ℝ
  | .low => 1 / 100
  | .first => 1901 / 2000
  | .second => 2101 / 2000
  | .third => 2301 / 2000

def bandWeight : Band → ℝ
  | .low => 3 / 200
  | .first => 67 / 200
  | .second => 33 / 100
  | .third => 8 / 25

def bandLaw (b : Band) : Measure ℝ :=
  ENNReal.ofReal (1 / (bandUpper b - bandLower b)) •
    volume.restrict (Icc (bandLower b) (bandUpper b))

theorem band_width_pos (b : Band) : 0 < bandUpper b - bandLower b := by
  cases b <;> norm_num [bandUpper, bandLower]

instance bandLaw_probability (b : Band) : IsProbabilityMeasure (bandLaw b) := by
  constructor
  cases b <;> norm_num [bandLaw, bandUpper, bandLower,
    Measure.smul_apply, Measure.restrict_apply, Real.volume_Icc,ENNReal.ofReal_div_of_pos]
  all_goals exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

instance bandLaw_atomless (b : Band) : NullSingletonClass (bandLaw b) := by
  constructor
  intro v
  simp only [bandLaw,Measure.smul_apply,measure_singleton,smul_zero]

theorem bandLaw_support (b : Band) :
    ∀ᵐ v ∂bandLaw b, v ∈ Icc (bandLower b) (bandUpper b) :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

def sourceValueLaw : Measure ℝ :=
  ENNReal.ofReal (3 / 200 : ℝ) • bandLaw .low +
    ENNReal.ofReal (67 / 200 : ℝ) • bandLaw .first +
    ENNReal.ofReal (33 / 100 : ℝ) • bandLaw .second +
    ENNReal.ofReal (8 / 25 : ℝ) • bandLaw .third

instance sourceValueLaw_probability : IsProbabilityMeasure sourceValueLaw := by
  constructor
  simp only [sourceValueLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 3/200) (by norm_num : (0:ℝ) ≤ 67/200),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num : (0:ℝ) ≤ 33/100),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num : (0:ℝ) ≤ 8/25)]
  norm_num

instance sourceValueLaw_atomless : NullSingletonClass sourceValueLaw := by
  constructor
  intro v
  simp only [sourceValueLaw,Measure.add_apply,Measure.smul_apply,measure_singleton,smul_zero,add_zero]

def activeMass : Partition → ℝ
  | .row335 => 67 / 200
  | .row665 => 133 / 200

def upperMass : Partition → ℝ
  | .row335 => 13 / 20
  | .row665 => 8 / 25

def upperFloor : Partition → ℝ
  | .row335 => 71 / 100
  | .row665 => 381 / 500

def activeLower (_r : Partition) : ℝ := 1899 / 2000

def activeUpper : Partition → ℝ
  | .row335 => 1901 / 2000
  | .row665 => 2101 / 2000

def upperLower : Partition → ℝ
  | .row335 => 2099 / 2000
  | .row665 => 2299 / 2000

def activeValueLaw : Partition → Measure ℝ
  | .row335 => bandLaw .first
  | .row665 =>
      ENNReal.ofReal (67 / 133 : ℝ) • bandLaw .first +
        ENNReal.ofReal (66 / 133 : ℝ) • bandLaw .second

def upperValueLaw : Partition → Measure ℝ
  | .row335 =>
      ENNReal.ofReal (33 / 65 : ℝ) • bandLaw .second +
        ENNReal.ofReal (32 / 65 : ℝ) • bandLaw .third
  | .row665 => bandLaw .third

instance activeValueLaw_probability (r : Partition) :
    IsProbabilityMeasure (activeValueLaw r) := by
  cases r
  · exact bandLaw_probability _
  · constructor
    simp only [activeValueLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 67/133) (by norm_num : (0:ℝ) ≤ 66/133)]
    norm_num

instance upperValueLaw_probability (r : Partition) :
    IsProbabilityMeasure (upperValueLaw r) := by
  cases r
  · constructor
    simp only [upperValueLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 33/65) (by norm_num : (0:ℝ) ≤ 32/65)]
    norm_num
  · exact bandLaw_probability _

instance activeValueLaw_atomless (r : Partition) :
    NullSingletonClass (activeValueLaw r) := by
  constructor
  intro v
  cases r <;> simp [activeValueLaw,Measure.add_apply,Measure.smul_apply,measure_singleton]

instance upperValueLaw_atomless (r : Partition) :
    NullSingletonClass (upperValueLaw r) := by
  constructor
  intro v
  cases r <;> simp [upperValueLaw,Measure.add_apply,Measure.smul_apply,measure_singleton]

theorem sourceValueLaw_decomposition (r : Partition) :
    sourceValueLaw =
      ENNReal.ofReal (3 / 200 : ℝ) • bandLaw .low +
        ENNReal.ofReal (activeMass r) • activeValueLaw r +
        ENNReal.ofReal (upperMass r) • upperValueLaw r := by
  cases r
  · simp only [sourceValueLaw, activeMass, upperMass, activeValueLaw, upperValueLaw,
      smul_add, smul_smul]
    simp_rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 13/20)]
    norm_num
    abel
  · simp only [sourceValueLaw, activeMass, upperMass, activeValueLaw, upperValueLaw,
      smul_add, smul_smul]
    simp_rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 133/200)]
    norm_num
    abel

theorem activeValueLaw_support (r : Partition) :
    ∀ᵐ v ∂activeValueLaw r, v ∈ Icc (activeLower r) (activeUpper r) := by
  cases r
  · simpa [activeValueLaw, activeLower, activeUpper, bandLower, bandUpper]
      using bandLaw_support Band.first
  · rw [activeValueLaw, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      filter_upwards [bandLaw_support Band.first] with v hv
      norm_num [bandLower, bandUpper, activeLower, activeUpper] at hv ⊢
      exact ⟨hv.1, by linarith [hv.2]⟩
    · apply Measure.ae_smul_measure
      filter_upwards [bandLaw_support Band.second] with v hv
      norm_num [bandLower, bandUpper, activeLower, activeUpper] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩

theorem upperValueLaw_support (r : Partition) :
    ∀ᵐ v ∂upperValueLaw r, v ∈ Icc (upperLower r) (2301 / 2000) := by
  cases r
  · rw [upperValueLaw, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      filter_upwards [bandLaw_support Band.second] with v hv
      norm_num [bandLower, bandUpper, upperLower] at hv ⊢
      exact ⟨hv.1, by linarith [hv.2]⟩
    · apply Measure.ae_smul_measure
      filter_upwards [bandLaw_support Band.third] with v hv
      norm_num [bandLower, bandUpper, upperLower] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
  · simpa [upperValueLaw, upperLower, bandLower, bandUpper]
      using bandLaw_support Band.third

theorem source_integral (f : ℝ → ℝ)
    (hi : ∀ b, Integrable f (bandLaw b)) :
    (∫ v, f v ∂sourceValueLaw) =
      (3 / 200 : ℝ) * (∫ v, f v ∂bandLaw .low) +
      (67 / 200 : ℝ) * (∫ v, f v ∂bandLaw .first) +
      (33 / 100 : ℝ) * (∫ v, f v ∂bandLaw .second) +
      (8 / 25 : ℝ) * (∫ v, f v ∂bandLaw .third) := by
  have h0 := (hi .low).smul_measure (c := ENNReal.ofReal (3 / 200 : ℝ))
    ENNReal.ofReal_ne_top
  have h1 := (hi .first).smul_measure (c := ENNReal.ofReal (67 / 200 : ℝ))
    ENNReal.ofReal_ne_top
  have h2 := (hi .second).smul_measure (c := ENNReal.ofReal (33 / 100 : ℝ))
    ENNReal.ofReal_ne_top
  have h3 := (hi .third).smul_measure (c := ENNReal.ofReal (8 / 25 : ℝ))
    ENNReal.ofReal_ne_top
  rw [sourceValueLaw, integral_add_measure ((h0.add_measure h1).add_measure h2) h3,
    integral_add_measure (h0.add_measure h1) h2, integral_add_measure h0 h1]
  norm_num [integral_smul_measure]

theorem band_integral (b : Band) (f : ℝ → ℝ) :
    (∫ v, f v ∂bandLaw b) =
      (∫ v in bandLower b..bandUpper b, f v) / (bandUpper b - bandLower b) := by
  rw [bandLaw, integral_smul_measure,
    ENNReal.toReal_ofReal (one_div_nonneg.mpr (band_width_pos b).le),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (sub_nonneg.mp (band_width_pos b).le)]
  simp only [smul_eq_mul]
  ring

private theorem band_cdf_zero (b : Band) {t : ℝ} (ht : t < bandLower b) :
    bandLaw b (Iic t) = 0 := by
  have he : Iic t ∩ Icc (bandLower b) (bandUpper b) = ∅ := by
    ext v
    simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
    rintro ⟨hv, hlo, _⟩
    linarith
  simp [bandLaw, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, he]

theorem source_cdf_on_low_band {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 100)) :
    sourceValueLaw.real (Iic t) = (3 / 2 : ℝ) * t := by
  have he : Iic t ∩ Icc (0 : ℝ) (1 / 100) = Icc 0 t := by
    ext v
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hvt, hv0, _⟩
      exact ⟨hv0, hvt⟩
    · rintro ⟨hv0, hvt⟩
      exact ⟨hvt, hv0, hvt.trans ht.2⟩
  have hz1 := band_cdf_zero Band.first (t := t) (by
    norm_num [bandLower]; linarith [ht.2])
  have hz2 := band_cdf_zero Band.second (t := t) (by
    norm_num [bandLower]; linarith [ht.2])
  have hz3 := band_cdf_zero Band.third (t := t) (by
    norm_num [bandLower]; linarith [ht.2])
  have hlo : bandLaw .low (Iic t) = ENNReal.ofReal (100 * t) := by
    simp only [bandLaw, bandLower, bandUpper]
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, he,
      Real.volume_Icc]
    norm_num only [sub_zero, one_div_div, div_one]
    rw [smul_eq_mul, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
  simp only [Measure.real, sourceValueLaw, Measure.add_apply, Measure.smul_apply,
    hz1, hz2, hz3, hlo, smul_eq_mul, mul_zero, add_zero,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 3 / 200 by norm_num),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0:ℝ) ≤ 100) ht.1)]
  ring

theorem efficient_cutoff_and_density :
    sourceValueLaw.real (Iic (1 / 150 : ℝ)) = 1 / 100 ∧
      sourceValueLaw.real (Ioi (1 / 150 : ℝ)) = 99 / 100 ∧
      HasDerivAt (fun t => sourceValueLaw.real (Iic t)) (3 / 2) (1 / 150) := by
  have hc : sourceValueLaw.real (Iic (1 / 150 : ℝ)) = 1 / 100 := by
    rw [source_cdf_on_low_band (by norm_num)]
    norm_num
  refine ⟨hc, ?_, ?_⟩
  · have h := probReal_compl_eq_one_sub (μ := sourceValueLaw)
      (s := Iic (1 / 150 : ℝ)) measurableSet_Iic
    rw [compl_Iic, hc] at h
    norm_num at h ⊢
    exact h
  · have hd : HasDerivAt (fun t : ℝ => (3 / 2) * t) (3 / 2) (1 / 150) := by
      simpa using (hasDerivAt_id (1 / 150 : ℝ)).const_mul (3 / 2 : ℝ)
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 150)
      (by norm_num : (1 / 150 : ℝ) < 1 / 100)] with t ht
    exact source_cdf_on_low_band ⟨ht.1.le, ht.2.le⟩

def rho : ℝ := 99 / 200
def eta : ℝ := 1 / 10
def xi : ℝ := 9 / 20
def lowCeiling : ℝ := 1 / 100

def marketCapacity (m : ℕ) : ℕ := (99 * m) / 200

theorem marketCapacity_floor (m : ℕ) :
    marketCapacity m = Nat.floor (rho * (m : ℝ)) := by
  have hr : (99 * m) % 200 < 200 := Nat.mod_lt _ (by norm_num)
  have he : (99 * m) % 200 + 200 * ((99 * m) / 200) = 99 * m :=
    Nat.mod_add_div _ _
  have hrR : (((99 * m) % 200 : ℕ) : ℝ) < 200 := by exact_mod_cast hr
  have heR : (((99 * m) % 200 : ℕ) : ℝ) +
      200 * (((99 * m) / 200 : ℕ) : ℝ) = 99 * (m : ℝ) := by
    exact_mod_cast he
  have hn : (0 : ℝ) ≤ (((99 * m) % 200 : ℕ) : ℝ) := Nat.cast_nonneg _
  symm
  apply (Nat.floor_eq_iff
    (mul_nonneg (by norm_num [rho] : (0 : ℝ) ≤ rho) (Nat.cast_nonneg m))).2
  dsimp [marketCapacity, rho]
  constructor <;> nlinarith

theorem marketCapacity_density :
    Tendsto (fun m : ℕ => (marketCapacity m : ℝ) / (m : ℝ))
      atTop (𝓝 rho) := by
  simpa only [Function.comp_def, ← marketCapacity_floor] using
    (tendsto_nat_floor_mul_div_atTop (show 0 ≤ rho by norm_num [rho])).comp
      tendsto_natCast_atTop_atTop

theorem marketCapacity_tendsto : Tendsto marketCapacity atTop atTop := by
  simpa only [Function.comp_def, ← marketCapacity_floor] using
    tendsto_nat_floor_mul_atTop rho (show 0 < rho by norm_num [rho])

def affineSchedule : Schedule 2 := Schedule.affine 2 eta (by norm_num [eta])
  (by norm_num [eta])

theorem primitive_coefficients :
    eta = 1 / 10 ∧ xi = (1 - eta) / 2 ∧ rho = 99 / 200 ∧
      ∀ r, (3 / 200 : ℝ) + activeMass r + upperMass r = 1 := by
  refine ⟨rfl, by norm_num [xi, eta], rfl, ?_⟩
  intro r
  cases r <;> norm_num [activeMass, upperMass]

end FCAppendix.Affine.Multiple07
