import FCAppendix.Affine.Tail04.OriginalValueSplits
import FCAppendix.Affine.LowBody.NoisyAtomlessLimit

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Filter

namespace OriginalValues

def clipToBand (l u : ℝ) (hlu : l ≤ u) (v : ℝ) : Icc l u :=
  ⟨max l (min u v), le_max_left _ _, max_le hlu (min_le_left _ _)⟩

theorem measurable_clipToBand (l u : ℝ) (hlu : l ≤ u) :
    Measurable (clipToBand l u hlu) := by
  apply Measurable.subtype_mk
  exact measurable_const.max (measurable_const.min measurable_id)

theorem clipToBand_eq (l u : ℝ) (hlu : l ≤ u) {v : ℝ} (hv : v ∈ Icc l u) :
    (clipToBand l u hlu v : ℝ) = v := by
  simp [clipToBand, min_eq_right hv.2, max_eq_right hv.1]

theorem conditional_mem (μ : Measure ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
    ∀ᵐ v ∂cond μ E, v ∈ E := by
  rw [ae_iff]
  change cond μ E Eᶜ = 0
  rw [cond_apply hE]
  simp

def compactConditional (μ : Measure ℝ) (l u : ℝ) (hlu : l ≤ u) :
    Measure (Icc l u) := (cond μ (Icc l u)).map (clipToBand l u hlu)

theorem compactConditional_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (l u : ℝ) (hlu : l ≤ u) (hm : μ (Icc l u) ≠ 0) :
    IsProbabilityMeasure (compactConditional μ l u hlu) := by
  letI : IsProbabilityMeasure (cond μ (Icc l u)) := cond_isProbabilityMeasure hm
  exact Measure.isProbabilityMeasure_map (measurable_clipToBand l u hlu).aemeasurable

theorem compactConditional_real (μ : Measure ℝ) (l u : ℝ) (hlu : l ≤ u) :
    (compactConditional μ l u hlu).map Subtype.val = cond μ (Icc l u) := by
  rw [compactConditional, Measure.map_map measurable_subtype_coe
    (measurable_clipToBand l u hlu)]
  calc
    _ = (cond μ (Icc l u)).map id := by
      apply Measure.map_congr
      filter_upwards [conditional_mem μ (Icc l u) measurableSet_Icc] with v hv
      exact clipToBand_eq l u hlu hv
    _ = _ := Measure.map_id

theorem compactConditional_positive (μ : Measure ℝ) [NullSingletonClass μ]
    (u : ℝ) (hu : 0 ≤ u) :
    ∀ᵐ (v : Icc (0:ℝ) u) ∂(compactConditional μ 0 u hu), 0 < v.1 := by
  have hzero : cond μ (Icc 0 u) ({0} : Set ℝ) = 0 := by
    rw [cond_apply measurableSet_Icc]
    have hsubset : Icc (0:ℝ) u ∩ {0} ⊆ {0} := inter_subset_right
    have hz : μ (Icc (0:ℝ) u ∩ {0}) = 0 :=
      measure_mono_null hsubset (measure_singleton 0)
    rw [hz, mul_zero]
  have hn : ∀ᵐ v ∂cond μ (Icc 0 u), v ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  have hp : ∀ᵐ v ∂cond μ (Icc 0 u), 0 < v := by
    filter_upwards [conditional_mem μ (Icc 0 u) measurableSet_Icc, hn] with v hv hv0
    exact lt_of_le_of_ne hv.1 (Ne.symm hv0)
  rw [compactConditional]
  apply (ae_map_iff (measurable_clipToBand 0 u hu).aemeasurable
    (measurableSet_lt measurable_const measurable_subtype_coe)).mpr
  filter_upwards [hp, conditional_mem μ (Icc 0 u) measurableSet_Icc] with v hv hmem
  simpa only [clipToBand_eq 0 u hu hmem] using hv

end OriginalValues
namespace ValueParameters
open OriginalValues

variable (P : ValueParameters)

theorem low_closed_indicator :
    (Icc (0:ℝ) P.d0).indicator (valueDensity P) =
      fun v => lowMass P.theta*bandDensity 0 P.d0 v := by
  funext v
  by_cases hv : v ∈ Icc (0:ℝ) P.d0
  · rw [indicator_of_mem hv, valueDensity_on_low P v hv]
    simp only [bandDensity, indicator_of_mem hv, sub_zero]
    ring
  · simp only [indicator_of_notMem hv, bandDensity, mul_zero]

theorem low_closed_mass :
    valueLaw P (Icc (0:ℝ) P.d0) = ENNReal.ofReal (lowMass P.theta) := by
  have hi : (∫ v in Icc (0:ℝ) P.d0, valueDensity P v) = lowMass P.theta := by
    rw [← integral_indicator measurableSet_Icc, P.low_closed_indicator,
      integral_const_mul, integral_bandDensity 0 P.d0 P.d0_pos, mul_one]
  rw [valueLaw, withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (valueDensity_integrable P).integrableOn
      (Eventually.of_forall (valueDensity_nonneg P)), hi]

def originalLowLaw : Measure (LowBody.LowValue P.d0) :=
  compactConditional (valueLaw P) 0 P.d0 P.d0_pos.le

instance originalLowLaw_probability : IsProbabilityMeasure P.originalLowLaw := by
  apply compactConditional_probability
  rw [P.low_closed_mass]
  exact (ENNReal.ofReal_pos.mpr P.low_mass_pos).ne'

include P in
theorem originalLowLaw_positive :
    ∀ᵐ (v : LowBody.LowValue P.d0) ∂P.originalLowLaw, 0 < v.1 :=
  compactConditional_positive (valueLaw P) P.d0 P.d0_pos.le

theorem originalLowLaw_real :
    P.originalLowLaw.map Subtype.val = cond (valueLaw P) (Icc 0 P.d0) :=
  compactConditional_real (valueLaw P) 0 P.d0 P.d0_pos.le

theorem weighted_originalLowLaw :
    ENNReal.ofReal (lowMass P.theta) • P.originalLowLaw.map Subtype.val =
      (valueLaw P).restrict (Icc 0 P.d0) := by
  rw [P.originalLowLaw_real, ← P.low_closed_mass, Hybrid.measure_smul_cond]

def originalPartialLaw : Measure (Icc (2-P.w) (2+P.w)) :=
  compactConditional (valueLaw P) (2-P.w) (2+P.w) (by linarith [P.w_pos])

instance originalPartialLaw_probability : IsProbabilityMeasure P.originalPartialLaw := by
  apply compactConditional_probability
  have h := P.partial_mass
  intro hz
  change (valueLaw P).real (Icc (2-P.w) (2+P.w)) = partialMass at h
  rw [measureReal_def, hz, ENNReal.toReal_zero] at h
  norm_num [partialMass] at h

theorem originalPartialLaw_real :
    P.originalPartialLaw.map Subtype.val = cond (valueLaw P) P.partialValues :=
  compactConditional_real (valueLaw P) (2-P.w) (2+P.w) (by linarith [P.w_pos])

def originalMovingActiveLaw (t : ℝ) (ht : P.M ≤ t) :
    Measure (Icc (P.vA-P.w) t) :=
  compactConditional (valueLaw P) (P.vA-P.w) t
    (by linarith [P.active_tail_gap, P.w_pos])

theorem originalMovingActiveLaw_probability (t : ℝ) (ht : P.M ≤ t) :
    IsProbabilityMeasure (P.originalMovingActiveLaw t ht) := by
  have hpow : powerTail P.M 10 t ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      ((le_div_iff₀ P.M_pos).2 (by simpa using ht)) (by norm_num)
  have hbound := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg P.active_mass_pos.le P.zeta_pos.le)
  have hstrict := mul_lt_mul_of_pos_left P.zeta_lt_one P.active_mass_pos
  simp only [mul_one] at hbound hstrict
  have hm : activeMass P.theta*P.zeta*powerTail P.M 10 t < activeMass P.theta := by
    exact hbound.trans_lt hstrict
  apply compactConditional_probability
  have h := P.moving_active_mass t ht
  intro hz
  change (valueLaw P).real (Icc (P.vA-P.w) t) = _ at h
  rw [measureReal_def, hz, ENNReal.toReal_zero] at h
  linarith

theorem originalMovingActiveLaw_real (t : ℝ) (ht : P.M ≤ t) :
    (P.originalMovingActiveLaw t ht).map Subtype.val =
      cond (valueLaw P) (P.movingActiveValues t) :=
  compactConditional_real (valueLaw P) (P.vA-P.w) t
    (by linarith [P.active_tail_gap, P.w_pos])

end ValueParameters
namespace OriginalValues
export ValueParameters (low_closed_indicator low_closed_mass originalLowLaw originalLowLaw_positive originalLowLaw_real weighted_originalLowLaw originalPartialLaw originalPartialLaw_real originalMovingActiveLaw originalMovingActiveLaw_probability originalMovingActiveLaw_real)
end OriginalValues
end FCAppendix.Affine.Tail04
