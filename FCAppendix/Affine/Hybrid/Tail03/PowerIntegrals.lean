import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory Filter Topology Set Real

def powerTail (t p v : ℝ) : ℝ := (v / t) ^ (-p)

def powerTailPrimitive (t p v : ℝ) : ℝ :=
  -t / (p - 1) * (v / t) ^ (1 - p)

private theorem div_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (fun v : ℝ => v / t) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * t)] with v hv
  exact (le_div_iff₀ ht).2 hv

theorem powerTail_nonneg (t p v : ℝ) (ht : 0 < t) (hv : 0 ≤ v) :
    0 ≤ powerTail t p v := Real.rpow_nonneg (div_nonneg hv ht.le) _

theorem powerTail_at_floor (t p : ℝ) (ht : t ≠ 0) : powerTail t p t = 1 := by
  simp [powerTail, ht]

theorem powerTailPrimitive_hasDerivAt (t p v : ℝ)
    (ht : 0 < t) (hp : p ≠ 1) (hv : 0 < v) :
    HasDerivAt (powerTailPrimitive t p) (powerTail t p v) v := by
  have hratio : v / t ≠ 0 := (div_pos hv ht).ne'
  have h := ((hasDerivAt_rpow_const
    (Or.inl hratio) : HasDerivAt (fun y : ℝ => y ^ (1 - p))
      ((1 - p) * (v / t) ^ ((1 - p) - 1)) (v / t)).comp v
    ((hasDerivAt_id v).div_const t)).const_mul (-t / (p - 1))
  have hd : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  convert! h using 1
  dsimp [powerTail]
  rw [show 1 - p - 1 = -p by ring]
  field_simp [ht.ne',hd]
  ring

theorem powerTailPrimitive_tendsto (t p : ℝ) (ht : 0 < t) (hp : 1 < p) :
    Tendsto (powerTailPrimitive t p) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hp)).comp (div_tendsto_atTop t ht)
  have h' := h.const_mul (-t / (p - 1))
  change Tendsto (fun v : ℝ => -t/(p-1)*(v/t)^(1-p)) atTop (𝓝 0)
  simpa only [show -(p - 1) = 1 - p by ring, Function.comp_apply, mul_zero] using h'

theorem powerTail_integrable (t p : ℝ) (ht : 0 < t) (hp : 1 < p) :
    IntegrableOn (powerTail t p) (Ioi t) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := powerTailPrimitive t p) (l := 0)
  · intro v hv
    exact powerTailPrimitive_hasDerivAt t p v ht hp.ne' (ht.trans_le hv)
  · intro v hv
    exact powerTail_nonneg t p v ht (ht.trans hv).le
  · exact powerTailPrimitive_tendsto t p ht hp

theorem integral_powerTail (t p : ℝ) (ht : 0 < t) (hp : 1 < p) :
    (∫ v in Ioi t, powerTail t p v) = t / (p - 1) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := powerTailPrimitive t p) (f' := powerTail t p) (m := (0 : ℝ))
    (fun v hv => powerTailPrimitive_hasDerivAt t p v ht hp.ne' (ht.trans_le hv))
    (powerTail_integrable t p ht hp) (powerTailPrimitive_tendsto t p ht hp)
  simpa [powerTailPrimitive, ht.ne', neg_div] using h

theorem integral_powerTail_above (t p s : ℝ) (ht : 0 < t) (hp : 1 < p)
    (hs : t ≤ s) :
    (∫ v in Ioi s, powerTail t p v) =
      t / (p - 1) * (s / t) ^ (1 - p) := by
  have hi : IntegrableOn (powerTail t p) (Ioi s) :=
    (powerTail_integrable t p ht hp).mono_set (Ioi_subset_Ioi hs)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := powerTailPrimitive t p) (f' := powerTail t p) (m := (0 : ℝ))
    (fun v hv => powerTailPrimitive_hasDerivAt t p v ht hp.ne'
      (ht.trans_le (hs.trans hv))) hi (powerTailPrimitive_tendsto t p ht hp)
  simpa [powerTailPrimitive, neg_div] using h

theorem value_mul_powerTail (t p v : ℝ) (ht : 0 < t) (hv : 0 < v) :
    v * powerTail t p v = t * powerTail t (p - 1) v := by
  have hr : 0 < v / t := div_pos hv ht
  dsimp [powerTail]
  rw [show -(p - 1) = 1 + (-p) by ring, Real.rpow_add hr]
  rw [Real.rpow_one]
  field_simp

theorem value_powerTail_integrable (t p : ℝ) (ht : 0 < t) (hp : 2 < p) :
    IntegrableOn (fun v => v * powerTail t p v) (Ioi t) := by
  have h := (powerTail_integrable t (p - 1) ht (by linarith)).const_mul t
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (value_mul_powerTail t p v ht (ht.trans hv)).symm

theorem integral_value_powerTail (t p : ℝ) (ht : 0 < t) (hp : 2 < p) :
    (∫ v in Ioi t, v * powerTail t p v) = t ^ 2 / (p - 2) := by
  calc
    _ = ∫ v in Ioi t, t * powerTail t (p - 1) v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      exact value_mul_powerTail t p v ht (ht.trans hv)
    _ = t * (∫ v in Ioi t, powerTail t (p - 1) v) := integral_const_mul _ _
    _ = t ^ 2 / (p - 2) := by
      rw [integral_powerTail t (p - 1) ht (by linarith)]
      ring

theorem failure_integrals (f : ℝ → ℝ) (D t p : ℝ)
    (ht : 0 < t) (hp : 2 < p) (_hD : 0 ≤ D)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi t)))
    (hf : ∀ v ∈ Ioi t, 0 ≤ f v ∧ f v ≤ D * powerTail t p v) :
    IntegrableOn f (Ioi t) ∧
    IntegrableOn (fun v => v * f v) (Ioi t) ∧
    (∫ v in Ioi t, f v) ≤ D * t / (p - 1) ∧
    (∫ v in Ioi t, v * f v) ≤ D * t ^ 2 / (p - 2) := by
  have hmaj := (powerTail_integrable t p ht (by linarith)).const_mul D
  have hwmaj := (value_powerTail_integrable t p ht hp).const_mul D
  have hi : IntegrableOn f (Ioi t) := by
    apply hmaj.mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf v hv).1] using (hf v hv).2
  have hwi : IntegrableOn (fun v => v * f v) (Ioi t) := by
    apply hwmaj.mono' (aestronglyMeasurable_id.mul hm)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 ≤ v := (ht.trans hv).le
    have h := mul_le_mul_of_nonneg_left (hf v hv).2 hv0
    simpa [Real.norm_eq_abs, abs_of_nonneg hv0, abs_of_nonneg (hf v hv).1,
      mul_assoc, mul_left_comm, mul_comm] using h
  refine ⟨hi, hwi, ?_, ?_⟩
  · calc
      _ ≤ ∫ v in Ioi t, D * powerTail t p v := by
        apply integral_mono_ae hi hmaj
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        exact (hf v hv).2
      _ = D * t / (p - 1) := by
        rw [integral_const_mul, integral_powerTail t p ht (by linarith)]
        ring
  · calc
      _ ≤ ∫ v in Ioi t, D * (v * powerTail t p v) := by
        apply integral_mono_ae hwi hwmaj
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        have h := mul_le_mul_of_nonneg_left (hf v hv).2 (ht.trans hv).le
        simpa [mul_assoc, mul_left_comm, mul_comm] using h
      _ = D * t ^ 2 / (p - 2) := by
        rw [integral_const_mul, integral_value_powerTail t p ht hp]
        ring

theorem weighted_majorant_le_tD (D t : ℝ) (c : ℕ)
    (_hD : 0 ≤ D) (ht : 0 < t) (hc : 1 ≤ c) (htc : t ≤ (c : ℝ)) :
    D * t ^ 2 / (10 * (c : ℝ) - 2) ≤ D * t := by
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hp : 0 < 10 * (c : ℝ) - 2 := by linarith
  apply (div_le_iff₀ hp).2
  have htc' : t ≤ 10 * (c : ℝ) - 2 := by linarith
  have h := mul_le_mul_of_nonneg_left htc' (mul_nonneg _hD ht.le)
  nlinarith

def paretoTailDensity (h t v : ℝ) : ℝ := 10 * h / t * powerTail t 11 v

theorem pareto_density_weight_identity (h t p v : ℝ)
    (ht : 0 < t) (hv : 0 < v) :
    v * powerTail t p v * paretoTailDensity h t v =
      10 * h * powerTail t (p + 10) v := by
  have hr : 0 < v / t := div_pos hv ht
  dsimp [paretoTailDensity, powerTail]
  rw [show -(p + 10) = 1 + (-p) + (-11 : ℝ) by ring,
    Real.rpow_add hr, Real.rpow_add hr, Real.rpow_one]
  field_simp

theorem integral_pareto_weighted_majorant (D h t p : ℝ)
    (ht : 0 < t) (hp : 0 ≤ p) :
    (∫ v in Ioi t, v * (D * powerTail t p v) * paretoTailDensity h t v) =
      10 * h * D * t / (p + 9) := by
  calc
    _ = ∫ v in Ioi t, (10 * h * D) * powerTail t (p + 10) v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      have hid := pareto_density_weight_identity h t p v ht (ht.trans hv)
      calc
        _ = D * (v * powerTail t p v * paretoTailDensity h t v) := by ring
        _ = D * (10 * h * powerTail t (p + 10) v) := by rw [hid]
        _ = _ := by ring
    _ = (10 * h * D) * (∫ v in Ioi t, powerTail t (p + 10) v) :=
      integral_const_mul _ _
    _ = 10 * h * D * t / (p + 9) := by
      rw [integral_powerTail t (p + 10) ht (by linarith)]
      ring

end FCAppendix.Affine.Hybrid.Tail03
