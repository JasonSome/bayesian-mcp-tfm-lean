import FCAppendix.Exclusive.Duplication
import Mathlib.Probability.ConditionalProbability

namespace FCAppendix.Exclusive

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_supported_eq_mass_mul_cond (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (hh : 0 < μ.real E) (f : Ω → ℝ)
    (hs : ∀ᵐ x ∂μ, x ∉ E → f x = 0) :
    (∫ x, f x ∂μ) = μ.real E * ∫ x, f x ∂μ[|E] := by
  classical
  have hr : (∫ x in E, f x ∂μ) = ∫ x, f x ∂μ := by
    rw [← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    by_cases he : x ∈ E
    · simp [Set.indicator_of_mem he]
    · simp [Set.indicator_of_notMem he, hx he]
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, hr]
  change (∫ x, f x ∂μ) = μ.real E * ((μ.real E)⁻¹ * ∫ x, f x ∂μ)
  rw [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

theorem once_success_mono (n : ℕ) {p q : ℝ} (hpq : p ≤ q) (hq : q ≤ 1) :
    PayOnce.success n p ≤ PayOnce.success n q := by
  have h := PayOnce.power_mono (sub_nonneg.mpr hq)
    (show 1 - q ≤ 1 - p by linarith) n
  unfold PayOnce.success
  linarith

theorem supported_binomial_mixture_bounds
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ω → ℝ) (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (E : Set Ω) (hE : MeasurableSet E)
    (hs : ∀ᵐ x ∂μ, x ∉ E → p x = 0) (hh : 0 < μ.real E)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (hcap : (∫ x, p x ∂μ) ≤ t) :
    ((∫ x, PayOnce.success n (p x) ∂μ) ≤
      μ.real E * PayOnce.success n (min (t / μ.real E) 1)) ∧
    (((n : ℝ) - 1) * (∫ x, p x ^ 2 ∂μ) ≤
      (n : ℝ) * (∫ x, p x ∂μ) - ∫ x, PayOnce.success n (p x) ∂μ) ∧
    (((n : ℝ) - 1) / μ.real E * (∫ x, p x ∂μ) ^ 2 ≤
      ((n : ℝ) - 1) * (∫ x, p x ^ 2 ∂μ)) ∧
    (((n : ℝ) - 1) * (∫ x, PayOnce.success n (p x) ∂μ) ^ 2 /
        ((n : ℝ) ^ 2 * μ.real E) ≤
      (n : ℝ) * (∫ x, p x ∂μ) - ∫ x, PayOnce.success n (p x) ∂μ) := by
  have hEN : μ E ≠ 0 := by
    intro he
    have hz : μ.real E = 0 := by simp [Measure.real, he]
    linarith
  letI : IsProbabilityMeasure (μ[|E]) := cond_isProbabilityMeasure hEN
  let a : ℝ := ∫ x, p x ∂μ[|E]
  have ha := UnitInterval.mean_bounds (μ[|E]) p hp hp0 hp1
  change 0 ≤ a ∧ a ≤ 1 at ha
  have hm := integral_supported_eq_mass_mul_cond μ E hE hh p hs
  change (∫ x, p x ∂μ) = μ.real E * a at hm
  have hsq := integral_supported_eq_mass_mul_cond μ E hE hh (fun x => p x ^ 2)
    (hs.mono fun x hx he => by simp [hx he])
  have hsucc := integral_supported_eq_mass_mul_cond μ E hE hh
    (fun x => PayOnce.success n (p x))
    (hs.mono fun x hx he => by simp [hx he, PayOnce.success])
  have hi := UnitInterval.integrable μ p hp hp0 hp1
  have hsi := UnitInterval.integrable_success μ p hp hp0 hp1 n
  have hqi := UnitInterval.integrable_pow μ p hp hp0 hp1 2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hdup : ((n : ℝ) - 1) * (∫ x, p x ^ 2 ∂μ) ≤
      (n : ℝ) * (∫ x, p x ∂μ) - ∫ x, PayOnce.success n (p x) ∂μ := by
    have hi' := integral_mono (hqi.const_mul ((n : ℝ) - 1))
      ((hi.const_mul (n : ℝ)).sub hsi)
      (fun x => binomial_duplicate_lower n hn (p x) (hp0 x) (hp1 x))
    rw [integral_const_mul] at hi'
    simp only [Pi.sub_apply] at hi'
    rw [integral_sub (hi.const_mul (n : ℝ)) hsi, integral_const_mul] at hi'
    exact hi'
  have hid : ((n : ℝ) - 1) / μ.real E * (∫ x, p x ∂μ) ^ 2 =
      μ.real E * ((n : ℝ) - 1) * a ^ 2 := by
    rw [hm]
    field_simp [hh.ne']
  have hcs : ((n : ℝ) - 1) / μ.real E * (∫ x, p x ∂μ) ^ 2 ≤
      ((n : ℝ) - 1) * (∫ x, p x ^ 2 ∂μ) := by
    rw [hid, hsq]
    have hpow := UnitInterval.pow_mean_le (μ[|E]) p hp hp0 hp1 2
    have h := mul_le_mul_of_nonneg_left hpow (mul_nonneg hh.le hn1)
    dsimp only [a]
    nlinarith
  have hcover : (∫ x, PayOnce.success n (p x) ∂μ) ≤
      μ.real E * PayOnce.success n (min (t / μ.real E) 1) := by
    have hacap : a ≤ t / μ.real E := by
      apply (le_div_iff₀ hh).mpr
      rw [hm] at hcap
      simpa only [mul_comm] using hcap
    have haj : a ≤ min (t / μ.real E) 1 := le_min hacap ha.2
    calc
      _ = μ.real E * ∫ x, PayOnce.success n (p x) ∂μ[|E] := hsucc
      _ ≤ μ.real E * PayOnce.success n a :=
        mul_le_mul_of_nonneg_left (UnitInterval.success_mean_le (μ[|E]) p hp hp0 hp1 n) hh.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (once_success_mono n haj (min_le_right _ _)) hh.le
  have hQ0 : 0 ≤ ∫ x, PayOnce.success n (p x) ∂μ :=
    integral_nonneg (f := fun x => PayOnce.success n (p x)) fun x => by
      simpa [IndependentCounts.binomial_success, PayOnce.success] using
        CountLaw.success_nonneg (IndependentCounts.binomial n (p x) (hp0 x) (hp1 x))
  have hload : (∫ x, PayOnce.success n (p x) ∂μ) ≤ (n : ℝ) * μ.real E * a := by
    have h := integral_mono hsi (hi.const_mul (n : ℝ)) fun x => by
      simpa only [IndependentCounts.binomial_success, IndependentCounts.binomial_load,
        PayOnce.success] using
        CountLaw.success_le_load (IndependentCounts.binomial n (p x) (hp0 x) (hp1 x))
    rw [integral_const_mul, hm] at h
    simpa only [mul_assoc] using h
  have hconddup : μ.real E * ((n : ℝ) - 1) * a ^ 2 ≤
      (n : ℝ) * (∫ x, p x ∂μ) - ∫ x, PayOnce.success n (p x) ∂μ := by
    simpa only [hid] using hcs.trans hdup
  exact ⟨hcover, hdup, hcs,
    coverage_quadratic n (μ.real E) _ _ a hnR hh hQ0 ha.1 hload hconddup⟩

theorem supported_binomial_mixture_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ω → ℝ) (E : Set Ω) (hh : μ.real E = 0)
    (hs : ∀ᵐ x ∂μ, x ∉ E → p x = 0) (n : ℕ) :
    p =ᵐ[μ] 0 ∧ (∫ x, p x ∂μ) = 0 ∧
      (∫ x, PayOnce.success n (p x) ∂μ) = 0 := by
  have he : μ E = 0 := (ENNReal.toReal_eq_zero_iff (μ E)).mp hh |>.resolve_right (measure_ne_top μ E)
  have hzero : p =ᵐ[μ] 0 := by
    filter_upwards [hs, measure_eq_zero_iff_ae_notMem.mp he] with x hx hn
    exact hx hn
  refine ⟨hzero, integral_eq_zero_of_ae hzero, ?_⟩
  apply integral_eq_zero_of_ae
  filter_upwards [hzero] with x hx
  simp [hx, PayOnce.success]

theorem once_coverage_cap_strict (n : ℕ) (hn : 2 ≤ n) (h ρ : ℝ)
    (hh : 0 < h) (hρ : 0 < ρ) (hρh : ρ < h) :
    h * PayOnce.success n (ρ / h) < min ((n : ℝ) * ρ) h := by
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < ρ / h := div_pos hρ hh
  have hp1 : ρ / h < 1 := (div_lt_one hh).mpr hρh
  have hd := binomial_duplicate_lower n hn0 (ρ / h) hp0.le hp1.le
  have hdp : 0 < ((n : ℝ) - 1) * (ρ / h) ^ 2 :=
    mul_pos (by linarith) (sq_pos_of_pos hp0)
  have hsload : PayOnce.success n (ρ / h) < (n : ℝ) * (ρ / h) := by linarith
  have hsfail : PayOnce.success n (ρ / h) < 1 := by
    have hp := pow_pos (sub_pos.mpr hp1) n
    unfold PayOnce.success
    linarith
  apply lt_min
  · calc
      h * PayOnce.success n (ρ / h) < h * ((n : ℝ) * (ρ / h)) :=
        mul_lt_mul_of_pos_left hsload hh
      _ = (n : ℝ) * ρ := by field_simp [hh.ne']
  · calc
      h * PayOnce.success n (ρ / h) < h * 1 := mul_lt_mul_of_pos_left hsfail hh
      _ = h := mul_one h

end FCAppendix.Exclusive
