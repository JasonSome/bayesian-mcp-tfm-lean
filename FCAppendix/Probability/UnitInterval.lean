import FCAppendix.PayOnce.Polynomial

namespace FCAppendix
namespace UnitInterval

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integrable (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) : Integrable p μ := by
  apply (integrable_const (1 : ℝ)).mono' hp.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (hp0 ω)]
  exact hp1 ω

theorem integrable_pow (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) (n : ℕ) :
    Integrable (fun ω => (p ω) ^ n) μ := by
  apply integrable μ _ (by fun_prop)
  · intro ω
    exact pow_nonneg (hp0 ω) n
  · intro ω
    simpa using PayOnce.power_mono (hp0 ω) (hp1 ω) n

theorem mean_bounds (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) :
    0 ≤ (∫ ω, p ω ∂μ) ∧ (∫ ω, p ω ∂μ) ≤ 1 := by
  constructor
  · exact integral_nonneg hp0
  · have h := integral_mono (integrable μ p hp hp0 hp1) (integrable_const (1 : ℝ)) hp1
    simpa using h

theorem pow_mean_le (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) (n : ℕ) :
    (∫ ω, p ω ∂μ) ^ n ≤ ∫ ω, (p ω) ^ n ∂μ := by
  apply (convexOn_pow (𝕜 := ℝ) n).map_integral_le
  · fun_prop
  · exact isClosed_Ici
  · exact Filter.Eventually.of_forall hp0
  · exact integrable μ p hp hp0 hp1
  · exact integrable_pow μ p hp hp0 hp1 n

theorem integrable_success (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) (n : ℕ) :
    Integrable (fun ω => PayOnce.success n (p ω)) μ := by
  have hpow := integrable_pow μ (fun ω => 1 - p ω) (measurable_const.sub hp)
    (fun ω => sub_nonneg.mpr (hp1 ω)) (fun ω => by linarith [hp0 ω]) n
  exact (integrable_const (1 : ℝ)).sub hpow

theorem success_mean_le (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) (n : ℕ) :
    (∫ ω, PayOnce.success n (p ω) ∂μ) ≤ PayOnce.success n (∫ ω, p ω ∂μ) := by
  have hq := pow_mean_le μ (fun ω => 1 - p ω) (measurable_const.sub hp)
    (fun ω => sub_nonneg.mpr (hp1 ω)) (fun ω => by linarith [hp0 ω]) n
  have hpint := integrable μ p hp hp0 hp1
  have hpow := integrable_pow μ (fun ω => 1 - p ω) (measurable_const.sub hp)
    (fun ω => sub_nonneg.mpr (hp1 ω)) (fun ω => by linarith [hp0 ω]) n
  rw [integral_sub (integrable_const (1 : ℝ)) hpint] at hq
  simp at hq
  unfold PayOnce.success
  rw [integral_sub (integrable_const (1 : ℝ)) hpow]
  simpa using (show 1 - (∫ ω, (1 - p ω) ^ n ∂μ) ≤
    1 - (1 - ∫ ω, p ω ∂μ) ^ n by linarith)

theorem strict_pow_or_constant (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    p =ᵐ[μ] (fun _ => ∫ ω, p ω ∂μ) ∨
      (∫ ω, p ω ∂μ) ^ n < ∫ ω, (p ω) ^ n ∂μ := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hconv : StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ n) := by
    simpa only [Real.rpow_natCast] using strictConvexOn_rpow hnR
  have h := hconv.ae_eq_const_or_map_average_lt
    (by fun_prop) isClosed_Ici (Filter.Eventually.of_forall hp0)
    (integrable μ p hp hp0 hp1) (integrable_pow μ p hp hp0 hp1 n)
  simpa only [average_eq_integral, Function.const_def] using h

theorem strict_success_or_constant (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    p =ᵐ[μ] (fun _ => ∫ ω, p ω ∂μ) ∨
      (∫ ω, PayOnce.success n (p ω) ∂μ) < PayOnce.success n (∫ ω, p ω ∂μ) := by
  have hpint := integrable μ p hp hp0 hp1
  have hint : (∫ ω, 1 - p ω ∂μ) = 1 - ∫ ω, p ω ∂μ := by
    rw [integral_sub (integrable_const (1 : ℝ)) hpint]
    simp
  rcases strict_pow_or_constant μ (fun ω => 1 - p ω) (measurable_const.sub hp)
      (fun ω => sub_nonneg.mpr (hp1 ω)) (fun ω => by linarith [hp0 ω]) n hn with hc | hs
  · left
    rw [hint] at hc
    filter_upwards [hc] with ω hω
    linarith
  · right
    rw [hint] at hs
    have hpow := integrable_pow μ (fun ω => 1 - p ω) (measurable_const.sub hp)
      (fun ω => sub_nonneg.mpr (hp1 ω)) (fun ω => by linarith [hp0 ω]) n
    unfold PayOnce.success
    rw [integral_sub (integrable_const (1 : ℝ)) hpow]
    simpa using (show 1 - (∫ ω, (1 - p ω) ^ n ∂μ) <
      1 - (1 - ∫ ω, p ω ∂μ) ^ n by linarith)

end UnitInterval
end FCAppendix
