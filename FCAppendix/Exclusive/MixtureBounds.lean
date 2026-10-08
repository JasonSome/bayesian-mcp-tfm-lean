import FCAppendix.Exclusive.Duplication

namespace FCAppendix.Exclusive

open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem pow_tangent_succ (r : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (r + 1) + ((r + 1 : ℕ) : ℝ) * x ^ r * (y - x) ≤ y ^ (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h₁ := mul_nonneg hy (sub_nonneg.mpr ih)
    have h₂ : 0 ≤ ((r + 1 : ℕ) : ℝ) * x ^ r * (y - x) ^ 2 :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)) (sq_nonneg _)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at *
    nlinarith

noncomputable def successSlope (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) * (1 - p) ^ (n - 1)

theorem successSlope_nonneg (n : ℕ) {p : ℝ} (hp : p ≤ 1) :
    0 ≤ successSlope n p :=
  mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (sub_nonneg.mpr hp) _)

theorem success_tangent (n : ℕ) {p q : ℝ} (hp : p ≤ 1) (hq : q ≤ 1) :
    PayOnce.success n p ≤ PayOnce.success n q + successSlope n q * (p - q) := by
  cases n with
  | zero => simp [PayOnce.success, successSlope]
  | succ r =>
    have h := pow_tangent_succ r (sub_nonneg.mpr hq) (sub_nonneg.mpr hp)
    simp only [PayOnce.success, successSlope, Nat.add_sub_cancel]
    nlinarith

section Mixture

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (p : Ω → ℝ) (hp : Measurable p)
variable (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1)
variable (E : Set Ω) (hE : MeasurableSet E)
variable (hz : ∀ᵐ ω ∂P, ω ∉ E → p ω = 0)

include hp hp0 hp1 hE hz

theorem supported_mean_le_mass : (∫ ω, p ω ∂P) ≤ P.real E := by
  have hpi := UnitInterval.integrable P p hp hp0 hp1
  have h := integral_mono_ae hpi ((integrable_const (1 : ℝ)).indicator hE) (by
    filter_upwards [hz] with ω hω
    by_cases he : ω ∈ E
    · simpa only [indicator_of_mem he] using hp1 ω
    · simp only [indicator_of_notMem he, hω he, le_refl])
  simpa only [integral_indicator_const (μ := P) (1 : ℝ) hE, smul_eq_mul, mul_one] using h

theorem supported_success_le (n : ℕ) {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmean : (∫ ω, p ω ∂P) ≤ P.real E * q) :
    (∫ ω, PayOnce.success n (p ω) ∂P) ≤ P.real E * PayOnce.success n q := by
  have hpi := UnitInterval.integrable P p hp hp0 hp1
  have hsi := UnitInterval.integrable_success P p hp hp0 hp1 n
  have hzi : Integrable (E.indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hE
  let d := successSlope n q
  let a := PayOnce.success n q - d * q
  have hi : Integrable (fun ω => a * E.indicator (1 : Ω → ℝ) ω + d * p ω) P :=
    (hzi.const_mul a).add (hpi.const_mul d)
  have hpoint : ∀ᵐ ω ∂P,
      PayOnce.success n (p ω) ≤ a * E.indicator (1 : Ω → ℝ) ω + d * p ω := by
    filter_upwards [hz] with ω hω
    by_cases he : ω ∈ E
    · rw [indicator_of_mem he]
      simp only [Pi.one_apply]
      have h := success_tangent n (hp1 ω) hq1
      dsimp only [a, d]
      nlinarith
    · simp [hω he, indicator_of_notMem he, PayOnce.success]
  have h := integral_mono_ae hsi hi hpoint
  rw [integral_add (hzi.const_mul a) (hpi.const_mul d),
    integral_const_mul, integral_const_mul, integral_indicator_one hE] at h
  have hd : 0 ≤ d := successSlope_nonneg n hq1
  have hmul := mul_le_mul_of_nonneg_left hmean hd
  dsimp only [a] at h
  nlinarith

theorem supported_capacity_success_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hh : 0 < P.real E) (hmean : (∫ ω, p ω ∂P) ≤ u) :
    (∫ ω, PayOnce.success n (p ω) ∂P) ≤
      P.real E * PayOnce.success n (min (u / P.real E) 1) := by
  apply supported_success_le P p hp hp0 hp1 E hE hz n
    (le_min (div_nonneg hu hh.le) zero_le_one) (min_le_right _ _)
  by_cases hq : u / P.real E ≤ 1
  · rw [min_eq_left hq]
    simpa only [mul_div_cancel₀ _ hh.ne'] using hmean
  · rw [min_eq_right (le_of_not_ge hq), mul_one]
    exact supported_mean_le_mass P p hp hp0 hp1 E hE hz

theorem supported_square_mean (hh : 0 < P.real E) :
    (∫ ω, p ω ∂P) ^ 2 / P.real E ≤ ∫ ω, (p ω) ^ 2 ∂P := by
  let a := (∫ ω, p ω ∂P) / P.real E
  have hpi := UnitInterval.integrable P p hp hp0 hp1
  have hsq := UnitInterval.integrable_pow P p hp hp0 hp1 2
  have hzi : Integrable (E.indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hE
  have hpoint : ∀ᵐ ω ∂P,
      2 * a * p ω - a ^ 2 * E.indicator (1 : Ω → ℝ) ω ≤ (p ω) ^ 2 := by
    filter_upwards [hz] with ω hω
    by_cases he : ω ∈ E
    · rw [indicator_of_mem he]
      simp only [Pi.one_apply]
      nlinarith [sq_nonneg (p ω - a)]
    · simp [indicator_of_notMem he, hω he]
  have h := integral_mono_ae ((hpi.const_mul (2 * a)).sub (hzi.const_mul (a ^ 2))) hsq hpoint
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hpi.const_mul (2 * a)) (hzi.const_mul (a ^ 2)),
    integral_const_mul, integral_const_mul, integral_indicator_one hE] at h
  have he : 2 * a * (∫ ω, p ω ∂P) - a ^ 2 * P.real E =
      (∫ ω, p ω ∂P) ^ 2 / P.real E := by
    dsimp only [a]
    field_simp [hh.ne']
    ring
  rwa [he] at h

theorem supported_duplicate_lower (n : ℕ) (hn : 1 ≤ n) (hh : 0 < P.real E) :
    ((n : ℝ) - 1) * (∫ ω, p ω ∂P) ^ 2 / P.real E ≤
      (n : ℝ) * (∫ ω, p ω ∂P) - ∫ ω, PayOnce.success n (p ω) ∂P := by
  have hpi := UnitInterval.integrable P p hp hp0 hp1
  have hsi := UnitInterval.integrable_success P p hp hp0 hp1 n
  have hsq := UnitInterval.integrable_pow P p hp hp0 hp1 2
  have h := integral_mono (hsq.const_mul ((n : ℝ) - 1))
    ((hpi.const_mul (n : ℝ)).sub hsi)
    (fun ω => binomial_duplicate_lower n hn (p ω) (hp0 ω) (hp1 ω))
  simp only [Pi.sub_apply] at h
  rw [integral_const_mul, integral_sub (hpi.const_mul (n : ℝ)) hsi,
    integral_const_mul] at h
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcs := mul_le_mul_of_nonneg_left
    (supported_square_mean P p hp hp0 hp1 E hE hz hh) (sub_nonneg.mpr hnR)
  simp only [mul_div_assoc] at ⊢
  exact hcs.trans h

theorem supported_coverage_quadratic (n : ℕ) (hn : 1 ≤ n) (hh : 0 < P.real E) :
    ((n : ℝ) - 1) * (∫ ω, PayOnce.success n (p ω) ∂P) ^ 2 /
        ((n : ℝ) ^ 2 * P.real E) ≤
      (n : ℝ) * (∫ ω, p ω ∂P) - ∫ ω, PayOnce.success n (p ω) ∂P := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := UnitInterval.integrable P p hp hp0 hp1
  have hsi := UnitInterval.integrable_success P p hp hp0 hp1 n
  have hs0 (ω : Ω) : 0 ≤ PayOnce.success n (p ω) := by
    simpa only [IndependentCounts.binomial_success, PayOnce.success] using
      (IndependentCounts.binomial n (p ω) (hp0 ω) (hp1 ω)).success_nonneg
  have hmean : 0 ≤ ∫ ω, p ω ∂P := integral_nonneg hp0
  have hload : (∫ ω, PayOnce.success n (p ω) ∂P) ≤ (n : ℝ) * (∫ ω, p ω ∂P) := by
    have h := integral_mono hsi (hpi.const_mul n) (fun ω => by
      simpa only [IndependentCounts.binomial_success, IndependentCounts.binomial_load,
        PayOnce.success] using
        (IndependentCounts.binomial n (p ω) (hp0 ω) (hp1 ω)).success_le_load)
    simpa only [integral_const_mul] using h
  apply coverage_quadratic (n : ℝ) (P.real E) _ _
    ((∫ ω, p ω ∂P) / P.real E) hnR hh (integral_nonneg hs0) (div_nonneg hmean hh.le)
  · simpa [mul_assoc, mul_div_cancel₀ _ hh.ne'] using hload
  · have he : P.real E * ((n : ℝ) - 1) *
        ((∫ ω, p ω ∂P) / P.real E) ^ 2 =
        ((n : ℝ) - 1) * (∫ ω, p ω ∂P) ^ 2 / P.real E := by
      field_simp [hh.ne']
    rw [he]
    exact supported_duplicate_lower P p hp hp0 hp1 E hE hz n hn hh

end Mixture

theorem coverage_bound_strict (n : ℕ) (hn : 2 ≤ n) {rho h : ℝ}
    (hrho : 0 < rho) (hrhoh : rho < h) :
    h * PayOnce.success n (rho / h) < min ((n : ℝ) * rho) h := by
  have hh : 0 < h := hrho.trans hrhoh
  have hp0 : 0 < rho / h := div_pos hrho hh
  have hp1 : rho / h < 1 := (div_lt_one hh).mpr hrhoh
  have hdup := binomial_duplicate_lower n (by omega) (rho / h) hp0.le hp1.le
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hdpos : 0 < ((n : ℝ) - 1) * (rho / h) ^ 2 := by positivity
  have hslt : PayOnce.success n (rho / h) < (n : ℝ) * (rho / h) := by linarith
  have hsone : PayOnce.success n (rho / h) < 1 := by
    have hpow : 0 < (1 - rho / h) ^ n := pow_pos (sub_pos.mpr hp1) _
    dsimp only [PayOnce.success]
    linarith
  refine lt_min ?_ ?_
  · have h := mul_lt_mul_of_pos_left hslt hh
    convert h using 1
    field_simp [hh.ne']
  · simpa only [mul_one] using mul_lt_mul_of_pos_left hsone hh

theorem exists_near_full_multiplicity (n : ℕ) (hn : 2 ≤ n)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ p : ℝ, 1 / (n : ℝ) < p ∧ p < 1 ∧
      (n : ℝ) - zeta < (n : ℝ) * p / PayOnce.success n p := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hnR
  have hmax : max (1 / (n : ℝ)) (1 - zeta / n) < 1 := by
    apply max_lt
    · exact (div_lt_one hn0).mpr hnR
    · have hdiv := div_pos hzeta hn0
      linarith
  obtain ⟨p, hlo, hp1⟩ := exists_between hmax
  have hpmin : 1 / (n : ℝ) < p := (le_max_left _ _).trans_lt hlo
  have hp0 : 0 < p := (one_div_pos.mpr hn0).trans hpmin
  have hz : (n : ℝ) - zeta < (n : ℝ) * p := by
    have h := (le_max_right _ _).trans_lt hlo
    have hmul := mul_lt_mul_of_pos_left h hn0
    have hcancel : (n : ℝ) * (1 - zeta / n) = (n : ℝ) - zeta := by
      field_simp [hn0.ne']
    rwa [hcancel] at hmul
  have hs := PayOnce.success_pos n (by omega) p hp0 hp1.le
  have hnp : 0 ≤ (n : ℝ) * p := (mul_pos hn0 hp0).le
  have hquot : (n : ℝ) * p ≤ (n : ℝ) * p / PayOnce.success n p := by
    apply (le_div_iff₀ hs).mpr
    exact mul_le_of_le_one_right hnp (PayOnce.success_le_one n p hp1.le)
  exact ⟨p, hpmin, hp1, hz.trans_le hquot⟩

end FCAppendix.Exclusive
