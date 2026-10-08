import FCAppendix.Probability.FiniteTiltCalculus

namespace FCAppendix.FiniteCramer

open Real Set CommonList SimultaneousCongestion
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem variance_le_quarter (ν : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ x, X x ∈ Icc (0 : ℝ) 1) : variance ν X ≤ 1 / 4 := by
  have hb : ν.expect (fun x => (X x - 1 / 2) ^ 2) ≤ 1 / 4 := by
    apply ν.expect_le_const
    intro x
    have h := hX x
    nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
  have he : ν.expect (fun x => (X x - 1 / 2) ^ 2) =
      ν.expect (fun x => X x ^ 2) - ν.expect X + 1 / 4 := by
    calc
      _ = ν.expect (fun x => X x ^ 2 - X x + 1 / 4) :=
        ν.expect_congr (fun _ => by ring)
      _ = _ := by rw [ν.expect_add, ν.expect_sub, ν.expect_const]
  rw [he] at hb
  rw [variance_eq]
  nlinarith [sq_nonneg (ν.expect X - 1 / 2)]

theorem mean_linear_bounds (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ x, X x ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    (0 ≤ θ → mean μ X θ ≤ μ.expect X + θ / 4) ∧
    (θ ≤ 0 → μ.expect X + θ / 4 ≤ mean μ X θ) := by
  constructor
  · intro hθ
    rcases hθ.eq_or_lt with hθ | hθ
    · subst θ; simp
    · obtain ⟨t, _, hd⟩ := exists_deriv_eq_slope (mean μ X) hθ
        (differentiable_mean μ X).continuous.continuousOn
        (differentiable_mean μ X).differentiableOn
      rw [deriv_mean, mean_zero, sub_zero] at hd
      have hv := variance_le_quarter (tilted μ X t) X hX
      rw [hd] at hv
      have hh := (div_le_iff₀ hθ).mp hv
      linarith
  · intro hθ
    rcases hθ.eq_or_lt with hθ | hθ
    · subst θ; simp
    · obtain ⟨t, _, hd⟩ := exists_deriv_eq_slope (mean μ X) hθ
        (differentiable_mean μ X).continuous.continuousOn
        (differentiable_mean μ X).differentiableOn
      rw [deriv_mean, mean_zero] at hd
      have hv := variance_le_quarter (tilted μ X t) X hX
      rw [hd] at hv
      have hh := (div_le_iff₀ (sub_pos.mpr hθ)).mp hv
      linarith

theorem cgf_le_quadratic (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ x, X x ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    cgf μ X θ ≤ μ.expect X * θ + θ ^ 2 / 8 := by
  let f : ℝ → ℝ := fun t => cgf μ X t - μ.expect X * t - t ^ 2 / 8
  have hd (t : ℝ) : HasDerivAt f (mean μ X t - μ.expect X - t / 4) t := by
    dsimp only [f]
    convert ((hasDerivAt_cgf μ X t).sub ((hasDerivAt_id t).const_mul (μ.expect X))).sub
      (((hasDerivAt_id t).pow 2).div_const 8) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hf : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hf0 : f 0 = 0 := by simp [f]
  have hnonpos : f θ ≤ 0 := by
    rcases lt_trichotomy θ 0 with hθ | hθ | hθ
    · obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope f hθ hf.continuous.continuousOn hf.differentiableOn
      rw [(hd t).deriv, hf0] at he
      have hm := (mean_linear_bounds μ X hX t).2 ht.2.le
      have hs : 0 ≤ (0 - f θ) / (0 - θ) := by linarith
      have hprod := (le_div_iff₀ (sub_pos.mpr hθ)).mp hs
      linarith
    · rw [hθ, hf0]
    · obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope f hθ hf.continuous.continuousOn hf.differentiableOn
      rw [(hd t).deriv, hf0] at he
      have hm := (mean_linear_bounds μ X hX t).1 ht.1.le
      have hs : (f θ - 0) / (θ - 0) ≤ 0 := by linarith
      have hprod := (div_le_iff₀ (sub_pos.mpr hθ)).mp hs
      linarith
  dsimp [f] at hnonpos
  linarith

theorem iid_chernoff (μ : FiniteLaw Ω) (X : Ω → ℝ) (N : ℕ) (θ z : ℝ)
    (E : (Fin N → Ω) → Prop)
    (hE : ∀ T, E T → θ * z ≤ θ * ∑ i, X (T i)) :
    (iid μ N).prob E ≤ exp (-θ * z + N * cgf μ X θ) := by
  classical
  have hpoint : ∀ T : Fin N → Ω, (if E T then (1 : ℝ) else 0) ≤
      exp (-θ * z) * ∏ i, exp (θ * X (T i)) := by
    intro T
    have he : exp (-θ * z) * ∏ i, exp (θ * X (T i)) =
        exp (θ * (∑ i, X (T i)) - θ * z) := by
      rw [← exp_sum, ← exp_add, ← Finset.mul_sum]
      congr 1
      ring
    rw [he]
    by_cases ht : E T
    · rw [if_pos ht]
      exact one_le_exp (sub_nonneg.mpr (hE T ht))
    · rw [if_neg ht]
      exact (exp_pos _).le
  have hm := (iid μ N).expect_mono hpoint
  rw [FiniteLaw.expect_const_mul, expect_iid_prod μ N (fun x => exp (θ * X x))] at hm
  change (iid μ N).prob E ≤ exp (-θ * z) * Z μ X θ ^ N at hm
  have hZ : Z μ X θ ^ N = exp ((N : ℝ) * cgf μ X θ) := by
    rw [cgf, exp_nat_mul, exp_log (Z_pos μ X θ)]
  rw [hZ, ← exp_add] at hm
  exact hm

theorem iid_upper_hoeffding (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ x, X x ∈ Icc (0 : ℝ) 1) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (iid μ N).prob (fun T => (N : ℝ) * (μ.expect X + δ) ≤ ∑ i, X (T i)) ≤
      exp (-2 * N * δ ^ 2) := by
  have hh := iid_chernoff μ X N (4 * δ) (N * (μ.expect X + δ))
    (fun T => (N : ℝ) * (μ.expect X + δ) ≤ ∑ i, X (T i))
    (fun _ h => mul_le_mul_of_nonneg_left h (by positivity))
  apply hh.trans
  apply exp_le_exp.mpr
  have hc := mul_le_mul_of_nonneg_left (cgf_le_quadratic μ X hX (4 * δ))
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

theorem iid_lower_hoeffding (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ x, X x ∈ Icc (0 : ℝ) 1) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (iid μ N).prob (fun T => (∑ i, X (T i)) ≤ (N : ℝ) * (μ.expect X - δ)) ≤
      exp (-2 * N * δ ^ 2) := by
  have hh := iid_chernoff μ X N (-4 * δ) (N * (μ.expect X - δ))
    (fun T => (∑ i, X (T i)) ≤ (N : ℝ) * (μ.expect X - δ))
    (fun _ h => mul_le_mul_of_nonpos_left h (by nlinarith))
  apply hh.trans
  apply exp_le_exp.mpr
  have hc := mul_le_mul_of_nonneg_left (cgf_le_quadratic μ X hX (-4 * δ))
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

end FCAppendix.FiniteCramer
