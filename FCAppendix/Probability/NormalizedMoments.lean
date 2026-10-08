import FCAppendix.Probability.L1WeakConvergence

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology Real

theorem add_natPow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℕ) :
    (a+b)^r ≤ 2^r*(a^r+b^r) := by
  rcases le_total a b with hab | hba
  · calc
      _ ≤ (2*b)^r := pow_le_pow_left₀ (add_nonneg ha hb) (by linarith) r
      _ = 2^r*b^r := mul_pow _ _ _
      _ ≤ 2^r*(a^r+b^r) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg ha r)) (by positivity)
  · calc
      _ ≤ (2*a)^r := pow_le_pow_left₀ (add_nonneg ha hb) (by linarith) r
      _ = 2^r*a^r := mul_pow _ _ _
      _ ≤ 2^r*(a^r+b^r) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg hb r)) (by positivity)

theorem memLp_unitInterval_div_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Ω → ℝ) (hp : Measurable p)
    (hpb : ∀ ω, p ω ∈ Icc (0:ℝ) 1) (s : ℝ) (j : ℕ) :
    MemLp (fun ω => (p ω/s)^j) 2 μ := by
  have hb ω : |(p ω/s)^j| ≤ (1/|s|)^j := by
    rw [abs_pow,abs_div,abs_of_nonneg (hpb ω).1]
    exact pow_le_pow_left₀ (div_nonneg (hpb ω).1 (abs_nonneg s)) (div_le_div_of_nonneg_right (hpb ω).2 (abs_nonneg s)) j
  apply memLp_of_bounded (a := -((1/|s|)^j)) (b := (1/|s|)^j) ?_ (by fun_prop) 2
  exact .of_forall fun ω => abs_le.mp (hb ω)

theorem integral_unitInterval_div_pow_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → ℝ) (hp : Measurable p)
    (hpb : ∀ ω, p ω ∈ Icc (0:ℝ) 1) {s q D K : ℝ}
    (hs : 0 < s) (hq : |q|/s ≤ D) (r : ℕ)
    (hi : Integrable (fun ω => |p ω-q|^r) μ)
    (hK : (∫ ω, |p ω-q|^r ∂μ)/s^r ≤ K) :
    (∫ ω, (p ω/s)^r ∂μ) ≤ 2^r*(K+D^r) := by
  have hD : 0 ≤ D := (div_nonneg (abs_nonneg q) hs.le).trans hq
  have hb ω : (p ω/s)^r ≤ 2^r*((|p ω-q|/s)^r+D^r) := by
    have h0 : p ω ≤ |p ω-q|+|q| := by
      simpa only [sub_add_cancel,abs_of_nonneg (hpb ω).1] using (abs_add_le (p ω-q) q)
    have h1 : p ω/s ≤ |p ω-q|/s+D := by
      have hh := div_le_div_of_nonneg_right h0 hs.le
      rw [add_div] at hh
      linarith
    exact (pow_le_pow_left₀ (div_nonneg (hpb ω).1 hs.le) h1 r).trans
      (add_natPow_le (by positivity) hD r)
  have hleft : Integrable (fun ω => (p ω/s)^r) μ :=
    (memLp_unitInterval_div_pow μ p hp hpb s r).integrable (by norm_num)
  have hright : Integrable (fun ω => 2^r*((|p ω-q|/s)^r+D^r)) μ := by
    simpa only [div_pow,Pi.add_apply] using ((hi.div_const (s^r)).add (integrable_const (D^r))).const_mul (2^r)
  have hh := integral_mono hleft hright hb
  have hii : Integrable (fun ω => (|p ω-q|/s)^r) μ := by
    simpa only [div_pow] using hi.div_const (s^r)
  rw [integral_const_mul,integral_add hii (integrable_const _)] at hh
  simp only [div_pow,integral_div,integral_const,probReal_univ,one_smul] at hh
  simpa only [div_pow,integral_div] using
    hh.trans (mul_le_mul_of_nonneg_left (add_le_add hK le_rfl) (by positivity))

end FCAppendix.Probability
