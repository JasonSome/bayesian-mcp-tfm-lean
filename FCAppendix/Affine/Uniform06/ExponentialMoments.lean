import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

noncomputable section
namespace FCAppendix.Affine.Uniform06.ExponentialMoments

open MeasureTheory Set

theorem laplace_moment (n : ℕ) {theta : ℝ} (htheta : 0 < theta) :
    (∫ w in Ioi (0 : ℝ), w ^ n * Real.exp (-(theta * w))) =
      (n.factorial : ℝ) / theta ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := theta) (by positivity) htheta
  have hn : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
  simp only [add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] at h
  rw [hn, Real.rpow_natCast] at h
  simpa only [div_pow, one_pow, one_div, div_eq_mul_inv, mul_comm, mul_one, inv_pow] using h

theorem laplace_moment_integrable (n : ℕ) {theta : ℝ} (htheta : 0 < theta) :
    IntegrableOn (fun w : ℝ => w ^ n * Real.exp (-(theta * w))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [laplace_moment n htheta]
  exact (div_pos (by exact_mod_cast Nat.factorial_pos n)
    (pow_pos htheta _)).ne'

theorem integral_Ioi_sub (f : ℝ → ℝ) (s : ℝ) :
    (∫ w in Ioi s, f (w - s)) = ∫ x in Ioi (0 : ℝ), f x := by
  let g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator f
  have hi : (Ioi s).indicator (fun w => f (w - s)) = fun w => g (w - s) := by
    funext w
    by_cases hw : s < w
    · have hx : 0 < w - s := sub_pos.mpr hw
      simp [g, Set.indicator_of_mem, hw, hx]
    · have hx : ¬0 < w - s := by simpa only [sub_pos] using hw
      simp [g, Set.indicator_of_notMem, hw, hx]
  rw [← integral_indicator measurableSet_Ioi, hi]
  rw [integral_sub_right_eq_self g s]
  exact integral_indicator measurableSet_Ioi

theorem shifted_laplace_moment (n : ℕ) {theta : ℝ} (htheta : 0 < theta)
    (s : ℝ) :
    (∫ w in Ioi s, (w - s) ^ n * Real.exp (-(theta * w))) =
      Real.exp (-(theta * s)) * (n.factorial : ℝ) / theta ^ (n + 1) := by
  have hexp (w : ℝ) : Real.exp (-(theta * w)) =
      Real.exp (-(theta * s)) * Real.exp (-(theta * (w - s))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ∫ w in Ioi s,
        Real.exp (-(theta * s)) *
          ((w - s) ^ n * Real.exp (-(theta * (w - s)))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        dsimp only
        rw [hexp w]
        ring
    _ = Real.exp (-(theta * s)) *
        ∫ w in Ioi s, (w - s) ^ n * Real.exp (-(theta * (w - s))) :=
      integral_const_mul _ _
    _ = Real.exp (-(theta * s)) *
        ∫ x in Ioi (0 : ℝ), x ^ n * Real.exp (-(theta * x)) := by
      congr 1
      exact integral_Ioi_sub (fun x : ℝ => x^n*Real.exp (-(theta*x))) s
    _ = _ := by rw [laplace_moment n htheta]; ring

theorem shifted_laplace_moment_integrable (n : ℕ) {theta : ℝ}
    (htheta : 0 < theta) (s : ℝ) :
    IntegrableOn (fun w : ℝ => (w - s) ^ n * Real.exp (-(theta * w)))
      (Ioi s) := by
  apply Integrable.of_integral_ne_zero
  rw [shifted_laplace_moment n htheta s]
  exact (div_pos (mul_pos (Real.exp_pos _)
    (by exact_mod_cast Nat.factorial_pos n)) (pow_pos htheta _)).ne'

theorem exponential_positive_part_integral_first {theta : ℝ}
    (htheta : 0 < theta) (s : ℝ) :
    (∫ w in Ioi s, (w - s) * Real.exp (-(theta * w))) =
      Real.exp (-(theta * s)) / theta ^ 2 := by
  simpa only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
    using shifted_laplace_moment 1 htheta s

theorem exponential_positive_part_integral_second {theta : ℝ}
    (htheta : 0 < theta) (s : ℝ) :
    (∫ w in Ioi s, (w - s) ^ 2 * Real.exp (-(theta * w))) =
      2 * Real.exp (-(theta * s)) / theta ^ 3 := by
  simpa only [Nat.factorial_two, Nat.cast_ofNat, mul_comm]
    using shifted_laplace_moment 2 htheta s

theorem first_integrable {theta : ℝ} (htheta : 0 < theta) (s : ℝ) :
    IntegrableOn (fun w : ℝ => (w - s) * Real.exp (-(theta * w))) (Ioi s) := by
  simpa only [pow_one] using shifted_laplace_moment_integrable 1 htheta s

theorem second_integrable {theta : ℝ} (htheta : 0 < theta) (s : ℝ) :
    IntegrableOn (fun w : ℝ => (w - s) ^ 2 * Real.exp (-(theta * w))) (Ioi s) :=
  shifted_laplace_moment_integrable 2 htheta s

end FCAppendix.Affine.Uniform06.ExponentialMoments
