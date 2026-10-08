import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi

namespace FCAppendix.Probability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

theorem integral_abs_sub_integral_le_sqrt_variance
    (μ : Measure α) [IsProbabilityMeasure μ] {h : α → ℝ} (hh : MemLp h 2 μ) :
    (∫ x, |h x - ∫ y, h y ∂μ| ∂μ) ≤ Real.sqrt (variance h μ) := by
  have hc : MemLp (fun x => |h x - ∫ y, h y ∂μ|) 2 μ := (hh.sub (memLp_const _)).abs
  have hs := variance_nonneg (fun x => |h x - ∫ y, h y ∂μ|) μ
  rw [variance_eq_sub hc] at hs
  simp only [Pi.pow_apply, sq_abs] at hs
  rw [← variance_eq_integral hh.aemeasurable] at hs
  apply (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _)) (variance_nonneg h μ)).mpr
  linarith

theorem iid_empiricalMean_L1_le
    (μ : Measure α) [IsProbabilityMeasure μ] {h : α → ℝ}
    (hh : AEStronglyMeasurable h μ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, |h x| ≤ B) (m : ℕ) (hm : 0 < m) :
    (∫ x : Fin m → α,
      |(∑ i, h (x i)) / m - ∫ y, h y ∂μ| ∂Measure.pi (fun _ : Fin m => μ)) ≤
      B / Real.sqrt m := by
  let ν := Measure.pi (fun _ : Fin m => μ)
  let S : (Fin m → α) → ℝ := fun x => ∑ i, h (x i)
  have hL : MemLp h 2 μ := MemLp.of_bound hh B (by simpa only [Real.norm_eq_abs] using hb)
  have hLi (i : Fin m) : MemLp (fun x : Fin m → α => h (x i)) 2 ν :=
    hL.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => μ) i)
  have hS : MemLp S 2 ν := by
    exact memLp_finsetSum _ (fun i _ => hLi i)
  have hmean : MemLp (fun x => S x / (m : ℝ)) 2 ν := by
    simpa only [div_eq_mul_inv] using hS.mul_const ((m : ℝ)⁻¹)
  have hi : (∫ x, S x / (m : ℝ) ∂ν) = ∫ y, h y ∂μ := by
    rw [integral_div]
    have he : (∫ x, S x ∂ν) = (m : ℝ) * ∫ y, h y ∂μ := by
      dsimp only [S, ν]
      rw [integral_finsetSum _ (fun i _ => (hLi i).integrable (by norm_num))]
      have hcomp (i : Fin m) :
          (∫ x : Fin m → α, h (x i) ∂Measure.pi (fun _ : Fin m => μ)) = ∫ y, h y ∂μ :=
        integral_comp_eval (μ := fun _ : Fin m => μ) hh
      simp only [ν, hcomp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [he, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hm.ne')]
  have hvar : variance (fun x => S x / (m : ℝ)) ν = variance h μ / m := by
    have he : variance S ν = (m : ℝ) * variance h μ := by
      have heq : (∑ i : Fin m, fun x : Fin m → α => h (x i)) = S := by ext; simp [S]
      have hh := variance_sum_pi (μ := fun _ : Fin m => μ) (X := fun _ => h) (fun _ => hL)
      rw [heq] at hh
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
    simp only [div_eq_mul_inv, variance_mul_const, he]
    field_simp
  have hvle : variance h μ ≤ B ^ 2 := by
    apply (variance_le_expectation_sq hL.aestronglyMeasurable).trans
    calc
      (∫ x, h x ^ 2 ∂μ) ≤ ∫ _x, B ^ 2 ∂μ := by
        apply integral_mono_ae hL.integrable_sq (integrable_const _)
        filter_upwards [hb] with x hx
        nlinarith [sq_abs (h x), abs_nonneg (h x)]
      _ = B ^ 2 := by simp
  have hbound := integral_abs_sub_integral_le_sqrt_variance ν hmean
  rw [hi, hvar] at hbound
  apply hbound.trans
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hs : (Real.sqrt (m : ℝ)) ^ 2 = m := Real.sq_sqrt hmR.le
  rw [div_pow, hs]
  exact div_le_div_of_nonneg_right hvle hmR.le

theorem iid_empiricalMean_L1_tendsto_zero
    (μ : ℕ → Measure α) [∀ k, IsProbabilityMeasure (μ k)] (h : ℕ → α → ℝ)
    (hh : ∀ k, AEStronglyMeasurable (h k) (μ k)) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, ∀ᵐ x ∂μ k, |h k x| ≤ B)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun k => ∫ x : Fin (M k) → α,
      |(∑ i, h k (x i)) / M k - ∫ y, h k y ∂μ k|
        ∂Measure.pi (fun _ : Fin (M k) => μ k)) atTop (𝓝 0) := by
  have hMR : Tendsto (fun k => (M k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hbound : Tendsto (fun k => B / Real.sqrt (M k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hMR)).const_mul B
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
    _ hbound
  filter_upwards [hM.eventually_gt_atTop 0] with k hk
  exact iid_empiricalMean_L1_le (μ k) (hh k) B hB (hb k) (M k) hk

end FCAppendix.Probability
