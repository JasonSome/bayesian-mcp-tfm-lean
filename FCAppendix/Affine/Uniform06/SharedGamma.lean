import FCAppendix.Affine.Uniform06.SamplingCoefficientBounds
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
namespace FCAppendix.Affine.Uniform06.SharedGamma

open Set Filter
open scoped Topology BigOperators

def gamma (α q : ℝ) : ℝ := 1+2*α*q/(1-q)

lemma gamma_bounds {α q Q : ℝ} (hα : α ∈ Icc (0:ℝ) 1)
    (hq : q ∈ Icc (0:ℝ) Q) (hQ : Q < 1) :
    1 ≤ gamma α q ∧ gamma α q ≤ 1+2*Q/(1-Q) := by
  have hq1 : q < 1 := hq.2.trans_lt hQ
  have hQ0 : 0 ≤ Q := hq.1.trans hq.2
  have hnum : 2*α*q ≤ 2*Q := by nlinarith [mul_le_mul hα.2 hq.2 hq.1 zero_le_one]
  have hden : 0 < 1-Q := sub_pos.mpr hQ
  have hdenq : 0 < 1-q := sub_pos.mpr hq1
  unfold gamma
  constructor
  · have hh : 0 ≤ 2*α*q/(1-q) := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα.1) hq.1) hdenq.le
    linarith
  · apply add_le_add le_rfl
    exact (div_le_div_of_nonneg_right hnum hdenq.le).trans
      (div_le_div_of_nonneg_left (by positivity) hden (by linarith [hq.2]))

lemma bounded_guard_mul_error {α e : ℕ → ℝ}
    (hα : ∀ n,α n ∈ Icc (0:ℝ) 1) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => α n*e n) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun n => ?_) (by simpa only [norm_zero] using he.norm)
  rw [norm_mul,Real.norm_of_nonneg (hα n).1]
  exact (mul_le_mul_of_nonneg_right (hα n).2 (norm_nonneg _)).trans_eq (one_mul _)

theorem moving_gamma_from_cell_errors
    (zero α q : ℕ → ℝ) (plus minus : ℕ → ℕ → ℝ) (L : ℝ)
    (hα : ∀ n,α n ∈ Icc (0:ℝ) 1)
    {Q B : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (_hB : 0 ≤ B)
    (hq : ∀ᶠ n in atTop,q n ∈ Icc (0:ℝ) Q)
    (hbound : ∀ᶠ n in atTop,∀ k : ℕ,
      ‖plus n k‖ ≤ B*Q^(k+1) ∧ ‖minus n k‖ ≤ B*Q^(k+1))
    (hzero : Tendsto (fun n => zero n-L) atTop (𝓝 0))
    (hplus : ∀ k,Tendsto (fun n => plus n k-α n*L*(q n)^(k+1)) atTop (𝓝 0))
    (hminus : ∀ k,Tendsto (fun n => minus n k-α n*L*(q n)^(k+1)) atTop (𝓝 0)) :
    Tendsto (fun n => zero n+(∑' k,(plus n k+minus n k))-
      L*gamma (α n) (q n)) atTop (𝓝 0) := by
  let F := fun n k => plus n k+minus n k
  let G := fun n k => 2*α n*L*(q n)^(k+1)
  let D := fun k : ℕ => (2*B+2*|L|)*Q^(k+1)
  have hgeo : HasSum (fun k : ℕ => Q^(k+1)) (Q/(1-Q)) := by
    simpa only [pow_succ',div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hQ0 hQ1).mul_left Q
  have hD : Summable D := hgeo.summable.mul_left _
  have herror (k : ℕ) : Tendsto (fun n => F n k-G n k) atTop (𝓝 0) := by
    dsimp only [F,G]
    convert! (hplus k).add (hminus k) using 1
    · funext n
      ring
    · norm_num
  have hdom : ∀ᶠ n in atTop,∀ k,‖F n k-G n k‖ ≤ D k := by
    filter_upwards [hq,hbound] with n hn hbn k
    have hF : ‖F n k‖ ≤ 2*B*Q^(k+1) := by
      exact (norm_add_le _ _).trans (by nlinarith [(hbn k).1,(hbn k).2])
    have hG : ‖G n k‖ ≤ 2*|L| *Q^(k+1) := by
      simp only [G,norm_mul,Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num),
        abs_of_nonneg (hα n).1,abs_of_nonneg (pow_nonneg hn.1 _)]
      calc
        _ ≤ 2*1*|L| *Q^(k+1) := mul_le_mul
          (by nlinarith [mul_le_mul_of_nonneg_right (hα n).2 (abs_nonneg L)])
          (pow_le_pow_left₀ hn.1 hn.2 (k+1))
          (pow_nonneg hn.1 _) (by positivity)
        _ = _ := by ring
    change |F n k| ≤ 2*B*Q^(k+1) at hF
    change |G n k| ≤ 2*|L| *Q^(k+1) at hG
    apply (norm_sub_le _ _).trans
    change |F n k|+|G n k| ≤ D k
    dsimp only [D]
    nlinarith only [hF,hG]
  have hs := tendsto_tsum_of_dominated_convergence hD herror hdom
  have hrewrite : ∀ᶠ n in atTop,
      (∑' k,(F n k-G n k))=(∑' k,(plus n k+minus n k))-2*α n*L*q n/(1-q n) := by
    filter_upwards [hq,hbound] with n hn hbn
    have hFsum : Summable (F n) := by
      apply (hgeo.summable.mul_left (2*B)).of_norm_bounded
      intro k
      exact (norm_add_le _ _).trans (by nlinarith [(hbn k).1,(hbn k).2])
    have hGsum : HasSum (G n) (2*α n*L*q n/(1-q n)) := by
      simpa only [G,pow_succ',div_eq_mul_inv,mul_assoc] using
        (hasSum_geometric_of_lt_one hn.1 (hn.2.trans_lt hQ1)).mul_left (2*α n*L*q n)
    rw [hFsum.tsum_sub hGsum.summable,hGsum.tsum_eq]
  have hsmall : Tendsto (fun n => zero n-L+(∑' k,(F n k-G n k))) atTop (𝓝 0) := by
    simpa only [tsum_zero,add_zero] using hzero.add hs
  apply hsmall.congr'
  filter_upwards [hrewrite] with n hn
  rw [hn]
  unfold gamma
  ring

theorem guarded_cell_error {F α q : ℕ → ℝ} {q₀ L : ℝ} (k : ℕ)
    (hα : ∀ n,α n ∈ Icc (0:ℝ) 1)
    (hF : Tendsto F atTop (𝓝 (L*q₀^k)))
    (hq : Tendsto q atTop (𝓝 q₀)) :
    Tendsto (fun n => α n*F n-α n*L*(q n)^k) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n => F n-L*(q n)^k) atTop (𝓝 0) := by
    simpa only [sub_self] using hF.sub ((hq.pow k).const_mul L)
  convert! bounded_guard_mul_error hα hsmall using 1
  funext n
  ring

end FCAppendix.Affine.Uniform06.SharedGamma
