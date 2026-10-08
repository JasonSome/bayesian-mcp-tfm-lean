import FCAppendix.PayOnce.EntryHazard

namespace FCAppendix.PayOnce.EntryDerivativeLower
open Real

theorem combine_central_rare_hazard {M N : ℕ} {d H A B q : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hMN : M ≤ 2*N)
    (hd : 0 ≤ d) (hA : 0 < A) (hB : 0 < B)
    (hlarge : 2*H ≤ sqrt (M:ℝ))
    (hcentral : d ≤ 1/sqrt (M:ℝ) → q ≤ A/sqrt (M:ℝ))
    (hrare : H/(N:ℝ) ≤ d → q ≤ B/((N:ℝ)*d)) :
    q ≤ max (2*A) (4*B)/(sqrt (M:ℝ)+(M:ℝ)*d) := by
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hs := sqrt_pos.mpr hMR
  have hsq := sq_sqrt hMR.le
  have hMNr : (M:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hMN
  have hden : 0 < sqrt (M:ℝ)+(M:ℝ)*d := add_pos_of_pos_of_nonneg hs (mul_nonneg hMR.le hd)
  by_cases hc : d ≤ 1/sqrt (M:ℝ)
  · have hdroot := (le_div_iff₀ hs).mp hc
    have hmd : (M:ℝ)*d ≤ sqrt (M:ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hdroot hs.le]
    apply (hcentral hc).trans
    apply (div_le_div_iff₀ hs hden).mpr
    have hcoef := mul_le_mul_of_nonneg_right (le_max_left (2*A) (4*B)) hs.le
    nlinarith [mul_nonneg hA.le (show 0 ≤ sqrt (M:ℝ)-(M:ℝ)*d by linarith)]
  · have hdgt : 1/sqrt (M:ℝ) < d := lt_of_not_ge hc
    have hdp : 0 < d := (one_div_pos.mpr hs).trans hdgt
    have hHdiv : H/(N:ℝ) ≤ 1/sqrt (M:ℝ) := by
      apply (div_le_div_iff₀ hNR hs).mpr
      nlinarith [mul_le_mul_of_nonneg_right hlarge hs.le]
    have hrare' := hrare (hHdiv.trans hdgt.le)
    have hds := (div_lt_iff₀ hs).mp hdgt
    have hsm : sqrt (M:ℝ) ≤ (M:ℝ)*d := by
      nlinarith [mul_le_mul_of_nonneg_left hds.le hs.le]
    apply hrare'.trans
    apply (div_le_div_iff₀ (mul_pos hNR hdp) hden).mpr
    have hdenupper : sqrt (M:ℝ)+(M:ℝ)*d ≤ 4*(N:ℝ)*d := by
      have hh := mul_le_mul_of_nonneg_right hMNr hd
      linarith
    have hcoef := mul_le_mul_of_nonneg_right (le_max_right (2*A) (4*B)) (mul_nonneg hNR.le hd)
    nlinarith [mul_le_mul_of_nonneg_left hdenupper hB.le]

end FCAppendix.PayOnce.EntryDerivativeLower
