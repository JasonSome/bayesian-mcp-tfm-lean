import FCAppendix.PayOnce.OwnImpact
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

namespace FCAppendix.PayOnce.OwnImpact

open Filter Topology Set CommonList
open scoped BigOperators

theorem hasStrictDerivAt_H (n : ℕ) (p : ℝ) :
    HasStrictDerivAt (H n) (-Hslope n p) p := by
  have hc : ContDiff ℝ 1 (H n) := by unfold H; fun_prop
  exact hc.contDiffAt.hasStrictDerivAt' (hasDerivAt_H n p) (by norm_num)

theorem hasStrictDerivAt_scalarDemand {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hb : 0 < b) (hi : scalarDemand n hn b hb L ∈ Ioo (0 : ℝ) 1) :
    HasStrictDerivAt (scalarDemand n hn b hb)
      (-sensitivity n b (scalarDemand n hn b hb L)) L := by
  let p := scalarDemand n hn b hb L
  have hp : p ∈ Icc (0 : ℝ) 1 := ⟨hi.1.le, hi.2.le⟩
  have hg := (scalarDemand_continuous n hn b hb).continuousAt (x := L)
  have hfg : ∀ᶠ y in 𝓝 L, b * H n (scalarDemand n hn b hb y) = y := by
    filter_upwards [hg.eventually (isOpen_Ioo.mem_nhds hi)] with y hy
    exact (scalarDemand_spec n hn b hb y).2.2.2.2 hy.1 hy.2
  have hf := (hasStrictDerivAt_H n p).const_mul b
  have hf0 : b * (-Hslope n p) ≠ 0 := mul_ne_zero hb.ne' (neg_ne_zero.mpr (Hslope_pos hn hp).ne')
  have hh := hf.of_local_left_inverse hg hf0 hfg
  convert hh using 1 <;> first | rfl | (simp only [sensitivity, mul_neg, inv_neg, one_div, p])

theorem kernel_eq_scalarDemand {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hb : 0 < b) (hL : 0 < L) : kernel n b L = scalarDemand n hn b hb L :=
  (eq_kernel_of_scalarThreshold n hn hb hL (scalarDemand_spec n hn b hb L)).symm

theorem hasStrictDerivAt_kernel_price_interior {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hi : kernel n b L ∈ Ioo (0 : ℝ) 1) :
    HasStrictDerivAt (kernel n b) (-sensitivity n b (kernel n b L)) L := by
  have he := kernel_eq_scalarDemand hn hb hL
  have hh := hasStrictDerivAt_scalarDemand hn hb (by rwa [← he])
  rw [← he] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hL] with y hy
  exact (kernel_eq_scalarDemand hn hb hy).symm

theorem hasStrictDerivAt_kernel_price_zero {n : ℕ} {b L : ℝ} (h : b < L) :
    HasStrictDerivAt (kernel n b) 0 L := by
  apply (hasStrictDerivAt_const L (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds h] with y hy
  exact (kernel_of_le n hy.le).symm

theorem hasStrictDerivAt_kernel_price_one {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hL : 0 < L) (h : (n : ℝ) * L < b) : HasStrictDerivAt (kernel n b) 0 L := by
  apply (hasStrictDerivAt_const L (1 : ℝ)).congr_of_eventuallyEq
  have hc : ContinuousAt (fun x : ℝ => (n : ℝ) * x) L := continuousAt_const.mul continuousAt_id
  filter_upwards [eventually_gt_nhds hL, hc.eventually_lt_const h] with y hy hyb
  exact (kernel_of_ge n hn hy hyb.le).symm

theorem hasStrictDerivAt_kernel_price {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hzero : b ≠ L) (hone : b ≠ (n : ℝ) * L) :
    HasStrictDerivAt (kernel n b)
      (if 0 < kernel n b L ∧ kernel n b L < 1 then -sensitivity n b (kernel n b L) else 0) L := by
  classical
  by_cases hbl : b < L
  · have hk := kernel_of_le n hbl.le
    rw [hk]
    simp only [lt_self_iff_false, false_and, ↓reduceIte]
    exact hasStrictDerivAt_kernel_price_zero hbl
  · have hlb : L < b := lt_of_le_of_ne (le_of_not_gt hbl) (Ne.symm hzero)
    by_cases hnb : (n : ℝ) * L < b
    · have hk := kernel_of_ge n hn hL hnb.le
      rw [hk]
      simp only [lt_self_iff_false, and_false, ↓reduceIte]
      exact hasStrictDerivAt_kernel_price_one hn hL hnb
    · have hbn : b < (n : ℝ) * L := lt_of_le_of_ne (le_of_not_gt hnb) hone
      have hp0 := kernel_nonneg n hn hb hL
      have hp1 := kernel_le_one n hn hb hL
      have hne0 : kernel n b L ≠ 0 := by
        intro hz
        exact (not_le_of_gt hlb) ((kernel_eq_zero_iff n hn hb hL).mp hz)
      have hne1 : kernel n b L ≠ 1 := by
        intro hz
        have he := (le_div_iff₀ (Nat.cast_pos.mpr (show 0 < n by omega))).mp
          ((kernel_eq_one_iff n hn hb hL).mp hz)
        exact (not_le_of_gt hbn) (by simpa only [mul_comm] using he)
      have hi : kernel n b L ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hp0 hne0.symm, lt_of_le_of_ne hp1 hne1⟩
      rw [if_pos (show 0 < kernel n b L ∧ kernel n b L < 1 from hi)]
      exact hasStrictDerivAt_kernel_price_interior hn hb hL hi

end FCAppendix.PayOnce.OwnImpact
