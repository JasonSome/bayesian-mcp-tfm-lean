import FCAppendix.PayOnce.FiniteFOCResponse

namespace FCAppendix.PayOnce.NearEntryFOCResponse
open Set Real CommonList OwnImpact RareSuccessSlope ResponseFactor

theorem mul_pow_sub_le_abs_pow_sub {k : ℕ} (hk : 0 < k) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x-y| *x^(k-1) ≤ |x^k-y^k| := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [Nat.succ_sub_one]
  by_cases hxy : y ≤ x
  · have hpow := pow_le_pow_left₀ hy hxy j
    have hprod := mul_nonneg hy (sub_nonneg.mpr hpow)
    rw [abs_of_nonneg (sub_nonneg.mpr hxy),
      abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hy hxy (j+1)))]
    have hid : x^(j+1)-y^(j+1) = (x-y)*x^j+y*(x^j-y^j) := by
      rw [pow_succ,pow_succ]
      ring
    rw [hid]
    linarith
  · have hyx : x ≤ y := (lt_of_not_ge hxy).le
    have hpow := pow_le_pow_left₀ hx hyx j
    have hprod := mul_nonneg hy (sub_nonneg.mpr hpow)
    rw [abs_of_nonpos (sub_nonpos.mpr hyx),
      abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ hx hyx (j+1)))]
    have hid : y^(j+1)-x^(j+1) = (y-x)*x^j+y*(y^j-x^j) := by
      rw [pow_succ,pow_succ]
      ring
    linarith [hid]

theorem root_difference_le {k : ℕ} (hk : 0 < k) {x y : ℝ}
    (hx : (1:ℝ)/2 ≤ x) (hy : 0 ≤ y) :
    |x-y| ≤ (2:ℝ)^(k-1)*|x^k-y^k| := by
  have hpow : ((1:ℝ)/2)^(k-1) ≤ x^(k-1) :=
    pow_le_pow_left₀ (by norm_num) hx _
  have hh := (mul_le_mul_of_nonneg_left hpow (abs_nonneg (x-y))).trans
    (mul_pow_sub_le_abs_pow_sub hk (by linarith) hy)
  have hrec : (2:ℝ)^(k-1)*((1:ℝ)/2)^(k-1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    |x-y| = |x-y| *((2:ℝ)^(k-1)*((1:ℝ)/2)^(k-1)) := by rw [hrec,mul_one]
    _ = (2:ℝ)^(k-1)*(|x-y| *((1:ℝ)/2)^(k-1)) := by ring
    _ ≤ (2:ℝ)^(k-1)*|x^k-y^k| := mul_le_mul_of_nonneg_left hh (by positivity)

theorem pStar_of_le {n : ℕ} (hn : 2 ≤ n) {L w : ℝ}
    (hL : 0 < L) (hLw : L ≤ w) :
    Limit.pStar n L w = 1-(L/w)^(1/((n:ℝ)-1)) := by
  have hw := hL.trans_le hLw
  rw [Limit.pStar_of_pos hw]
  apply max_eq_right
  have hh := rpow_le_one (div_nonneg hL.le hw.le)
    ((div_le_one hw).mpr hLw) (Limit.exponent_pos hn).le
  linarith

theorem residual_identity {n : ℕ} (hn : 2 ≤ n) {L b w p : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hreceipt : b*H n p = L) :
    b*success n p-(w-b)*phi n p = J n p*(L-w*(1-p)^(n-1)) := by
  have hsum := success_add_phi_eq_J_mul_H hn hp
  rw [phi_eq_J_mul_pow] at hsum ⊢
  linear_combination b*hsum+J n p*hreceipt

theorem response_error_of_residual {n : ℕ} (hn : 2 ≤ n) {L b w p e : ℝ}
    (hL : 0 < L) (hLw : L ≤ w) (hp : p ∈ Icc (0:ℝ) (1/2))
    (hreceipt : b*H n p = L)
    (herr : |b*success n p-(w-b)*phi n p| ≤ e) :
    |p-Limit.pStar n L w| ≤ ((n:ℝ)*2^(n-2))*e/L := by
  let z := (L/w)^(1/((n:ℝ)-1))
  have hw : 0 < w := hL.trans_le hLw
  have hpunit : p ∈ Icc (0:ℝ) 1 := ⟨hp.1,by linarith [hp.2]⟩
  have hz : 0 ≤ z := rpow_nonneg (div_nonneg hL.le hw.le) _
  have hzpow : z^(n-1) = L/w := by
    dsimp only [z]
    have hexp : 1/((n:ℝ)-1) = (((n-1:ℕ):ℝ))⁻¹ := by
      rw [Nat.cast_sub (by omega),Nat.cast_one,one_div]
    rw [hexp,rpow_inv_natCast_pow (div_nonneg hL.le hw.le) (by omega)]
  have hres : J n p*|L-w*(1-p)^(n-1)| ≤ e := by
    rw [residual_identity hn hpunit hreceipt,abs_mul,abs_of_pos (J_pos hn hpunit)] at herr
    exact herr
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hJ := (J_bounds hn hpunit).1
  have hraw : |L-w*(1-p)^(n-1)| ≤ (n:ℝ)*e := by
    have hh := (mul_le_mul_of_nonneg_right hJ (abs_nonneg (L-w*(1-p)^(n-1)))).trans hres
    have hh' := mul_le_mul_of_nonneg_left hh hnR.le
    field_simp at hh'
    exact hh'
  have hroot := root_difference_le (k := n-1) (by omega)
    (x := 1-p) (y := z) (by linarith [hp.2]) hz
  have hnorm : w*|(1-p)^(n-1)-z^(n-1)| = |L-w*(1-p)^(n-1)| := by
    rw [hzpow]
    calc
      w*|(1-p)^(n-1)-L/w| = |w*((1-p)^(n-1)-L/w)| := by
        rw [abs_mul,abs_of_pos hw]
      _ = |L-w*(1-p)^(n-1)| := by
        rw [mul_sub,mul_div_cancel₀ L hw.ne',abs_sub_comm]
  have hbound : L*|(1-p)-z| ≤ ((n:ℝ)*2^(n-2))*e := by
    calc
      L*|(1-p)-z| ≤ w*|(1-p)-z| := mul_le_mul_of_nonneg_right hLw (abs_nonneg _)
      _ ≤ w*(2^((n-1)-1)*|(1-p)^(n-1)-z^(n-1)|) :=
        mul_le_mul_of_nonneg_left hroot hw.le
      _ = 2^(n-2)*|L-w*(1-p)^(n-1)| := by
        rw [show (n-1)-1 = n-2 by omega,← hnorm]
        ring
      _ ≤ 2^(n-2)*((n:ℝ)*e) := mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = ((n:ℝ)*2^(n-2))*e := by ring
  rw [pStar_of_le hn hL hLw]
  apply (le_div_iff₀ hL).mpr
  have habs : |p-(1-z)| = |(1-p)-z| := by
    rw [show p-(1-z) = -((1-p)-z) by ring,abs_neg]
  change |p-(1-z)| *L ≤ _
  rw [habs,mul_comm]
  exact hbound

theorem kernel_receipt_of_ge {n : ℕ} (hn : 2 ≤ n) {L b : ℝ}
    (hL : 0 < L) (hLb : L ≤ b) (hp : kernel n b L < 1) :
    b*H n (kernel n b L) = L := by
  have hb := hL.trans_le hLb
  have hp0 := (KernelTailEvent.kernel_bounds hn hL b).1
  by_cases hz : kernel n b L = 0
  · have hbL := (kernel_eq_zero_iff n hn hb hL).mp hz
    have he : b = L := le_antisymm hbL hLb
    rw [hz,H_zero n (by omega),mul_one,he]
  · exact (scalarThreshold_kernel n hn hb hL).2.2.2.2 (lt_of_le_of_ne hp0 (Ne.symm hz)) hp

theorem kernel_response_error_of_residual {n : ℕ} (hn : 2 ≤ n) {L b w e : ℝ}
    (hL : 0 < L) (hLb : L ≤ b) (hbw : b ≤ w) (hp : kernel n b L ≤ 1/2)
    (herr : |b*success n (kernel n b L)-(w-b)*phi n (kernel n b L)| ≤ e) :
    |kernel n b L-Limit.pStar n L w| ≤ ((n:ℝ)*2^(n-2))*e/L := by
  exact response_error_of_residual hn hL (hLb.trans hbw)
    ⟨(KernelTailEvent.kernel_bounds hn hL b).1,hp⟩
    (kernel_receipt_of_ge hn hL hLb (by linarith)) herr

end FCAppendix.PayOnce.NearEntryFOCResponse
