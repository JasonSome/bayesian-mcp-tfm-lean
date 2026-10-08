import FCAppendix.PayOnce.ServedIdentification

namespace FCAppendix.PayOnce.Limit
open Set Filter Topology CommonList
open OwnImpact

noncomputable def bidStar (n : ℕ) (L w : ℝ) : ℝ :=
  if w ≤ L then max w 0 else L/H n (pStar n L w)

theorem bidStar_of_le {n : ℕ} {L w : ℝ} (hw : w ≤ L) :
    bidStar n L w = max w 0 := if_pos hw

theorem bidStar_of_lt {n : ℕ} {L w : ℝ} (hw : L < w) :
    bidStar n L w = L/H n (pStar n L w) := if_neg (not_le.mpr hw)

theorem continuous_pStar {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) :
    Continuous (pStar n L) := ManyProposers.continuous_pStar hn hL

theorem continuous_bidStar {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) :
    Continuous (bidStar n L) := by
  have hH : ∀ w, H n (pStar n L w) ≠ 0 := fun w =>
    (H_pos n (by omega) _ pStar_nonneg (pStar_le_one hL.le)).ne'
  apply Continuous.if_le (continuous_id.max continuous_const)
    (continuous_const.div ((continuous_H n).comp (continuous_pStar hn hL)) hH)
    continuous_id continuous_const
  intro w hw
  change w = L at hw
  subst w
  change max L 0 = L/H n (pStar n L L)
  rw [pStar_eq_zero_of_le hn hL.le le_rfl,H_zero n (by omega),div_one,max_eq_left hL.le]

theorem bidStar_nonneg {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (w : ℝ) :
    0 ≤ bidStar n L w := by
  unfold bidStar
  split_ifs
  · exact le_max_right _ _
  · exact (div_pos hL (H_pos n (by omega) _ pStar_nonneg (pStar_le_one hL.le))).le

theorem bidStar_le_mul_price {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (w : ℝ) :
    bidStar n L w ≤ (n:ℝ)*L := by
  have hnR : (1:ℝ) ≤ n := Nat.one_le_cast.mpr (by omega)
  have hLn : L ≤ (n:ℝ)*L := le_mul_of_one_le_left hL.le hnR
  unfold bidStar
  split_ifs with hw
  · exact (max_le hw hL.le).trans hLn
  · have hH := H_pos n (by omega) (pStar n L w) pStar_nonneg (pStar_le_one hL.le)
    have hh := (H_bounds n (by omega) (pStar n L w) pStar_nonneg (pStar_le_one hL.le)).1
    have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hmul := (div_le_iff₀ hn0).mp hh
    apply (div_le_iff₀ hH).mpr
    nlinarith

theorem pStar_equation {n : ℕ} (hn : 2 ≤ n) {L w : ℝ} (hL : 0 < L) (hw : L < w) :
    w*(1-pStar n L w)^(n-1) = L := by
  have hw0 := hL.trans hw
  have he : 1/((n:ℝ)-1) = (((n-1:ℕ):ℝ))⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one,one_div]
  rw [pStar_of_lt hn hL.le hw,sub_sub_cancel,he,
    Real.rpow_inv_natCast_pow (div_pos hL hw0).le (by omega)]
  exact mul_div_cancel₀ _ hw0.ne'

theorem bidStar_le_net_value {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (w : ℝ) :
    bidStar n L w ≤ max w 0 := by
  by_cases hw : w ≤ L
  · rw [bidStar_of_le hw]
  have hLw := lt_of_not_ge hw
  have hw0 := hL.trans hLw
  have hp0 := (pStar_pos_iff hn hL.le).mpr hLw
  have hp1 := pStar_lt_one hn hL hLw
  have hH := H_pos n (by omega) (pStar n L w) hp0.le hp1.le
  have hsl := Hslope_pos hn ⟨hp0.le,hp1.le⟩
  have hid := H_sub_mul_Hslope (show 0 < n by omega) (pStar n L w)
  have heq := pStar_equation hn hL hLw
  rw [bidStar_of_lt hLw,max_eq_left hw0.le]
  apply (div_le_iff₀ hH).mpr
  have hh : 0 ≤ w*pStar n L w*Hslope n (pStar n L w) := by positivity
  nlinarith

theorem kernel_bidStar {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (w : ℝ) :
    kernel n (bidStar n L w) L = pStar n L w := by
  by_cases hw : w ≤ L
  · rw [bidStar_of_le hw,kernel_of_le n (max_le hw hL.le),pStar_eq_zero_of_le hn hL.le hw]
  have hLw := lt_of_not_ge hw
  rw [bidStar_of_lt hLw]
  have hp : pStar n L w ∈ Icc (0:ℝ) 1 := ⟨pStar_nonneg,pStar_le_one hL.le⟩
  have hH := H_pos n (by omega) _ hp.1 hp.2
  have hh := KernelTailEvent.kernel_at_score hn (div_pos hL hH) hp.1 hp.2
  rw [div_mul_cancel₀ _ hH.ne'] at hh
  exact hh

end FCAppendix.PayOnce.Limit
