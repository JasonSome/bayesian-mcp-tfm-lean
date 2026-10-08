import FCAppendix.PayOnce.OwnImpact
import FCAppendix.PayOnce.DummyKernel
import Mathlib.Analysis.Calculus.MeanValue

namespace FCAppendix.PayOnce.PriceInteriorBounds
open Set CommonList OwnImpact KernelTailEvent
open scoped BigOperators

theorem H_abs_sub_le {n : ℕ} (hn : 2 ≤ n) {p q : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    |H n p-H n q| ≤ (n:ℝ)*|p-q| := by
  have hd (x : ℝ) (_hx : x ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (H n) (-Hslope n x) (Icc (0:ℝ) 1) x :=
    (hasDerivAt_H n x).hasDerivWithinAt
  have hb (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖-Hslope n x‖ ≤ (n:ℝ) := by
    rw [norm_neg,Real.norm_eq_abs,abs_of_pos (Hslope_pos hn hx)]
    exact (Hslope_bounds hn hx).2
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc (0:ℝ) 1) hq hp

theorem price_gap_le_kernel_gap {n : ℕ} (hn : 2 ≤ n) {b L T : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hT : 0 < T)
    (hpL : kernel n b L ∈ Ioo (0:ℝ) 1) (hpT : kernel n b T ∈ Ioo (0:ℝ) 1) :
    |L-T| ≤ (n:ℝ)*b*|kernel n b L-kernel n b T| := by
  have heL := (scalarThreshold_kernel n hn hb hL).2.2.2.2 hpL.1 hpL.2
  have heT := (scalarThreshold_kernel n hn hb hT).2.2.2.2 hpT.1 hpT.2
  have hdiff : L-T = b*(H n (kernel n b L)-H n (kernel n b T)) := by
    calc
      L-T = b*H n (kernel n b L)-b*H n (kernel n b T) := by linarith only [heL,heT]
      _ = _ := by ring
  calc
    |L-T| = b*|H n (kernel n b L)-H n (kernel n b T)| := by
      rw [hdiff,abs_mul,abs_of_pos hb]
    _ ≤ b*((n:ℝ)*|kernel n b L-kernel n b T|) :=
      mul_le_mul_of_nonneg_left (H_abs_sub_le hn ⟨hpL.1.le,hpL.2.le⟩ ⟨hpT.1.le,hpT.2.le⟩) hb.le
    _ = _ := by ring

theorem kernel_interior_on_window {n : ℕ} (hn : 2 ≤ n)
    {ℓ u a z b L : ℝ} (hℓ : 0 < ℓ) (hL : L ∈ Icc ℓ u)
    (ha : u < a) (hz : z < (n:ℝ)*ℓ) (hb : b ∈ Ioo a z) :
    kernel n b L ∈ Ioo (0:ℝ) 1 := by
  have hLpos : 0 < L := hℓ.trans_le hL.1
  have hLb : L < b := hL.2.trans_lt (ha.trans hb.1)
  have hbpos : 0 < b := hLpos.trans hLb
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hbn : b < (n:ℝ)*L := hb.2.trans (hz.trans_le (mul_le_mul_of_nonneg_left hL.1 hnR.le))
  have hp := kernel_bounds hn hLpos b
  constructor
  · apply lt_of_le_of_ne hp.1
    intro he
    exact hLb.not_ge ((kernel_eq_zero_iff n hn hbpos hLpos).mp he.symm)
  · apply lt_of_le_of_ne hp.2
    intro he
    have hh := (le_div_iff₀ hnR).mp ((kernel_eq_one_iff n hn hbpos hLpos).mp he)
    nlinarith

theorem interior_count_mul_price_gap_le_demand_gap_of_le
    {ι : Type*} [Fintype ι] {n : ℕ} (hn : 2 ≤ n) (r : ι → ℝ)
    {ℓ u a z L T : ℝ} (hℓ : 0 < ℓ)
    (hL : L ∈ Icc ℓ u) (hT : T ∈ Icc ℓ u) (hLT : L ≤ T)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ)
    (J : Finset ι) (hJ : ∀ j ∈ J, r j ∈ Ioo a z) :
    (J.card:ℝ)*(T-L) ≤ (n:ℝ)*z*((∑ j, kernel n (r j) L)-(∑ j, kernel n (r j) T)) := by
  have hLpos := hℓ.trans_le hL.1
  have hTpos := hℓ.trans_le hT.1
  have hzpos : 0 < z := ((hLpos.trans_le hL.2).trans ha).trans haz
  have hmono j : kernel n (r j) T ≤ kernel n (r j) L :=
    kernel_antitone_price hn hLpos hTpos hLT
  have hone j (hj : j ∈ J) : T-L ≤ (n:ℝ)*z*(kernel n (r j) L-kernel n (r j) T) := by
    have hrj := hJ j hj
    have hb : 0 < r j := (hLpos.trans_le hL.2).trans (ha.trans hrj.1)
    have hh := price_gap_le_kernel_gap hn hb hLpos hTpos
      (kernel_interior_on_window hn hℓ hL ha hz hrj)
      (kernel_interior_on_window hn hℓ hT ha hz hrj)
    rw [abs_of_nonpos (sub_nonpos.mpr hLT),neg_sub,
      abs_of_nonneg (sub_nonneg.mpr (hmono j))] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrj.2.le (Nat.cast_nonneg n)) (sub_nonneg.mpr (hmono j)))
  have hsub : (∑ j ∈ J, (kernel n (r j) L-kernel n (r j) T)) ≤
      ∑ j, (kernel n (r j) L-kernel n (r j) T) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      (fun j _ _ => sub_nonneg.mpr (hmono j))
  calc
    (J.card:ℝ)*(T-L) = ∑ _j ∈ J, (T-L) := by simp [mul_sub]
    _ ≤ ∑ j ∈ J, (n:ℝ)*z*(kernel n (r j) L-kernel n (r j) T) :=
      Finset.sum_le_sum hone
    _ = (n:ℝ)*z*(∑ j ∈ J, (kernel n (r j) L-kernel n (r j) T)) := by rw [Finset.mul_sum]
    _ ≤ (n:ℝ)*z*(∑ j, (kernel n (r j) L-kernel n (r j) T)) :=
      mul_le_mul_of_nonneg_left hsub (mul_nonneg (Nat.cast_nonneg n) hzpos.le)
    _ = _ := by rw [Finset.sum_sub_distrib]

theorem interior_count_mul_price_gap_le_demand_gap
    {ι : Type*} [Fintype ι] {n : ℕ} (hn : 2 ≤ n) (r : ι → ℝ)
    {ℓ u a z L T : ℝ} (hℓ : 0 < ℓ)
    (hL : L ∈ Icc ℓ u) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ)
    (J : Finset ι) (hJ : ∀ j ∈ J, r j ∈ Ioo a z) :
    (J.card:ℝ)*|L-T| ≤ (n:ℝ)*z*|(∑ j, kernel n (r j) L)-(∑ j, kernel n (r j) T)| := by
  have hLpos := hℓ.trans_le hL.1
  have hTpos := hℓ.trans_le hT.1
  rcases le_total L T with hLT | hTL
  · have hsum : (∑ j, kernel n (r j) T) ≤ ∑ j, kernel n (r j) L :=
      Finset.sum_le_sum (fun j _ => kernel_antitone_price hn hLpos hTpos hLT)
    rw [abs_of_nonpos (sub_nonpos.mpr hLT),neg_sub,abs_of_nonneg (sub_nonneg.mpr hsum)]
    exact interior_count_mul_price_gap_le_demand_gap_of_le hn r hℓ hL hT hLT ha haz hz J hJ
  · have hsum : (∑ j, kernel n (r j) L) ≤ ∑ j, kernel n (r j) T :=
      Finset.sum_le_sum (fun j _ => kernel_antitone_price hn hTpos hLpos hTL)
    rw [abs_of_nonneg (sub_nonneg.mpr hTL),abs_of_nonpos (sub_nonpos.mpr hsum),neg_sub]
    exact interior_count_mul_price_gap_le_demand_gap_of_le hn r hℓ hT hL hTL ha haz hz J hJ

theorem price_gap_le_normalized_demand_gap
    {ι : Type*} [Fintype ι] {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M) (r : ι → ℝ)
    {ℓ u a z L T q : ℝ} (hℓ : 0 < ℓ)
    (hL : L ∈ Icc ℓ u) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ)
    (J : Finset ι) (hJ : ∀ j ∈ J, r j ∈ Ioo a z)
    (hq : 0 < q) (hcount : q*(M:ℝ) ≤ J.card) :
    |L-T| ≤ ((n:ℝ)*z/q)*|(∑ j, kernel n (r j) L)/(M:ℝ)-(∑ j, kernel n (r j) T)/(M:ℝ)| := by
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hs := interior_count_mul_price_gap_le_demand_gap hn r hℓ hL hT ha haz hz J hJ
  have hbound := (mul_le_mul_of_nonneg_right hcount (abs_nonneg (L-T))).trans hs
  rw [← sub_div,abs_div,abs_of_pos hMR]
  have he : ((n:ℝ)*z/q)*
      (|(∑ j, kernel n (r j) L)-(∑ j, kernel n (r j) T)|/(M:ℝ)) =
      ((n:ℝ)*z*|(∑ j, kernel n (r j) L)-(∑ j, kernel n (r j) T)|)/(q*M) := by
    field_simp
  rw [he]
  exact (le_div_iff₀ (mul_pos hq hMR)).mpr (by simpa only [mul_comm] using hbound)

theorem normalized_demand_gap_le_capacity_error
    {ι : Type*} [Fintype ι] {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M) (r : ι → ℝ)
    {b L T c : ℝ} (hL : 0 < L)
    (hcap : kernel n b L+∑ j, kernel n (r j) L = c) :
    |(∑ j, kernel n (r j) L)/(M:ℝ)-(∑ j, kernel n (r j) T)/(M:ℝ)| ≤
      |(∑ j, kernel n (r j) T)/(M:ℝ)-c/(M:ℝ)|+1/(M:ℝ) := by
  have hp := kernel_bounds hn hL b
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hraw : |(∑ j, kernel n (r j) L)-(∑ j, kernel n (r j) T)| ≤
      |(∑ j, kernel n (r j) T)-c|+1 := by
    calc
      _ = |(c-∑ j, kernel n (r j) T)-kernel n b L| := congrArg abs (by linarith only [hcap])
      _ ≤ |c-∑ j, kernel n (r j) T|+|kernel n b L| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_sub_comm c,abs_of_nonneg hp.1]
        exact add_le_add le_rfl hp.2
  have hnorm (x y : ℝ) : |x/(M:ℝ)-y/(M:ℝ)| = |x-y|/(M:ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hMR]
  rw [hnorm,hnorm,← add_div]
  exact div_le_div_of_nonneg_right hraw hMR.le

theorem price_gap_le_capacity_error
    {ι : Type*} [Fintype ι] {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M) (r : ι → ℝ)
    {ℓ u a z b L T q c : ℝ} (hℓ : 0 < ℓ)
    (hL : L ∈ Icc ℓ u) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ)
    (J : Finset ι) (hJ : ∀ j ∈ J, r j ∈ Ioo a z)
    (hq : 0 < q) (hcount : q*(M:ℝ) ≤ J.card)
    (hcap : kernel n b L+∑ j, kernel n (r j) L = c) :
    |L-T| ≤ ((n:ℝ)*z/q)*
      (|(∑ j, kernel n (r j) T)/(M:ℝ)-c/(M:ℝ)|+1/(M:ℝ)) := by
  have hzpos : 0 < z := (((hℓ.trans_le hL.1).trans_le hL.2).trans ha).trans haz
  exact (price_gap_le_normalized_demand_gap hn hM r hℓ hL hT ha haz hz J hJ hq hcount).trans
    (mul_le_mul_of_nonneg_left (normalized_demand_gap_le_capacity_error hn hM r
      (hℓ.trans_le hL.1) hcap) (by positivity))

theorem focal_price_gap_le
    {ι : Type*} [Fintype ι] {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M) (r : ι → ℝ)
    {ℓ u a z b d L T q c : ℝ} (hℓ : 0 < ℓ)
    (hL : L ∈ Icc ℓ u) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ)
    (J : Finset ι) (hJ : ∀ j ∈ J, r j ∈ Ioo a z)
    (hq : 0 < q) (hcount : q*(M:ℝ) ≤ J.card)
    (hcapL : kernel n b L+∑ j, kernel n (r j) L = c)
    (hcapT : kernel n d T+∑ j, kernel n (r j) T = c) :
    |L-T| ≤ (n:ℝ)*z/(q*M) := by
  have hLpos := hℓ.trans_le hL.1
  have hTpos := hℓ.trans_le hT.1
  have hzpos : 0 < z := ((hLpos.trans_le hL.2).trans ha).trans haz
  have hpL := kernel_bounds hn hLpos b
  have hpT := kernel_bounds hn hTpos d
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hraw : |(∑ j, kernel n (r j) L)-(∑ j, kernel n (r j) T)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hpL.2,hpT.1],by linarith [hpL.1,hpT.2]⟩
  have hnorm : |(∑ j, kernel n (r j) L)/(M:ℝ)-(∑ j, kernel n (r j) T)/(M:ℝ)| ≤ 1/(M:ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hMR]
    exact div_le_div_of_nonneg_right hraw hMR.le
  calc
    |L-T| ≤ ((n:ℝ)*z/q)*
        |(∑ j, kernel n (r j) L)/(M:ℝ)-(∑ j, kernel n (r j) T)/(M:ℝ)| :=
      price_gap_le_normalized_demand_gap hn hM r hℓ hL hT ha haz hz J hJ hq hcount
    _ ≤ ((n:ℝ)*z/q)*(1/(M:ℝ)) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by field_simp

theorem dummy_focal_price_gap_le
    {ι : Type*} [Fintype ι] {n M c : ℕ} (hn : 2 ≤ n) (hM : 0 < M) (r : ι → ℝ)
    {ℓ u a z b d L T q : ℝ} (hℓ : 0 < ℓ)
    (hL : L ∈ Icc ℓ u) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ)
    (J : Finset ι) (hJ : ∀ j ∈ J, r j ∈ Ioo a z)
    (hq : 0 < q) (hcount : q*(M:ℝ) ≤ J.card)
    (hcapL : kernel n b L+(∑ j : DummyKernel.Active r, kernel n (r j.val) L) =
      min c (Fintype.card (DummyKernel.Active r)+1))
    (hcapT : kernel n d T+(∑ j : DummyKernel.Active r, kernel n (r j.val) T) =
      min c (Fintype.card (DummyKernel.Active r)+1)) :
    |L-T| ≤ (n:ℝ)*z/(q*M) := by
  rw [DummyKernel.sum_active r (hℓ.trans_le hL.1)] at hcapL
  rw [DummyKernel.sum_active r (hℓ.trans_le hT.1)] at hcapT
  exact focal_price_gap_le hn hM r hℓ hL hT ha haz hz J hJ hq hcount hcapL hcapT

end FCAppendix.PayOnce.PriceInteriorBounds
