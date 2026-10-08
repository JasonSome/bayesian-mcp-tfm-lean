import FCAppendix.Probability.QuadraticExpectation
import FCAppendix.PayOnce.KernelPriceSlope
import FCAppendix.PayOnce.KernelLawConvergence

namespace FCAppendix.PayOnce.KernelEntryExpansion
open Set Real CommonList OwnImpact KernelTailEvent KernelLawConvergence

theorem success_linear_error_le (n : ℕ) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    |success n p-(n:ℝ)*p| ≤ ((n:ℝ)*((n:ℝ)-1)/2)*p^2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (BoundedEndpoint.success_le_nat_mul n hp.2))]
  linarith [(SharpEndpoint.success_quadratic_bounds n hp.1 hp.2).1]

theorem exists_receipt_entry_remainder {n : ℕ} (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ Icc (0:ℝ) 1,
      |H n p-1+(((n:ℝ)-1)/2)*p| ≤ K*p^2 := by
  have hH : ContDiff ℝ 2 (H n) := by unfold H; fun_prop
  obtain ⟨_,K,_,hK,_,hrem⟩ := Probability.exists_unit_quadratic_taylor
    (fun _ _ => hH.contDiffAt)
  refine ⟨K,hK,?_⟩
  intro p hp
  have hh := hrem p hp 0 (by norm_num)
  rw [H_zero n (by omega),EndpointVariance.deriv_H_zero (by omega),sub_zero] at hh
  simpa only [neg_div,neg_mul,sub_neg_eq_add] using hh

theorem exists_kernel_entry_expansion {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ Icc (3*t/4) (5*t/4),
      ∀ L ∈ Icc (3*t/4) (5*t/4),
        |kernel n b L-(2/(((n:ℝ)-1)*t))*max (b-L) 0| ≤
          C*((b-L)^2+|L-t| *|b-L|) := by
  obtain ⟨K,hK,hrem⟩ := exists_receipt_entry_remainder hn
  let a : ℝ := ((n:ℝ)-1)/2
  let ell : ℝ := t/2
  let U : ℝ := (n:ℝ)/ell
  let C₁ : ℝ := K/a*U^2
  let C₂ : ℝ := 1/(a*ell*t)
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; linarith
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁,U]; positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  refine ⟨C₁+C₂,add_pos hC₁ hC₂,?_⟩
  intro b hb L hL
  have hbpos : 0 < b := by linarith [hb.1]
  have hLpos : 0 < L := by linarith [hL.1]
  have hbdown : ell ≤ b := by dsimp [ell]; linarith [hb.1]
  have hLdown : ell ≤ L := by dsimp [ell]; linarith [hL.1]
  by_cases hlow : b ≤ L
  · rw [kernel_of_le n hlow,max_eq_right (sub_nonpos.mpr hlow),mul_zero,sub_zero,abs_zero]
    positivity
  have hLb : L < b := lt_of_not_ge hlow
  have hd : 0 < b-L := sub_pos.mpr hLb
  have hbn : b < (n:ℝ)*L := by
    have hh := mul_le_mul_of_nonneg_right hnR hLpos.le
    linarith [hL.1,hb.2]
  have hi := (kernel_interior_iff hn hLpos).mpr ⟨hLb,hbn⟩
  let p := kernel n b L
  have hp : p ∈ Icc (0:ℝ) 1 := ⟨hi.1.le,hi.2.le⟩
  have hreceipt : b*H n p = L :=
    (scalarThreshold_kernel n hn hbpos hLpos).2.2.2.2 hi.1 hi.2
  have hbound : p ≤ U*(b-L) := by
    have hh := kernel_price_difference hn hell hLdown hbdown b
    rw [kernel_of_le n le_rfl,sub_zero,abs_of_nonneg hp.1,
      abs_sub_comm L b,abs_of_pos hd] at hh
    exact hh
  have hbound2 : p^2 ≤ U^2*(b-L)^2 := by
    have hh := pow_le_pow_left₀ hp.1 hbound 2
    simpa only [mul_pow] using hh
  have hfirst : |(H n p-1+a*p)/a| ≤ C₁*(b-L)^2 := by
    rw [abs_div,abs_of_pos ha]
    calc
      |H n p-1+a*p|/a ≤ K*p^2/a := div_le_div_of_nonneg_right (hrem p hp) ha.le
      _ = K/a*p^2 := by ring
      _ ≤ K/a*(U^2*(b-L)^2) := mul_le_mul_of_nonneg_left hbound2 (by positivity)
      _ = _ := by dsimp [C₁]; ring
  have hinvdiff : |1/b-1/t| = |b-t|/(b*t) := by
    have he : 1/b-1/t = -(b-t)/(b*t) := by field_simp; ring
    rw [he,abs_div,abs_neg,abs_of_pos (mul_pos hbpos ht)]
  have hcoeff : 1/(a*(b*t)) ≤ C₂ := by
    apply one_div_le_one_div_of_le (by positivity : 0 < a*ell*t)
    nlinarith [mul_le_mul_of_nonneg_left hbdown (mul_pos ha ht).le]
  have hsecond : |((b-L)/a)*(1/b-1/t)| ≤ C₂*(b-L)*|b-t| := by
    rw [abs_mul,abs_div,abs_of_pos hd,abs_of_pos ha,hinvdiff]
    calc
      (b-L)/a*(|b-t|/(b*t)) = (1/(a*(b*t)))*((b-L)*|b-t|) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ ≤ C₂*((b-L)*|b-t|) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = _ := by ring
  have hidentity : p-(2/(((n:ℝ)-1)*t))*(b-L) =
      (H n p-1+a*p)/a+((b-L)/a)*(1/b-1/t) := by
    have hgap : (b-L)/b = 1-H n p := by
      apply (div_eq_iff hbpos.ne').mpr
      nlinarith [hreceipt]
    have hcoefeq : 2/(((n:ℝ)-1)*t) = 1/(a*t) := by
      dsimp [a]
      field_simp
    rw [hcoefeq]
    calc
      p-1/(a*t)*(b-L) = (p-(b-L)/b/a)+((b-L)/a)*(1/b-1/t) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ = _ := by rw [hgap]; field_simp [ha.ne']; ring
  have hbt : |b-t| ≤ (b-L)+|L-t| := by
    have hh := abs_sub_le b L t
    rwa [abs_of_pos hd] at hh
  have hthird := mul_le_mul_of_nonneg_left hbt (show 0 ≤ C₂*(b-L) by positivity)
  rw [max_eq_left hd.le,show kernel n b L = p from rfl,hidentity]
  calc
    |(H n p-1+a*p)/a+((b-L)/a)*(1/b-1/t)| ≤
        C₁*(b-L)^2+C₂*(b-L)*|b-t| :=
      (abs_add_le _ _).trans (add_le_add hfirst hsecond)
    _ ≤ C₁*(b-L)^2+C₂*(b-L)*((b-L)+|L-t|) := add_le_add_right hthird _
    _ ≤ (C₁+C₂)*((b-L)^2+|L-t| *|b-L|) := by
      rw [abs_of_pos hd]
      nlinarith [mul_nonneg hC₁.le (mul_nonneg (abs_nonneg (L-t)) hd.le)]

end FCAppendix.PayOnce.KernelEntryExpansion
