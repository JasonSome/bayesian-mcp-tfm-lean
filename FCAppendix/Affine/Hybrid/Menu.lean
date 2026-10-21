import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set

def exposure (xi lam b : ℝ) : ℝ := (1 - lam / b) / xi

def two (xi z v lam q : ℝ) : ℝ :=
  z * (v - lam / (1 - xi * q)) +
    (1-z) * (v * (2*q-q^2) - 2*lam*q)

def one (xi z v lam q : ℝ) : ℝ :=
  (z/2+(1-z)*q) * (v-lam/(1-xi*q))

def outsideTwo (v lam : ℝ) : ℝ := (v-lam)^2/v

def independentTwo (eta v b q : ℝ) : ℝ :=
  v * (2*q-q^2) - b * (2*q-(1-eta)*q^2)

lemma mixed_receipt (xi lam b : ℝ) (hxi : xi ≠ 0) (hb : b ≠ 0) :
    b * (1-xi*exposure xi lam b) = lam := by
  unfold exposure
  field_simp
  ring

lemma exposure_mem_Ioo {xi lam b : ℝ} (hxi : 0 < xi) (hb : 0 < b)
    (hlow : (1-xi)*b < lam) (hhigh : lam < b) :
    exposure xi lam b ∈ Ioo (0 : ℝ) 1 := by
  have hlo : 1-xi < lam/b := (lt_div_iff₀ hb).2 (by nlinarith)
  have hhi : lam/b < 1 := (div_lt_one hb).2 hhigh
  constructor
  · exact div_pos (by linarith) hxi
  · exact (div_lt_one hxi).2 (by linarith)

lemma independentTwo_eq_menu {xi eta lam b v : ℝ}
    (heta : eta = 1-2*xi) (hxi : xi ≠ 0) (hb : b ≠ 0) :
    independentTwo eta v b (exposure xi lam b) =
      two xi 0 v lam (exposure xi lam b) := by
  rw [heta]
  unfold independentTwo two exposure
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  field_simp
  ring

lemma exclusive_gain_identity (eta v b q : ℝ) :
    (v-b)-independentTwo eta v b q =
      (v-b)*(1-q)^2 + eta*b*q^2 := by
  unfold independentTwo
  ring

lemma exclusive_gain_pos {eta v b q : ℝ}
    (heta : 0 < eta) (hb : 0 < b) (hbv : b < v)
    (hq : q ∈ Icc (0 : ℝ) 1) :
    0 < (v-b)-independentTwo eta v b q := by
  rw [exclusive_gain_identity]
  by_cases hq1 : q = 1
  · subst q
    simpa using mul_pos heta hb
  · have hq' : q < 1 := lt_of_le_of_ne hq.2 hq1
    have hp : 0 < (v-b)*(1-q)^2 :=
      mul_pos (sub_pos.mpr hbv) (sq_pos_of_pos (sub_pos.mpr hq'))
    have hn : 0 ≤ eta*b*q^2 := mul_nonneg (mul_pos heta hb).le (sq_nonneg q)
    linarith

lemma exclusive_gain_uniform {eta v b q L U vmin : ℝ}
    (heta : 0 < eta) (hL : 0 < L) (hbL : L ≤ b) (hbU : b ≤ U)
    (hUv : U < vmin) (hvv : vmin ≤ v) :
    min (vmin-U) (eta*L) / 2 ≤
      (v-b)-independentTwo eta v b q := by
  rw [exclusive_gain_identity]
  have hmin0 : 0 ≤ min (vmin-U) (eta*L) :=
    le_min (sub_pos.mpr hUv).le (mul_pos heta hL).le
  have hleft : min (vmin-U) (eta*L) ≤ v-b := by
    exact (min_le_left _ _).trans (by linarith)
  have hright : min (vmin-U) (eta*L) ≤ eta*b :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hbL heta.le)
  have h1 := mul_le_mul_of_nonneg_right hleft (sq_nonneg (1-q))
  have h2 := mul_le_mul_of_nonneg_right hright (sq_nonneg q)
  have h3 := mul_nonneg hmin0 (sq_nonneg (q-1/2))
  nlinarith

lemma two_zero_square (xi v lam q : ℝ) (hv : v ≠ 0) :
    two xi 0 v lam q = outsideTwo v lam - v*(q-(1-lam/v))^2 := by
  unfold two outsideTwo
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  field_simp
  ring

lemma two_zero_max {xi v lam : ℝ} (hv : 0 < v)
    (hlam : 0 < lam) (hlv : lam < v) :
    (1-lam/v) ∈ Ioo (0 : ℝ) 1 ∧
      two xi 0 v lam (1-lam/v) = outsideTwo v lam ∧
      ∀ q : ℝ, two xi 0 v lam q ≤ outsideTwo v lam := by
  have hr0 : 0 < lam/v := div_pos hlam hv
  have hr1 : lam/v < 1 := (div_lt_one hv).2 hlv
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [two_zero_square _ _ _ _ hv.ne']
    simp
  · intro q
    rw [two_zero_square _ _ _ _ hv.ne']
    exact sub_le_self _ (mul_nonneg hv.le (sq_nonneg _))

lemma two_zero_strict_away {xi v lam q : ℝ} (hv : 0 < v)
    (hq : q ≠ 1-lam/v) :
    two xi 0 v lam q < outsideTwo v lam := by
  rw [two_zero_square _ _ _ _ hv.ne']
  exact sub_lt_self _ (mul_pos hv (sq_pos_of_ne_zero (sub_ne_zero.mpr hq)))

lemma two_jensen_gap {xi z v lam q r t : ℝ}
    (h0 : 1-xi*q ≠ 0) (h1 : 1-xi*r ≠ 0)
    (ht : 1-xi*((1-t)*q+t*r) ≠ 0) :
    two xi z v lam ((1-t)*q+t*r) -
      ((1-t)*two xi z v lam q + t*two xi z v lam r) =
    (1-z)*v*t*(1-t)*(r-q)^2 +
      z*lam*t*(1-t)*xi^2*(r-q)^2 /
        ((1-xi*q)*(1-xi*r)*(1-xi*((1-t)*q+t*r))) := by
  unfold two
  field_simp
  ring

lemma two_strict_jensen {xi z v lam q r t : ℝ}
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hv : 0 < v) (hlam : 0 < lam)
    (hq : q ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (hqr : q ≠ r) (ht0 : 0 < t) (ht1 : t < 1) :
    (1-t)*two xi z v lam q + t*two xi z v lam r <
      two xi z v lam ((1-t)*q+t*r) := by
  have hqden : 0 < 1-xi*q := by nlinarith [hq.2]
  have hrden : 0 < 1-xi*r := by nlinarith [hr.2]
  have hmid : (1-t)*q+t*r ≤ 1 := by
    nlinarith [mul_nonneg (sub_pos.mpr ht1).le (sub_nonneg.mpr hq.2),
      mul_nonneg ht0.le (sub_nonneg.mpr hr.2)]
  have hmidden : 0 < 1-xi*((1-t)*q+t*r) := by nlinarith
  have hgap := two_jensen_gap (z := z) (v := v) (lam := lam)
    hqden.ne' hrden.ne' hmidden.ne'
  have hpositive : 0 < (1-z)*v*t*(1-t)*(r-q)^2 := by
    exact mul_pos
      (mul_pos (mul_pos (mul_pos (sub_pos.mpr hz1) hv) ht0) (sub_pos.mpr ht1))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hqr.symm))
  have hnonnegative : 0 ≤ z*lam*t*(1-t)*xi^2*(r-q)^2 /
      ((1-xi*q)*(1-xi*r)*(1-xi*((1-t)*q+t*r))) := by
    positivity
  linarith

def phi (xi z q : ℝ) : ℝ :=
  (1-q) / (1+z*xi/(2*(1-z)*(1-xi*q)^2))

lemma phi_one {xi z : ℝ} : phi xi z 1 = 0 := by simp [phi]
lemma phi_zero (xi z : ℝ) : phi xi z 0 = 1/(1+z*xi/(2*(1-z))) := by
  simp [phi]

lemma phi_strictAntiOn {xi z : ℝ} (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    StrictAntiOn (phi xi z) (Icc (0 : ℝ) 1) := by
  intro q hq r hr hqr
  have hdq : 0 < 1-xi*q := by nlinarith [hq.2]
  have hdr : 0 < 1-xi*r := by nlinarith [hr.2]
  have hdenorder : 2*(1-z)*(1-xi*r)^2 ≤ 2*(1-z)*(1-xi*q)^2 := by
    have hmul : xi*q < xi*r := mul_lt_mul_of_pos_left hqr hxi0
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hdr.le hdq.le).2 (by linarith)) (by linarith)
  have hdq' : 0 < 2*(1-z)*(1-xi*q)^2 := by positivity
  have hdr' : 0 < 2*(1-z)*(1-xi*r)^2 := by positivity
  have hfrac : z*xi/(2*(1-z)*(1-xi*q)^2) ≤
      z*xi/(2*(1-z)*(1-xi*r)^2) :=
    div_le_div_of_nonneg_left (mul_nonneg hz0 hxi0.le) hdr' hdenorder
  have hDq : 0 < 1+z*xi/(2*(1-z)*(1-xi*q)^2) := by positivity
  have hDr : 0 < 1+z*xi/(2*(1-z)*(1-xi*r)^2) := by positivity
  unfold phi
  calc
    (1-r)/(1+z*xi/(2*(1-z)*(1-xi*r)^2))
        ≤ (1-r)/(1+z*xi/(2*(1-z)*(1-xi*q)^2)) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hr.2) hDq (by linarith)
    _ < (1-q)/(1+z*xi/(2*(1-z)*(1-xi*q)^2)) :=
      (div_lt_div_iff_of_pos_right hDq).2 (by linarith)

lemma phi_injectiveOn {xi z : ℝ} (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Set.InjOn (phi xi z) (Icc (0 : ℝ) 1) :=
  (phi_strictAntiOn hxi0 hxi1 hz0 hz1).injOn

def bidDerivative (xi z v lam b : ℝ) : ℝ :=
  -z + 2*(1-z)*lam*(v*(1-exposure xi lam b)-lam)/(xi*b^2)

def inwardScale (xi z qbar : ℝ) : ℝ :=
  (1-qbar)*(1-xi*qbar)/((1-xi*qbar)^2+z*xi/(2*(1-z)))

lemma reference_derivative_identity {xi z qbar v b : ℝ}
    (hxi : xi ≠ 0) (hz : 1-z ≠ 0) (hb : b ≠ 0)
    (hD : (1-xi*qbar)^2+z*xi/(2*(1-z)) ≠ 0) :
    bidDerivative xi z v ((1-xi*qbar)*b) b =
      (2*(1-z)*((1-xi*qbar)^2+z*xi/(2*(1-z)))/(xi*b)) *
        (inwardScale xi z qbar*v-b) := by
  unfold bidDerivative exposure inwardScale
  generalize hDdef : (1-xi*qbar)^2+z*xi/(2*(1-z)) = D at hD ⊢
  field_simp [hxi,hb,hD]
  rw [←hDdef]
  field_simp [hz]
  ring

lemma quadratic_positive_above {A B C x y : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hx : 0 < x) (hxy : x ≤ y)
    (hxpos : 0 < A*x^2-B*x-C) : 0 < A*y^2-B*y-C := by
  have hax : 0 < A*x-B := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hx.le h
    nlinarith
  have hsum : 0 < A*(y+x)-B := by nlinarith
  have hdiff := mul_nonneg (sub_nonneg.mpr hxy) hsum.le
  nlinarith

lemma quadratic_negative_below {A B C x y : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hx : 0 < x) (hxy : x ≤ y)
    (hyneg : A*y^2-B*y-C < 0) : A*x^2-B*x-C < 0 := by
  have hy : 0 < y := hx.trans_le hxy
  have hid : y*(A*x^2-B*x-C) =
      x*(A*y^2-B*y-C) - A*x*y*(y-x) - C*(y-x) := by ring
  have hn1 : 0 ≤ A*x*y*(y-x) := by positivity
  have hn2 : 0 ≤ C*(y-x) := by positivity
  have hp : x*(A*y^2-B*y-C) < 0 := mul_neg_of_pos_of_neg hx hyneg
  have : y*(A*x^2-B*x-C) < 0 := by linarith
  exact neg_of_mul_neg_right this hy.le

end FCAppendix.Affine.Hybrid
