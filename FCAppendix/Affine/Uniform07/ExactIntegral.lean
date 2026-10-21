import FCAppendix.Affine.Uniform07.Parameters
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Choose.Cast

namespace FCAppendix.Affine.Uniform07
open MeasureTheory Set
open scoped BigOperators
noncomputable def invMoment (l h : ℝ) : ℕ → ℝ
 | 0 => h-l
 | 1 => Real.log h-Real.log l
 | n+2 => (l⁻¹^(n+1)-h⁻¹^(n+1))/(n+1:ℝ)
noncomputable def invPrimitive : ℕ → ℝ → ℝ
 | 0 => id
 | 1 => Real.log
 | n+2 => fun y => -(y⁻¹^(n+1))/(n+1:ℝ)
private theorem invPrimitive_derivative (n : ℕ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (invPrimitive n) (y⁻¹^n) y := by
  cases n with
  | zero => simpa [invPrimitive] using hasDerivAt_id y
  | succ n =>
    cases n with
    | zero => simpa [invPrimitive] using Real.hasDerivAt_log hy
    | succ n =>
      have hd : HasDerivAt (fun t : ℝ => -(t⁻¹^(n+1))/(n+1:ℝ))
          (-(((n+1:ℕ):ℝ)*y⁻¹^n*-(y^2)⁻¹)/(n+1:ℝ)) y := by
        simpa only [Pi.pow_apply, Pi.neg_apply, Nat.add_sub_cancel] using
          (((hasDerivAt_inv hy).pow (n+1)).neg.div_const (n+1:ℝ))
      have he : -(((n+1:ℕ):ℝ)*y⁻¹^n*-(y^2)⁻¹)/(n+1:ℝ) = y⁻¹^(n+1+1) := by
        simp only [Nat.cast_add, Nat.cast_one, pow_succ, inv_pow]
        field_simp [hy, show (n:ℝ)+1 ≠ 0 by positivity]
      simpa only [he, invPrimitive] using hd

theorem integral_invpow (n : ℕ) {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h) :
    (∫ y in l..h, y⁻¹^n) = invMoment l h n := by
  have hnz : ∀ y ∈ uIcc l h, y ≠ 0 := by
    intro y hy; rw [uIcc_of_le hlh] at hy; exact (hl.trans_le hy.1).ne'
  have hc : ContinuousOn (fun y : ℝ => y⁻¹^n) (uIcc l h) :=
    (continuousOn_id.inv₀ hnz).pow n
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => invPrimitive_derivative n (hnz y hy)) hc.intervalIntegrable]
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => simp [invPrimitive,invMoment]; ring

noncomputable def moment (a c l h : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (k.choose j:ℝ)*a^(k-j)*(-c)^j*invMoment l h j

theorem integral_moment (a c : ℝ) (k : ℕ) {l h : ℝ}
    (hl : 0 < l) (hlh : l ≤ h) :
    (∫ y in l..h, (a-c/y)^k) = moment a c l h k := by
  have hc (j : ℕ) : IntervalIntegrable (fun y : ℝ => y⁻¹^j) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.pow
    apply continuousOn_id.inv₀
    intro y hy; rw [uIcc_of_le hlh] at hy; exact (hl.trans_le hy.1).ne'
  have hex (y : ℝ) : (a-c/y)^k = ∑ j ∈ Finset.range (k+1),
      ((k.choose j:ℝ)*a^(k-j)*(-c)^j)*y⁻¹^j := by
    rw [show a-c/y=(-c)*y⁻¹+a by ring,add_pow]
    apply Finset.sum_congr rfl
    intro j hj; rw [mul_pow]; ring
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hc j).const_mul _)]
  unfold moment
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_const_mul,integral_invpow j hl hlh]

def invMomentBox (l h : ℚ) (ll hh : Box) : ℕ → Box
 | 0 => Box.point (h-l)
 | 1 => Box.sub hh ll
 | n+2 => Box.point ((l⁻¹^(n+1)-h⁻¹^(n+1))/(n+1:ℚ))
def momentBox (a c l h : ℚ) (ll hh : Box) (k : ℕ) : Box :=
  Box.sum (Finset.range (k+1)) (fun j =>
    Box.scale (((k.factorial:ℚ)/((j.factorial:ℚ)*((k-j).factorial:ℚ)))*a^(k-j)*(-c)^j) (invMomentBox l h ll hh j))
theorem invMomentBox_ok (l h : ℚ) {ll hh : Box}
    (hl : ll.Holds (Real.log (l:ℝ))) (hh' : hh.Holds (Real.log (h:ℝ))) (n : ℕ) :
    (invMomentBox l h ll hh n).Holds (invMoment (l:ℝ) (h:ℝ) n) := by
  cases n with
  | zero => simpa [invMomentBox,invMoment] using Box.point_ok (h-l)
  | succ n =>
    cases n with
    | zero => exact Box.sub_ok hh' hl
    | succ n => simpa [invMomentBox,invMoment] using
        Box.point_ok ((l⁻¹^(n+1)-h⁻¹^(n+1))/(n+1:ℚ))
theorem momentBox_ok (a c l h : ℚ) {ll hh : Box}
    (hl : ll.Holds (Real.log (l:ℝ))) (hh' : hh.Holds (Real.log (h:ℝ))) (k : ℕ) :
    (momentBox a c l h ll hh k).Holds (moment (a:ℝ) (c:ℝ) l h k) := by
  apply Box.sum_ok
  intro j hj
  have hjk : j ≤ k := by have hh := Finset.mem_range.mp hj; omega
  change (Box.scale (((k.factorial:ℚ)/((j.factorial:ℚ)*((k-j).factorial:ℚ)))*
    a^(k-j)*(-c)^j) (invMomentBox l h ll hh j)).Holds _
  rw [← Nat.cast_choose ℚ hjk]
  simpa using Box.scale_ok ((k.choose j:ℚ)*a^(k-j)*(-c)^j)
    (invMomentBox_ok l h hl hh' j)

noncomputable def pieceP (a c y : ℝ) : ℝ := a-c/y
noncomputable def pieceZ (a c theta l h : ℝ) : ℝ :=
  ∫ y in l..h, Real.exp (-theta*pieceP a c y)
noncomputable def pieceF (a c theta l h : ℝ) : ℝ :=
  ∫ y in l..h, (pieceP a c y-rho)*Real.exp (-theta*pieceP a c y)
noncomputable def pieceZPoly (n : ℕ) (a c theta l h : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-theta)^k/(k.factorial:ℝ)*moment a c l h k
noncomputable def pieceFPoly (n : ℕ) (a c theta l h : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-theta)^k/(k.factorial:ℝ)*
    (moment a c l h (k+1)-rho*moment a c l h k)
def pieceZBox (n : ℕ) (a c theta l h : ℚ) (ll hh : Box) : Box :=
  Box.sum (Finset.range n) (fun k => Box.scale ((-theta)^k/(k.factorial:ℚ))
    (momentBox a c l h ll hh k))
def pieceFBox (n : ℕ) (a c theta l h : ℚ) (ll hh : Box) : Box :=
  Box.sum (Finset.range n) (fun k => Box.scale ((-theta)^k/(k.factorial:ℚ))
    (Box.sub (momentBox a c l h ll hh (k+1))
      (Box.scale (999/2000) (momentBox a c l h ll hh k))))
theorem pieceZBox_ok (n : ℕ) (a c theta l h : ℚ) {ll hh : Box}
    (hl : ll.Holds (Real.log (l:ℝ))) (hh' : hh.Holds (Real.log (h:ℝ))) :
    (pieceZBox n a c theta l h ll hh).Holds (pieceZPoly n a c theta l h) := by
  apply Box.sum_ok
  intro k hk
  simpa using Box.scale_ok ((-theta)^k/(k.factorial:ℚ)) (momentBox_ok a c l h hl hh' k)
theorem pieceFBox_ok (n : ℕ) (a c theta l h : ℚ) {ll hh : Box}
    (hl : ll.Holds (Real.log (l:ℝ))) (hh' : hh.Holds (Real.log (h:ℝ))) :
    (pieceFBox n a c theta l h ll hh).Holds (pieceFPoly n a c theta l h) := by
  apply Box.sum_ok
  intro k hk
  simpa [rho] using Box.scale_ok ((-theta)^k/(k.factorial:ℚ))
    (Box.sub_ok (momentBox_ok a c l h hl hh' (k+1))
      (Box.scale_ok (999/2000) (momentBox_ok a c l h hl hh' k)))

private theorem continuous_piece {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h) (a c : ℝ) :
    ContinuousOn (pieceP a c) (uIcc l h) := by
  unfold pieceP
  exact continuousOn_const.sub (continuousOn_const.div continuousOn_id (by
    intro y hy; rw [uIcc_of_le hlh] at hy; exact (hl.trans_le hy.1).ne'))

private theorem poly_integral (n : ℕ) (a c theta : ℝ) {l h : ℝ}
    (hl : 0 < l) (hlh : l ≤ h) :
    (∫ y in l..h, expPoly n (-theta*pieceP a c y)) = pieceZPoly n a c theta l h := by
  have hc := continuous_piece hl hlh a c
  have hex (y : ℝ) : expPoly n (-theta*pieceP a c y) =
      ∑ k ∈ Finset.range n, ((-theta)^k/(k.factorial:ℝ))*(a-c/y)^k := by
    unfold expPoly pieceP
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_pow]
    ring
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (f := fun k y =>
    (-theta)^k/(k.factorial:ℝ)*(a-c/y)^k) (fun k _ =>
    ((hc.pow k).const_mul _).intervalIntegrable)]
  unfold pieceZPoly
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_const_mul,integral_moment a c k hl hlh]

private theorem weighted_poly_integral (n : ℕ) (a c theta : ℝ) {l h : ℝ}
    (hl : 0 < l) (hlh : l ≤ h) :
    (∫ y in l..h, (pieceP a c y-rho)*expPoly n (-theta*pieceP a c y)) =
      pieceFPoly n a c theta l h := by
  have hc := continuous_piece hl hlh a c
  have he (y : ℝ) : (pieceP a c y-rho)*expPoly n (-theta*pieceP a c y) =
      ∑ k ∈ Finset.range n, ((-theta)^k/(k.factorial:ℝ))*
        ((pieceP a c y)^(k+1)-rho*(pieceP a c y)^k) := by
    unfold expPoly
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk; rw [mul_pow,pow_succ]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (f := fun k y =>
    (-theta)^k/(k.factorial:ℝ)*(pieceP a c y^(k+1)-rho*pieceP a c y^k)) (fun k _ =>
    (((hc.pow (k+1)).sub ((hc.pow k).const_mul rho)).const_mul _).intervalIntegrable)]
  unfold pieceFPoly
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (f := fun y => pieceP a c y^(k+1)) (g := fun y => rho*pieceP a c y^k)
      (hc.pow (k+1)).intervalIntegrable
      ((hc.pow k).const_mul rho).intervalIntegrable,intervalIntegral.integral_const_mul]
  rw [show pieceP a c = (fun y => a-c/y) from rfl,
    integral_moment a c (k+1) hl hlh,integral_moment a c k hl hlh]

theorem piece_errors (n : ℕ) {a c theta l h : ℝ} (hl : 0 < l) (hlh : l ≤ h)
    (htheta : 0 ≤ theta) (hsmall : theta/(n+1:ℝ) ≤ 1/2)
    (hp : ∀ y ∈ Icc l h, pieceP a c y ∈ Icc 0 1) :
    |pieceZ a c theta l h-pieceZPoly n a c theta l h| ≤
      (h-l)*(2*theta^n/(n.factorial:ℝ)) ∧
    |pieceF a c theta l h-pieceFPoly n a c theta l h| ≤
      (h-l)*(2*theta^n/(n.factorial:ℝ)) := by
  have hc := continuous_piece hl hlh a c
  have he : ContinuousOn (fun y => Real.exp (-theta*pieceP a c y)) (uIcc l h) := by fun_prop
  have hpoly : ContinuousOn (fun y => expPoly n (-theta*pieceP a c y)) (uIcc l h) := by
    unfold expPoly; fun_prop
  have herr (y : ℝ) (hy : y ∈ Icc l h) :
      |Real.exp (-theta*pieceP a c y)-expPoly n (-theta*pieceP a c y)| ≤
        2*theta^n/(n.factorial:ℝ) := by
    have hp' := hp y hy
    apply expPoly_error n htheta _ hsmall
    rw [abs_mul,abs_neg,abs_of_nonneg htheta,abs_of_nonneg hp'.1]
    nlinarith [htheta,hp'.2]
  constructor
  · rw [← poly_integral n a c theta hl hlh]
    unfold pieceZ
    rw [← intervalIntegral.integral_sub he.intervalIntegrable hpoly.intervalIntegrable]
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := l) (b := h)
      (f := fun y => Real.exp (-theta*pieceP a c y)-expPoly n (-theta*pieceP a c y))
      (C := 2*theta^n/(n.factorial:ℝ)) (by
        intro y hy; rw [uIoc_of_le hlh] at hy
        simpa [Real.norm_eq_abs] using herr y ⟨hy.1.le,hy.2⟩)
    simpa [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hlh),mul_comm] using H
  · rw [← weighted_poly_integral n a c theta hl hlh]
    unfold pieceF
    have hw : ContinuousOn (fun y => pieceP a c y-rho) (uIcc l h) := by fun_prop
    rw [← intervalIntegral.integral_sub
      (f := fun y => (pieceP a c y-rho)*Real.exp (-theta*pieceP a c y))
      (g := fun y => (pieceP a c y-rho)*expPoly n (-theta*pieceP a c y))
      (hw.mul he).intervalIntegrable (hw.mul hpoly).intervalIntegrable]
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := l) (b := h)
      (f := fun y => (pieceP a c y-rho)*Real.exp (-theta*pieceP a c y)-
        (pieceP a c y-rho)*expPoly n (-theta*pieceP a c y))
      (C := 2*theta^n/(n.factorial:ℝ)) (by
        intro y hy; rw [uIoc_of_le hlh] at hy
        have hp' := hp y ⟨hy.1.le,hy.2⟩
        have hw' : |pieceP a c y-rho| ≤ 1 := by
          rw [abs_le]; dsimp [rho]; constructor <;> linarith [hp'.1,hp'.2]
        rw [Real.norm_eq_abs,← mul_sub,abs_mul]
        simpa using mul_le_mul hw' (herr y ⟨hy.1.le,hy.2⟩) (abs_nonneg _)
          (by norm_num : (0:ℝ) ≤ 1))
    simpa [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hlh),mul_comm] using H
end FCAppendix.Affine.Uniform07
