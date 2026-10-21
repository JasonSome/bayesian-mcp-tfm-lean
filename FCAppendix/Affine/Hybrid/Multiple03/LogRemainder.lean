import Mathlib
import FCAppendix.Affine.Uniform07.RationalBounds

noncomputable section
namespace FCAppendix.Affine.Hybrid.Multiple03
open MeasureTheory Set
open scoped BigOperators

def atanhPolynomial (N : ℕ) (y : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range N, y^(2*j+1)/(2*j+1:ℝ)

def atanhLog (y : ℝ) : ℝ := Real.log (1+y)-Real.log (1-y)

def logPartial (N : ℕ) (x : ℝ) : ℝ :=
  atanhPolynomial N ((x-1)/(x+1))

def logRadius (N : ℕ) (x : ℝ) : ℝ :=
  2 * |(x-1)/(x+1)|^(2*N+1) /
    ((2*N+1:ℝ)*(1-((x-1)/(x+1))^2))

private lemma finite_geometric_even (N : ℕ) (y : ℝ) :
    (1-y^2)*(∑ j ∈ Finset.range N, y^(2*j))=1-y^(2*N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hp : y^(2*(N+1))=y^(2*N)*y^2 := by
      rw [show 2*(N+1)=2*N+2 by omega, pow_add]
    rw [hp]
    ring

private lemma atanhPolynomial_derivative (N : ℕ) (y : ℝ) :
    HasDerivAt (atanhPolynomial N) (2*∑ j ∈ Finset.range N, y^(2*j)) y := by
  induction N with
  | zero =>
    have hz : atanhPolynomial 0 = fun _ : ℝ => 0 := by ext x; simp [atanhPolynomial]
    rw [hz]
    simpa using hasDerivAt_const y (0:ℝ)
  | succ N ih =>
    have hpow : HasDerivAt (fun x : ℝ => 2*x^(2*N+1)/(2*N+1:ℝ))
        (2*y^(2*N)) y := by
      have hd := (((hasDerivAt_id y).pow (2*N+1)).const_mul 2).div_const
        (2*N+1:ℝ)
      convert! hd using 1 ; simp only [Nat.add_sub_cancel, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, id_eq]
      field_simp [show (2:ℝ)*N+1 ≠ 0 by positivity]
    convert! ih.add hpow using 1
    · ext x
      simp only [atanhPolynomial, Finset.sum_range_succ, Pi.add_apply]
      ring
    · simp only [Finset.sum_range_succ]
      ring

private lemma atanhLog_derivative {y : ℝ} (hy : |y|<1) :
    HasDerivAt atanhLog (2/(1-y^2)) y := by
  have hyl : -1< y := (abs_lt.mp hy).1
  have hyr : y<1 := (abs_lt.mp hy).2
  have hplus : 1+y ≠ 0 := by linarith
  have hminus : 1-y ≠ 0 := by linarith
  have hsq : 1-y^2 ≠ 0 := by
    have hp := mul_pos (by linarith : 0<1+y) (by linarith : 0<1-y)
    nlinarith
  have hd := (((hasDerivAt_const y (1:ℝ)).add (hasDerivAt_id y)).log hplus).sub
    (((hasDerivAt_const y (1:ℝ)).sub (hasDerivAt_id y)).log hminus)
  convert! hd using 1
  dsimp
  field_simp [hplus,hminus,hsq]
  ring

private lemma remainder_derivative (N : ℕ) {y : ℝ} (hy : |y|<1) :
    HasDerivAt (fun x => atanhLog x-atanhPolynomial N x)
      (2*y^(2*N)/(1-y^2)) y := by
  have hg := finite_geometric_even N y
  have hsq : 1-y^2 ≠ 0 := by
    have h := abs_lt.mp hy
    have hp := mul_pos (by linarith [h.1] : 0<1+y)
      (by linarith [h.2] : 0<1-y)
    nlinarith
  convert! (atanhLog_derivative hy).sub (atanhPolynomial_derivative N y) using 1
  field_simp [hsq]
  nlinarith [hg]

private lemma positive_atanh_remainder (N : ℕ) {y : ℝ}
    (hy0 : 0≤ y) (hy1 : y<1) :
    0≤ atanhLog y-atanhPolynomial N y ∧
    atanhLog y-atanhPolynomial N y ≤
      2*y^(2*N+1)/((2*N+1:ℝ)*(1-y^2)) := by
  let f : ℝ→ℝ := fun x => 2*x^(2*N)/(1-x^2)
  let g : ℝ→ℝ := fun x => (2/(1-y^2))*x^(2*N)
  have hyden : 0<1-y^2 := by
    have hp := mul_pos (by linarith : 0<1+y) (by linarith : 0<1-y)
    nlinarith
  have hxd (x : ℝ) (hx : x∈Icc 0 y) : 0<1-x^2 := by
    have hp := mul_pos (by linarith [hx.1] : 0<1+x)
      (by linarith [hx.2] : 0<1-x)
    nlinarith
  have hf : ContinuousOn f (uIcc 0 y) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      rw [uIcc_of_le hy0] at hx
      exact (hxd x hx).ne'
  have hg : ContinuousOn g (uIcc 0 y) := by fun_prop
  have heq : (∫ x in 0..y, f x)=atanhLog y-atanhPolynomial N y := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a:=0) (b:=y) (f:=fun x => atanhLog x-atanhPolynomial N x)
      (f':=f) (fun x hx => by
        rw [uIcc_of_le hy0] at hx
        exact remainder_derivative N (by
          rw [abs_of_nonneg hx.1]
          exact hx.2.trans_lt hy1)) hf.intervalIntegrable
    simpa [atanhLog,atanhPolynomial] using hi
  have hnonneg : 0≤∫ x in 0..y,f x := by
    apply intervalIntegral.integral_nonneg hy0
    intro x hx
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx.1 _))
      (hxd x hx).le
  have hle : (∫ x in 0..y,f x)≤∫ x in 0..y,g x := by
    apply intervalIntegral.integral_mono_on hy0 hf.intervalIntegrable hg.intervalIntegrable
    intro x hx
    have hxden := hxd x hx
    have hden : 1-y^2≤1-x^2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hy0 hx.1)
      nlinarith
    dsimp [f,g]
    calc
      2*x^(2*N)/(1-x^2) ≤ 2*x^(2*N)/(1-y^2) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (pow_nonneg hx.1 _)) hyden hden
      _=(2/(1-y^2))*x^(2*N) := by ring
  have hgint : (∫ x in 0..y,g x)=
      2*y^(2*N+1)/((2*N+1:ℝ)*(1-y^2)) := by
    dsimp [g]
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp only [zero_pow (show 2*N+1≠0 by omega),sub_zero]
    push_cast
    field_simp [hyden.ne',show (2:ℝ)*N+1 ≠ 0 by positivity]
  exact ⟨by simpa only [heq] using hnonneg,by simpa only [heq,hgint] using hle⟩

private lemma atanhPolynomial_neg (N : ℕ) (y : ℝ) :
    atanhPolynomial N (-y)=-atanhPolynomial N y := by
  have hp (j : ℕ) : (-y)^(2*j+1)= -y^(2*j+1) := by
    rw [pow_add,pow_mul,pow_add,pow_mul]
    simp
  simp only [atanhPolynomial,hp,neg_div,Finset.sum_neg_distrib]
  ring

private lemma atanhLog_neg (y : ℝ) : atanhLog (-y)=-atanhLog y := by
  simp [atanhLog] ; ring

theorem atanh_series_integral_remainder (N : ℕ) (x : ℝ) (hx : 0< x) :
    |Real.log x-logPartial N x|≤ logRadius N x := by
  let y : ℝ := (x-1)/(x+1)
  have hd : 0< x+1 := by linarith
  have hy : |y|<1 := by
    dsimp [y]
    rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hd]
      linarith
    · rw [div_lt_one hd]
      linarith
  have hplus : 0<1+y := by have hh := (abs_lt.mp hy).1; linarith
  have hminus : 0<1-y := by have hh := (abs_lt.mp hy).2; linarith
  have hlog : atanhLog y=Real.log x := by
    rw [atanhLog,←Real.log_div hplus.ne' hminus.ne']
    congr 1
    dsimp [y]
    field_simp [hd.ne']
    ring
  have hpos := positive_atanh_remainder N (abs_nonneg y) hy
  have hsquare : |y|^2=y^2 := sq_abs y
  have herror : |atanhLog y-atanhPolynomial N y|=
      atanhLog |y|-atanhPolynomial N |y| := by
    by_cases hy0 : 0≤ y
    · rw [abs_of_nonneg hy0] at hpos ⊢
      exact abs_of_nonneg hpos.1
    · have hy0' : y≤0 := (lt_of_not_ge hy0).le
      rw [abs_of_nonpos hy0',atanhLog_neg,atanhPolynomial_neg] at hpos ⊢
      rw [show -atanhLog y- -atanhPolynomial N y=
        -(atanhLog y-atanhPolynomial N y) by ring] at hpos ⊢
      exact abs_of_nonpos (by linarith [hpos.1])
  change |Real.log x-atanhPolynomial N y|≤
    2*|y|^(2*N+1)/((2*N+1:ℝ)*(1-y^2))
  rw [←hlog,herror]
  simpa only [hsquare] using hpos.2

theorem log_enclosure (N : ℕ) (x : ℝ) (hx : 0< x) :
    |Real.log x-logPartial N x|≤ logRadius N x :=
  atanh_series_integral_remainder N x hx

end FCAppendix.Affine.Hybrid.Multiple03
