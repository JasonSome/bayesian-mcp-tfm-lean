import FCAppendix.Affine.Hybrid.UpperCountDifference
import FCAppendix.Probability.BinomialTails

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open Affine.LowBody

def upperTieError (h : ℝ) (N : ℕ) : ℝ:=
  4*(1-h)/((N:ℝ)*h)+Real.sqrt (2/((N:ℝ)*h/2+1))

lemma binomial_lower_half_chebyshev {h : ℝ} (hh : 0 < h) (hh1 : h  ≤  1)
    (N : ℕ) (hN : 0 < N) :
    (IndependentCounts.binomial N h hh.le hh1).prob
      (fun K=>(K.val:ℝ)  ≤  (N:ℝ)*h/2)  ≤  4*(1-h)/((N:ℝ)*h) := by
  let B:=IndependentCounts.binomial N h hh.le hh1
  have hmean : B.expect (fun K=>(K.val:ℝ))=(N:ℝ)*h:=
    IndependentCounts.binomial_load N h hh.le hh1
  have hp:=B.prob_mono (E:=fun K=>(K.val:ℝ)  ≤  (N:ℝ)*h/2)
    (F:=fun K=>(N:ℝ)*h/2  ≤  |(K.val:ℝ)-B.expect (fun t=>(t.val:ℝ))|) (by
      intro K hK
      rw [hmean,abs_of_nonpos (by linarith)]
      linarith)
  have ht:=B.chebyshev (fun K=>(K.val:ℝ)) ((N:ℝ)*h/2) (by positivity)
  rw [IndependentCounts.binomial_variance] at ht
  apply (hp.trans ht).trans_eq
  field_simp
  ring

theorem upperDifference_probability_le (s a h : ℝ)
    (hs : 0  ≤  s) (ha : 0  ≤  a) (hh : 0 < h) (hh1 : h  ≤  1) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N : ℕ) (hN : 0 < N) (q : ℤ) :
    (CommonList.iid (categoryLaw s a h hs ha hh.le hsum G) N).prob
      (fun row=>upperDifference row=q)  ≤
      4*(1-h)/((N:ℝ)*h)+Real.sqrt (2/((N:ℝ)*h/2+1)) := by
  rw [FiniteLaw.prob_eq_expect]
  have hm:=upperDifference_binomial_mixture s a h hs ha hh.le hh1 hsum G N
    (fun z=>if z=q then (1:ℝ) else 0)
  rw [hm]
  let B:=IndependentCounts.binomial N h hh.le hh1
  let R:=Real.sqrt (2/((N:ℝ)*h/2+1))
  have hR : 0  ≤  R:=Real.sqrt_nonneg _
  have hpoint (K : Fin (N+1)) :
      (CommonList.iid fairRoute K.val).prob (fun coins=>coinDifference coins=q)  ≤
        (if (K.val:ℝ)  ≤  (N:ℝ)*h/2 then (1:ℝ) else 0)+R := by
    by_cases hk : (K.val:ℝ)  ≤  (N:ℝ)*h/2
    · rw [if_pos hk]
      exact ((CommonList.iid fairRoute K.val).prob_le_one _).trans (by linarith)
    · rw [if_neg hk,zero_add]
      apply (fair_coin_difference_probability_le K.val q).trans
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ)  ≤  2) (by positivity)
        (by linarith : (N:ℝ)*h/2+1  ≤  (K.val:ℝ)+1)
  have he (K : Fin (N+1)) :
      fairWalkExpectation K.val (fun z=>if z=q then (1:ℝ) else 0)=
        (CommonList.iid fairRoute K.val).prob (fun coins=>coinDifference coins=q) := by
    unfold fairWalkExpectation
    rw [FiniteLaw.prob_eq_expect]
  rw [B.expect_congr he]
  have hi:=B.expect_mono hpoint
  rw [B.expect_add,B.expect_const,←B.prob_eq_expect] at hi
  have hc:=binomial_lower_half_chebyshev hh hh1 N hN
  dsimp only [B,R] at hi
  linarith

theorem forced_upperDifference_probability_le {r : ℕ} (s a h : ℝ)
    (hs : 0  ≤  s) (ha : 0  ≤  a) (hh : 0 < h) (hh1 : h  ≤  1) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (fixed : Fin r→Fin 4)
    (N : ℕ) (hN : 0 < N) (q : ℤ) :
    (CommonList.iid (categoryLaw s a h hs ha hh.le hsum G) N).prob
      (fun row=>upperDifference fixed+upperDifference row=q)  ≤
      4*(1-h)/((N:ℝ)*h)+Real.sqrt (2/((N:ℝ)*h/2+1)) := by
  have he (row : Fin N→Fin 4) :
      upperDifference fixed+upperDifference row=q↔upperDifference row=q-upperDifference fixed:=by omega
  have hp : (CommonList.iid (categoryLaw s a h hs ha hh.le hsum G) N).prob
      (fun row=>upperDifference fixed+upperDifference row=q)=
      (CommonList.iid (categoryLaw s a h hs ha hh.le hsum G) N).prob
      (fun row=>upperDifference row=q-upperDifference fixed) := by
    unfold FiniteLaw.prob
    apply FiniteLaw.expect_congr
    intro row
    simp only [he]
    split_ifs <;> rfl
  rw [hp]
  exact upperDifference_probability_le s a h hs ha hh hh1 hsum G N hN _

theorem upperTieError_tendsto_zero {h : ℝ} (hh : 0 < h) :
    Tendsto (upperTieError h) atTop (𝓝 0) := by
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop
  have hNh : Tendsto (fun N : ℕ=>(N:ℝ)*h) atTop atTop:=by
    simpa only [mul_comm] using hNat.const_mul_atTop hh
  have hfirst : Tendsto (fun N : ℕ=>4*(1-h)/((N:ℝ)*h)) atTop (𝓝 0):=
    tendsto_const_nhds.div_atTop hNh
  have hden : Tendsto (fun N : ℕ=>(N:ℝ)*h/2+1) atTop atTop := by
    have ht:=(hNat.const_mul_atTop (half_pos hh)).atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
    convert ht using 1
    funext N
    ring
  have hratio : Tendsto (fun N : ℕ=>2/((N:ℝ)*h/2+1)) atTop (𝓝 0):=
    tendsto_const_nhds.div_atTop hden
  have hroot:=Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  change Tendsto (fun N : ℕ=>4*(1-h)/((N:ℝ)*h)+Real.sqrt (2/((N:ℝ)*h/2+1))) atTop (𝓝 0)
  simpa only [Function.comp_def,Real.sqrt_zero,add_zero] using hfirst.add hroot

theorem upperTieError_le_six_div_sqrt {h : ℝ} (hh : 0 < h) (hh1 : h  ≤  1)
    (N : ℕ) (hN : 0 < N) : upperTieError h N  ≤  (6/h)/Real.sqrt N := by
  have hn : (0:ℝ)<N:=Nat.cast_pos.mpr hN
  have hn1 : (1:ℝ) ≤ N:=by exact_mod_cast hN
  have hr : 0<Real.sqrt (N:ℝ):=Real.sqrt_pos.mpr hn
  have hrsq : (Real.sqrt (N:ℝ))^2=N:=Real.sq_sqrt hn.le
  have hrN : Real.sqrt (N:ℝ) ≤ N:=by nlinarith [Real.sqrt_nonneg (N:ℝ)]
  have hfirst : 4*(1-h)/((N:ℝ)*h) ≤ 4/(h*Real.sqrt N) := by
    have hnum : 4*(1-h) ≤ (4:ℝ):=by linarith
    have hc:=div_le_div_of_nonneg_right hnum (mul_pos hn hh).le
    have hd:=div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) (mul_pos hh hr)
      (show h*Real.sqrt (N:ℝ) ≤ (N:ℝ)*h by nlinarith)
    exact hc.trans hd
  have hsecond : Real.sqrt (2/((N:ℝ)*h/2+1)) ≤ 2/(h*Real.sqrt N) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [div_pow,mul_pow,Real.sq_sqrt hn.le]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hsq : h^2 ≤ h:=by nlinarith
    have hmul:=mul_le_mul_of_nonneg_right hsq hn.le
    nlinarith
  dsimp only [upperTieError]
  calc
    _ ≤ 4/(h*Real.sqrt N)+2/(h*Real.sqrt N):=add_le_add hfirst hsecond
    _=(6/h)/Real.sqrt N:=by field_simp;ring

end FCAppendix.Affine.Hybrid
