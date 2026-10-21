import FCAppendix.Affine.LowBody.ExpectedClusterLoss

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {N : ℕ}

lemma integrable_literal_noisyRow {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (w x : ℝ) (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν] :
    Integrable (fun p : (Fin N→RowRival)×ℝ=>literalRowPayoff ξ c w (x*(1+ε*p.2),p.1))
      (ν.prod uniformNoise) := by
  have hm : Measurable (fun p : (Fin N→RowRival)×ℝ=>literalRowPayoff ξ c w (x*(1+ε*p.2),p.1)):=
    (measurable_literalRowPayoff hξ hξ1 c w).comp
      ((show Measurable (fun p : (Fin N→RowRival)×ℝ=>x*(1+ε*p.2)) from by fun_prop).prodMk measurable_fst)
  apply Integrable.of_bound hm.aestronglyMeasurable (|w|+(3+2*|1-ξ|)*(|x| *(1+|ε|)))
  have hz:= (measurePreserving_snd (μ:=ν) (ν:=uniformNoise)).quasiMeasurePreserving.ae uniformNoise_support
  filter_upwards [hz] with p hp
  have hza : |p.2| ≤ 1:=by rw [abs_of_nonneg hp.1];exact hp.2
  have hnoise : |1+ε*p.2| ≤ 1+|ε| := by
    calc
      _ ≤ |1|+|ε*p.2|:=abs_add_le _ _
      _ ≤ 1+|ε| *1:=by rw [abs_mul];gcongr;simp
      _=1+|ε|:=by ring
  have hmul : |x*(1+ε*p.2)| ≤ |x| *(1+|ε|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hnoise (abs_nonneg x)
  rw [Real.norm_eq_abs]
  exact (abs_literalRowPayoff_le hξ hξ1 c w (x*(1+ε*p.2)) p.1).trans (by gcongr)

theorem integral_literalSmoothed_sub {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (w x y : ℝ) (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν] :
    (∫ω,literalSmoothedRowPayoff ξ ε c w x ω-literalSmoothedRowPayoff ξ ε c w y ω ∂ν)=
      ∫z,(∫ω,literalRowPayoff ξ c w (x*(1+ε*z),ω)-
        literalRowPayoff ξ c w (y*(1+ε*z),ω) ∂ν) ∂uniformNoise := by
  have hiX:=integrable_literal_noisyRow hξ hξ1 ε c w x ν
  have hiY:=integrable_literal_noisyRow hξ hξ1 ε c w y ν
  calc
    _=∫ω,(∫z,literalRowPayoff ξ c w (x*(1+ε*z),ω)-
        literalRowPayoff ξ c w (y*(1+ε*z),ω) ∂uniformNoise) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hiX.prod_right_ae,hiY.prod_right_ae] with ω hx hy
      exact (integral_sub hx hy).symm
    _=_:=integral_integral_swap (hiX.sub hiY)

variable {d : ℝ}

theorem expected_literalSmoothed_uniform_raise {ξ l U W ε : ℝ}
    (hξ : 0<ξ) (hξh : ξ ≤ 1/2) (hl : 0<l) (hlU : l ≤ U) (hW : 0 ≤ W) (hε : 0 ≤ ε)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    ∀e>0,∃δ>0,∀(c : ℕ)(w x y : ℝ)(B C : Set ℝ),
      MeasurableSet B→MeasurableSet C→Icc x (y*(1+ε))⊆B→
      Icc ((1-ξ)*x) ((1-ξ)*(y*(1+ε)))⊆C→
      |w| ≤ W→l ≤ x→x*(1+ε) ≤ U→x*(1+ε) ≤ w→x<y→(y-x)*(1+ε)<δ→
      (∫ω : Fin (N+1)→RowRival,literalSmoothedRowPayoff ξ ε c w x ω-
        literalSmoothedRowPayoff ξ ε c w y ω
        ∂Measure.pi (fun _ : Fin (N+1)=>rivalLaw s a h (realLowLaw mu))) ≤
      ((2*(1-ξ)-1)*U)*(N+1:ℕ)*s*((realLowLaw mu).real B+(realLowLaw mu).real C)*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum (realLowLaw mu)) N).prob (BothUnderflow c)+
        2*(1-ξ)*((y-x)*(1+ε))+e := by
  intro e he
  obtain ⟨δ,hδ,hraw⟩:=expected_patternPayoff_uniform_raise (N:=N) hξ hξh hl hlU hW
    s a h hs ha hh hsum mu e he
  refine ⟨δ,hδ,?_⟩
  intro c w x y B C hB hC hcoverB hcoverC hw hlx hxU hxw hxy hdist
  have hξ1 : ξ<1:=by linarith
  have hx : 0<x:=hl.trans_le hlx
  have hy : 0<y:=hx.trans hxy
  have hκ : 0 ≤ 1-ξ:=by linarith
  let ν:=Measure.pi (fun _ : Fin (N+1)=>rivalLaw s a h (realLowLaw mu))
  letI : IsProbabilityMeasure (rivalLaw s a h (realLowLaw mu)):=
    rivalLaw_isProbability s a h hs ha hh hsum (realLowLaw mu)
  rw [integral_literalSmoothed_sub hξ hξ1 ε c w x y ν]
  have hi:=(integrable_literal_noisyRow hξ hξ1 ε c w x ν).sub
    (integrable_literal_noisyRow hξ hξ1 ε c w y ν)
  have hbound:=integral_mono_ae hi.integral_prod_right (integrable_const
      (((2*(1-ξ)-1)*U)*(N+1:ℕ)*s*((realLowLaw mu).real B+(realLowLaw mu).real C)*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum (realLowLaw mu)) N).prob (BothUnderflow c)+
        2*(1-ξ)*((y-x)*(1+ε))+e)) (by
    filter_upwards [uniformNoise_support] with z hz
    have hn0 : 1 ≤ 1+ε*z:=by nlinarith [mul_nonneg hε hz.1]
    have hn1 : 1+ε*z ≤ 1+ε:=by
      have hh:=mul_le_mul_of_nonneg_left hz.2 hε
      linarith
    have hx0 : x ≤ x*(1+ε*z):=by nlinarith
    have hx1 : x*(1+ε*z) ≤ x*(1+ε):=mul_le_mul_of_nonneg_left hn1 hx.le
    have hy1 : y*(1+ε*z) ≤ y*(1+ε):=mul_le_mul_of_nonneg_left hn1 hy.le
    have hgap : (y-x)*(1+ε*z) ≤ (y-x)*(1+ε):=
      mul_le_mul_of_nonneg_left hn1 (sub_nonneg.mpr hxy.le)
    have hinc : x*(1+ε*z)<y*(1+ε*z):=mul_lt_mul_of_pos_right hxy (by linarith)
    have hcover₀ : Icc (x*(1+ε*z)) (y*(1+ε*z))⊆B :=
      fun t ht=>hcoverB ⟨hx0.trans ht.1,ht.2.trans hy1⟩
    have hcover₁ : Icc ((1-ξ)*(x*(1+ε*z))) ((1-ξ)*(y*(1+ε*z)))⊆C :=
      fun t ht=>hcoverC ⟨(mul_le_mul_of_nonneg_left hx0 hκ).trans ht.1,
        ht.2.trans (mul_le_mul_of_nonneg_left hy1 hκ)⟩
    have hh:=hraw c w (x*(1+ε*z)) (y*(1+ε*z)) B C hB hC hcover₀ hcover₁ hw
      (hlx.trans hx0) (hx1.trans hxU) (hx1.trans hxw) hinc (by nlinarith)
    change _ ≤ _
    have hprice:=mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2*(1-ξ))
    dsimp only [ν] at *
    simp only [Pi.sub_apply]
    nlinarith)
  simpa only [Pi.sub_apply,integral_const,probReal_univ,smul_eq_mul,one_mul] using hbound

end FCAppendix.Affine.LowBody
