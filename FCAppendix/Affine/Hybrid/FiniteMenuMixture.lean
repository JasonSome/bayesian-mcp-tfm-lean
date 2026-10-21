import FCAppendix.Affine.Hybrid.HarmonicIntegration
import FCAppendix.Affine.Hybrid.MenuLipschitz
import FCAppendix.Affine.Hybrid.SingletonPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Classical
open scoped BigOperators

lemma finite_union_mixture_error {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (E : Ω → Prop) [DecidablePred E] (a f0 z beta C D : ℝ)
    (f err : Ω → ℝ) (hC : 0 ≤ C) (herr : ∀ t, 0 ≤ err t)
    (hdiff : ∀ t, P.mass t ≠ 0 → ¬ E t → |f t-f0| ≤ C*err t)
    (hbias : |P.prob E-z| ≤ beta) (hgain : |a-f0| ≤ D) :
    |P.expect (fun t => if E t then a else f t)-(z*a+(1-z)*f0)| ≤
      C*P.expect err+D*beta := by
  let Q := P.expect (fun t => if E t then a else f0)
  have hQ : Q = P.prob E*a+(1-P.prob E)*f0 := by
    have hp (t : Ω) : (if E t then a else f0)=
        (if E t then (1:ℝ) else 0)*a+(1-(if E t then (1:ℝ) else 0))*f0 := by
      split_ifs <;> ring
    simp only [Q,hp,FiniteLaw.expect_add,FiniteLaw.expect_mul_const,
      FiniteLaw.expect_sub,FiniteLaw.expect_const,←FiniteLaw.prob_eq_expect]
  have hfirst : |P.expect (fun t => if E t then a else f t)-Q| ≤ C*P.expect err := by
    rw [←FiniteLaw.expect_sub]
    apply (P.abs_expect_le _).trans
    rw [←FiniteLaw.expect_const_mul]
    apply expect_le_expect_on_support
    intro t ht
    by_cases he : E t
    · simp only [if_pos he,sub_self,abs_zero]
      exact mul_nonneg hC (herr t)
    · simp only [if_neg he]
      exact hdiff t ht he
  have hsecond : |Q-(z*a+(1-z)*f0)| ≤ D*beta := by
    have he : Q-(z*a+(1-z)*f0)=(a-f0)*(P.prob E-z) := by rw [hQ]; ring
    rw [he,abs_mul]
    exact mul_le_mul hgain hbias (abs_nonneg _) ((abs_nonneg _).trans hgain)
  have he : P.expect (fun t => if E t then a else f t)-(z*a+(1-z)*f0)=
      (P.expect (fun t => if E t then a else f t)-Q)+(Q-(z*a+(1-z)*f0)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma exposure_mem_of_finite_factor {xi L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (hL : 0 < L) (b : ι → ℝ) (hb : ∀ j, b j ∈ Icc L U)
    (D : Finset ι) (r : ℕ) (hD : D.Nonempty)
    (hg : 0 ≤ finiteReceiptFactor xi D.card r)
    (hlo : (1-xi)*U < finiteReceiptFactor xi D.card r*L)
    (hhi : finiteReceiptFactor xi D.card r*U < L) (i : ι) :
    exposure xi (finiteMultiplier xi b D r) (b i) ∈ Icc (0:ℝ) 1 := by
  have hh := finiteMultiplier_box_bounds hL b D hD r (fun j _ => hb j) hg
  apply Set.Ioo_subset_Icc_self
  apply exposure_mem_Ioo hxi (hL.trans_le (hb i).1)
  · exact (mul_le_mul_of_nonneg_left (hb i).2 (by linarith : 0 ≤ 1-xi)).trans_lt
      (hlo.trans_le hh.1)
  · exact hh.2.trans_lt (hhi.trans_le (hb i).1)

lemma exposure_mem_of_mean_factor (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi L U h0 b : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hb : b ∈ Icc L U) (hh0 : 0 ≤ h0)
    (hlo : (1-xi)*U < h0*L) (hhi : h0*U < L) :
    exposure xi (h0/reciprocalMean G) b ∈ Icc (0:ℝ) 1 := by
  have hU : 0 < U := hL.trans_le (hb.1.trans hb.2)
  have hH := reciprocalMean_bounds G hL hbox
  have hH0 : 0 < reciprocalMean G := (one_div_pos.mpr hU).trans_le hH.1
  have hlo' : h0*L ≤ h0/reciprocalMean G := by
    apply (le_div_iff₀ hH0).2
    have hh := mul_le_mul_of_nonneg_left hH.2 (mul_nonneg hh0 hL.le)
    have he : h0*L*(1/L)=h0 := by field_simp
    nlinarith only [hh,he]
  have hhi' : h0/reciprocalMean G ≤ h0*U := by
    apply (div_le_iff₀ hH0).2
    have hh := mul_le_mul_of_nonneg_left hH.1 (mul_nonneg hh0 hU.le)
    have he : h0*U*(1/U)=h0 := by field_simp
    nlinarith only [hh,he]
  apply Set.Ioo_subset_Icc_self
  apply exposure_mem_Ioo hxi (hL.trans_le hb.1)
  · exact (mul_le_mul_of_nonneg_left hb.2 (by linarith : 0 ≤ 1-xi)).trans_lt
      (hlo.trans_le hlo')
  · exact hhi'.trans_lt (hhi.trans_le hb.1)

lemma sourceOwnerPayoff_eq_favored [Nonempty ι] (xi eta v : ℝ) (b : ι → ℝ)
    (r K1 K2 : ℕ) (i : ι) (hN : 2 ≤ Fintype.card ι)
    (hK : 0 < K1+K2) (hKN : K1+K2 ≤ Fintype.card ι) :
    sourceOwnerPayoff xi eta v b r K1 K2 i=
      (favoredSetLaw b (K1+K2)).expect (ownerSetPayoff xi eta v b r i) :=
  sourceOwnersLaw_expect_union b K1 K2 hN hK hKN _

end FCAppendix.Affine.Hybrid
