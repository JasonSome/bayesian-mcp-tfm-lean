import FCAppendix.Affine.Hybrid.Tail03.Optimizer

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set
open scoped BigOperators

def failureCoeff (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  ∑ r,regimeWeight p r*e0 p r*(1-exposure p lam r b)^2/width p^2
def paymentCoeff (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  ∑ r,regimeWeight p r*e0 p r*
    (p.eta2*(exposure p lam r b)^2-(1-exposure p lam r b)^2)/width p^2
def exposure1 (p : Center) (lam : Fin 2 → ℝ) (r : Fin 2) (b : ℝ) : ℝ :=
  lam r/(xi p*b^2)
def failureCoeff1 (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  ∑ r,regimeWeight p r*e0 p r*
    (-2*(1-exposure p lam r b)*exposure1 p lam r b)/width p^2
def paymentCoeff1 (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  ∑ r,regimeWeight p r*e0 p r*
    (2*(p.eta2*exposure p lam r b+1-exposure p lam r b)*exposure1 p lam r b)/width p^2

lemma exposure_hasDerivAt (p : Center) (lam : Fin 2 → ℝ) (r : Fin 2)
    {b : ℝ} (hb : b≠0) :
    HasDerivAt (exposure p lam r) (exposure1 p lam r b) b := by
  have hi := (hasDerivAt_const b (lam r)).div (hasDerivAt_id b) hb
  convert! ((hasDerivAt_const b 1).sub hi).div_const (xi p) using 1
  all_goals dsimp [exposure,exposure1]
  all_goals field_simp [hb,(xi_pos p).ne']
  all_goals ring

lemma failureCoeff_hasDerivAt (p : Center) (lam : Fin 2 → ℝ)
    {b : ℝ} (hb : b≠0) :
    HasDerivAt (failureCoeff p lam) (failureCoeff1 p lam b) b := by
  unfold failureCoeff failureCoeff1
  convert! HasDerivAt.fun_sum (fun r (_ : r∈Finset.univ) =>
    ((((hasDerivAt_const b 1).sub (exposure_hasDerivAt p lam r hb)).pow 2).const_mul
      (regimeWeight p r*e0 p r)).div_const (width p^2)) using 1
  all_goals simp only [Fin.sum_univ_two, Pi.sub_apply]
  all_goals ring

lemma paymentCoeff_hasDerivAt (p : Center) (lam : Fin 2 → ℝ)
    {b : ℝ} (hb : b≠0) :
    HasDerivAt (paymentCoeff p lam) (paymentCoeff1 p lam b) b := by
  unfold paymentCoeff paymentCoeff1
  convert! HasDerivAt.fun_sum (fun r (_ : r∈Finset.univ) =>
    (((((exposure_hasDerivAt p lam r hb).pow 2).const_mul p.eta2).sub
      (((hasDerivAt_const b 1).sub (exposure_hasDerivAt p lam r hb)).pow 2)).const_mul
      (regimeWeight p r*e0 p r)).div_const (width p^2)) using 1
  all_goals simp only [Fin.sum_univ_two, Pi.sub_apply]
  all_goals ring

lemma exact_boundary_factorizations (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) :
    served p lam b=1-(B p-b)^2*failureCoeff p lam b ∧
      payment p lam b=b+b*(B p-b)^2*paymentCoeff p lam b := by
  constructor
  · simp only [served,mixedProb,failureCoeff,Fin.sum_univ_two]
    field_simp [(width_pos p).ne']
  · simp only [payment,served,duplicates,mixedProb,paymentCoeff,Fin.sum_univ_two]
    field_simp [(width_pos p).ne']
    all_goals ring

lemma exact_boundary_derivatives (p : Center) (lam : Fin 2 → ℝ)
    {b : ℝ} (hb : b≠0) :
    served1 p lam b=2*(B p-b)*failureCoeff p lam b-
        (B p-b)^2*failureCoeff1 p lam b ∧
      payment1 p lam b=1+((B p-b)^2-2*b*(B p-b))*paymentCoeff p lam b+
        b*(B p-b)^2*paymentCoeff1 p lam b := by
  have hy := (hasDerivAt_const b (B p)).sub (hasDerivAt_id b)
  have hs := (hasDerivAt_const b 1).sub
    ((hy.pow 2).mul (failureCoeff_hasDerivAt p lam hb))
  have ht := (hasDerivAt_id b).add
    (((hasDerivAt_id b).mul (hy.pow 2)).mul (paymentCoeff_hasDerivAt p lam hb))
  constructor
  · have hfun : (fun b => 1-(B p-b)^2*failureCoeff p lam b)=served p lam := by
      ext b
      exact (exact_boundary_factorizations p lam b).1.symm
    change HasDerivAt (fun b => 1-(B p-b)^2*failureCoeff p lam b) _ b at hs
    rw [hfun] at hs
    have hu := (served_hasDerivAt p lam hb).unique hs
    simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub] at hu
    nlinarith only [hu]
  · have hfun : (fun b => b+b*(B p-b)^2*paymentCoeff p lam b)=payment p lam := by
      ext b
      exact (exact_boundary_factorizations p lam b).2.symm
    change HasDerivAt (fun b => b+b*(B p-b)^2*paymentCoeff p lam b) _ b at ht
    rw [hfun] at ht
    have hu := (payment_hasDerivAt p lam hb).unique ht
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub] at hu
    nlinarith only [hu]

lemma failureCoeff_at_B (p : Center) (lam : Fin 2 → ℝ) :
    failureCoeff p lam (B p)=leadingA p lam := rfl

lemma failureCoeff1_nonpos (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) (lam : Fin 2 → ℝ)
    (hlam : lam∈rect.box) {b : ℝ} (hb : b∈Icc (1:ℝ) (B p)) :
    failureCoeff1 p lam b≤0 := by
  have hb0 : 0< b := by linarith [hb.1]
  unfold failureCoeff1
  apply Finset.sum_nonpos
  intro r _
  have hq := h.receipt.probabilities lam hlam r b hb
  have hl : 0< lam r := (rect.positive r).trans_le (hlam.1 r)
  have hq1 : 0< exposure1 p lam r b := by unfold exposure1; exact div_pos hl (by have := xi_pos p; positivity)
  have hprod : -2*(1-exposure p lam r b)*exposure1 p lam r b≤0 := by
    have hp : 0≤(1-exposure p lam r b)*exposure1 p lam r b :=
      mul_nonneg (by linarith [hq.2]) hq1.le
    nlinarith
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (regime_weights_positive p r) (e0_pos p r)).le hprod)
    (sq_nonneg _)

structure BoundaryCoefficientBounds (p : Center) (rect : Rectangle p)
    extends LeadingWindow p rect where
  C : ℝ
  C_ge_one : 1≤ C
  bound : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p),
    |failureCoeff1 p lam b|≤ C ∧ |paymentCoeff p lam b|≤ C ∧
      |paymentCoeff1 p lam b|≤ C ∧ |payment1 p lam b|≤ C
  failure_deriv_nonpos : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p), failureCoeff1 p lam b≤0
  failure_lower : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p), leadingA p lam≤ failureCoeff p lam b
  failure_lipschitz : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p),
    |failureCoeff p lam b-leadingA p lam|≤ C*(B p-b)

theorem boundary_coefficient_bounds (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) (W : LeadingWindow p rect) :
    Nonempty (BoundaryCoefficientBounds p rect) := by
  let K : Set ((Fin 2 → ℝ)×ℝ) := rect.box×ˢIcc (1:ℝ) (B p)
  have hK : IsCompact K := rect.isCompact_box.prod isCompact_Icc
  have hxi : 0< xi p := xi_pos p
  have hwidth : 0< width p := width_pos p
  have hcA : ContinuousOn (fun z : (Fin 2 → ℝ)×ℝ => failureCoeff1 p z.1 z.2) K := by
    intro z hz
    have hb : z.2≠0 := ne_of_gt (by linarith [hz.2.1])
    simp only [failureCoeff1, exposure, exposure1, Fin.sum_univ_two]
    fun_prop (disch := first | exact hb | positivity)
  have hcC : ContinuousOn (fun z : (Fin 2 → ℝ)×ℝ => paymentCoeff p z.1 z.2) K := by
    intro z hz
    have hb : z.2≠0 := ne_of_gt (by linarith [hz.2.1])
    simp only [paymentCoeff, exposure, Fin.sum_univ_two]
    fun_prop (disch := first | exact hb | positivity)
  have hcC1 : ContinuousOn (fun z : (Fin 2 → ℝ)×ℝ => paymentCoeff1 p z.1 z.2) K := by
    intro z hz
    have hb : z.2≠0 := ne_of_gt (by linarith [hz.2.1])
    simp only [paymentCoeff1, exposure, exposure1, Fin.sum_univ_two]
    fun_prop (disch := first | exact hb | positivity)
  have hcT : ContinuousOn (fun z : (Fin 2 → ℝ)×ℝ => payment1 p z.1 z.2) K := by
    intro z hz
    exact (derivative_continuity p z.1 z.2
      (ne_of_gt (by linarith [hz.2.1]))).2.2.1.continuousWithinAt
  obtain ⟨CA,hCA,hCAb⟩ := compact_abs_bound hK hcA
  obtain ⟨CC,hCC,hCCb⟩ := compact_abs_bound hK hcC
  obtain ⟨CC1,hCC1,hCC1b⟩ := compact_abs_bound hK hcC1
  obtain ⟨CT,hCT,hCTb⟩ := compact_abs_bound hK hcT
  let C := 1+CA+CC+CC1+CT
  have hC : 1≤ C := by dsimp [C]; linarith
  have hbound : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p),
      |failureCoeff1 p lam b|≤ C ∧ |paymentCoeff p lam b|≤ C ∧
        |paymentCoeff1 p lam b|≤ C ∧ |payment1 p lam b|≤ C := by
    intro lam hlam b hb
    refine ⟨?_,?_,?_,?_⟩
    · exact (hCAb (lam,b) ⟨hlam,hb⟩).trans (by dsimp [C]; linarith)
    · exact (hCCb (lam,b) ⟨hlam,hb⟩).trans (by dsimp [C]; linarith)
    · exact (hCC1b (lam,b) ⟨hlam,hb⟩).trans (by dsimp [C]; linarith)
    · exact (hCTb (lam,b) ⟨hlam,hb⟩).trans (by dsimp [C]; linarith)
  have hmean : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p),
      leadingA p lam≤ failureCoeff p lam b ∧
      |failureCoeff p lam b-leadingA p lam|≤ C*(B p-b) := by
    intro lam hlam b hb
    rcases hb.2.eq_or_lt with heq | hlt
    · simp [heq,failureCoeff_at_B]
    · obtain ⟨z,hz,hzd⟩ := exists_hasDerivAt_eq_slope (failureCoeff p lam)
        (failureCoeff1 p lam) hlt
        (fun z hz => (failureCoeff_hasDerivAt p lam
          (ne_of_gt (by linarith [hb.1,hz.1]))).continuousAt.continuousWithinAt)
        (fun z hz => failureCoeff_hasDerivAt p lam (ne_of_gt (by linarith [hb.1,hz.1])))
      have hzK : z∈Icc (1:ℝ) (B p) := ⟨hb.1.trans hz.1.le,hz.2.le⟩
      have hn := failureCoeff1_nonpos p rect h lam hlam hzK
      have habs := (hbound lam hlam z hzK).1
      have hy : 0< B p-b := sub_pos.mpr hlt
      rw [failureCoeff_at_B] at hzd
      have heq : leadingA p lam-failureCoeff p lam b=failureCoeff1 p lam z*(B p-b) :=
        (eq_div_iff hy.ne').mp hzd |>.symm
      constructor
      · have hh := mul_nonpos_of_nonpos_of_nonneg hn hy.le
        linarith
      · rw [abs_sub_comm,heq,abs_mul,abs_of_pos hy]
        exact mul_le_mul_of_nonneg_right habs hy.le
  exact ⟨{
    toLeadingWindow := W
    C := C
    C_ge_one := hC
    bound := hbound
    failure_deriv_nonpos := fun lam hlam b hb => failureCoeff1_nonpos p rect h lam hlam hb
    failure_lower := fun lam hlam b hb => (hmean lam hlam b hb).1
    failure_lipschitz := fun lam hlam b hb => (hmean lam hlam b hb).2 }⟩

end FCAppendix.Affine.Hybrid.Tail03
