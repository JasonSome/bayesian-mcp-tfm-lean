import FCAppendix.Affine.Hybrid.PointwiseFiniteMenu
import FCAppendix.Affine.Hybrid.FavoredInterimJump

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Classical
open scoped BigOperators

lemma integral_abs_sub_le_of_ae_bound {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P] (f Q : α → ℝ) (a C D : ℝ)
    (hf : AEStronglyMeasurable f P) (hQi : Integrable Q P)
    (hp : ∀ᵐ x ∂P, |f x-a| ≤ C*Q x+D) :
    |(∫ x, f x ∂P)-a| ≤ C*(∫ x, Q x ∂P)+D := by
  have hdom : Integrable (fun x => C*Q x+D) P := (hQi.const_mul C).add (integrable_const D)
  have hdiff : Integrable (fun x => f x-a) P := hdom.mono'
    (hf.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using hp)
  have hfi : Integrable f P := by
    have he : (fun x => f x-a+a)=f := by funext x; ring
    exact he ▸ hdiff.add (integrable_const a)
  have he : (∫ x, f x-a ∂P)=(∫ x, f x ∂P)-a := by
    rw [integral_sub hfi (integrable_const a),integral_const,probReal_univ,one_smul]
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  have hh := integral_mono_ae hdiff.abs hdom hp
  rwa [integral_add (hQi.const_mul C) (integrable_const D),integral_const_mul,
    integral_const,probReal_univ,one_smul] at hh

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma integrable_favoredMultiplierError (G : Measure ℝ) [IsProbabilityMeasure G]
    {L U b : ℝ} (hL : 0 < L) (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hb : b ∈ Icc L U)
    (xi h0 H : ℝ) (r K : ℕ) (i : ι) :
    Integrable (fun x : ι → ℝ => favoredMultiplierError xi h0 H (Function.update x i b) r K)
      (Measure.pi (fun _ : ι => G)) := by
  unfold favoredMultiplierError
  simp only [favoredSetLaw,FiniteLaw.expect_finiteMix]
  apply integrable_rank_expect _ _ (measurable_fixedFocalRow i b)
  intro t
  apply integrable_finsetSum
  intro E _
  exact (((integrable_fixed_focal_multiplier G hL hbox hb xi (Finset.univ \ E) r i).sub
    (integrable_const _)).abs).const_mul _

omit [Nonempty ι] in
lemma measurable_ownerSetSingletonPayoff (xi v : ℝ) (r : ℕ) (i : ι) (E : Finset ι) :
    Measurable (fun b : ι → ℝ => ownerSetSingletonPayoff xi v b r i E) := by
  by_cases hi : i∈E
  · simp only [ownerSetSingletonPayoff,if_pos hi]
    exact (measurable_const.sub (measurable_pi_apply i)).div_const 2
  · have hq : Measurable (fun b : ι → ℝ => exposure xi
        (finiteMultiplier xi b (Finset.univ \ E) r) (b i)) :=
      (measurable_const.sub ((measurable_finiteMultiplier xi (Finset.univ \ E) r).div
        (measurable_pi_apply i))).div_const xi
    simp only [ownerSetSingletonPayoff,if_neg hi]
    exact (measurable_const.sub (measurable_pi_apply i)).mul hq

lemma measurable_sourceSingletonPayoff (xi v : ℝ) (r K1 K2 : ℕ) (i : ι) :
    Measurable (fun b : ι → ℝ => sourceSingletonPayoff xi v b r K1 K2 i) := by
  unfold sourceSingletonPayoff FiniteLaw.expect
  exact Finset.measurable_sum _ (fun AB _ =>
    (measurable_sourceOwnersLaw_mass K1 K2 AB).mul
      (measurable_ownerSetSingletonPayoff xi v r i (AB.1∪AB.2)))

def finiteHarmonicError (xi L U h0 : ℝ) (A K r : ℕ) : ℝ :=
  U*|finiteReceiptFactor xi (A-K) r-h0|+
    U^2*(2*((1/L)/Real.sqrt ((A-K : ℕ) : ℝ)+(1/L)/(A-K : ℕ)))

theorem sourceOwnerPayoff_interim_error (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi eta L U h0 z v W b : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hb : b ∈ Icc L U)
    (hh0 : 0 ≤ h0) (hh01 : |h0| ≤ 1)
    (h0lo : (1-xi)*U < h0*L) (h0hi : h0*U < L) (hv : |v| ≤ W)
    (r K1 K2 : ℕ) (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K1+K2)
    (hKN : K1+K2 < Fintype.card ι)
    (hg : 0 ≤ finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r)
    (hglo : (1-xi)*U < finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r*L)
    (hghi : finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r*U < L) (i : ι) :
    |(∫ x : ι → ℝ, sourceOwnerPayoff xi eta v (Function.update x i b) r K1 K2 i
      ∂Measure.pi (fun _ : ι => G))-
      (z*(v-b)+(1-z)*independentTwo eta v b (exposure xi (h0/reciprocalMean G) b))| ≤
      (broadcastExposureModulus eta W U/(xi*L))*finiteHarmonicError xi L U h0 (Fintype.card ι) (K1+K2) r+
      (W+U+broadcastExposureModulus eta W U)*
        (1/(Fintype.card ι : ℝ)+|((K1+K2 : ℕ) : ℝ)/(Fintype.card ι : ℝ)-z|) := by
  let P := Measure.pi (fun _ : ι => G)
  let Q : (ι → ℝ) → ℝ := fun x => favoredMultiplierError xi h0 (reciprocalMean G)
    (Function.update x i b) r (K1+K2)
  have hQi : Integrable Q P := integrable_favoredMultiplierError G hL hbox hb _ _ _ _ _ i
  have hp : ∀ᵐ x ∂P, |sourceOwnerPayoff xi eta v (Function.update x i b) r K1 K2 i-
      (z*(v-b)+(1-z)*independentTwo eta v b (exposure xi (h0/reciprocalMean G) b))| ≤
      (broadcastExposureModulus eta W U/(xi*L))*Q x+
      (W+U+broadcastExposureModulus eta W U)*
        (1/(Fintype.card ι : ℝ)+|((K1+K2 : ℕ) : ℝ)/(Fintype.card ι : ℝ)-z|) := by
    filter_upwards [ae_fixedFocalRow_box G hbox hb i] with x hx
    simpa only [Function.update_self] using sourceOwnerPayoff_menu_error G hxi hxi1 hL hbox
      hh0 h0lo h0hi hv (Function.update x i b) hx r K1 K2 hN hK hKN hg hglo hghi i
  have hh := integral_abs_sub_le_of_ae_bound P _ Q _ _ _
    (((measurable_sourceOwnerPayoff xi eta v r K1 K2 i).comp
      (measurable_fixedFocalRow i b)).aestronglyMeasurable) hQi hp
  have hQ := favored_multiplier_L1 G hL hbox hb hh01 xi r (K1+K2) hN hK hKN i
  have hC : 0 ≤ broadcastExposureModulus eta W U/(xi*L) :=
    div_nonneg (broadcastExposureModulus_nonneg ((abs_nonneg _).trans hv)
      (hL.trans_le (hb.1.trans hb.2)).le) (mul_pos hxi hL).le
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hQ hC) le_rfl)

theorem sourceSingletonPayoff_interim_error (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi L U h0 z v W b : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hb : b ∈ Icc L U)
    (hh0 : 0 ≤ h0) (hh01 : |h0| ≤ 1)
    (h0lo : (1-xi)*U < h0*L) (h0hi : h0*U < L) (hv : |v| ≤ W)
    (r K1 K2 : ℕ) (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K1+K2)
    (hKN : K1+K2 < Fintype.card ι)
    (hg : 0 ≤ finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r)
    (hglo : (1-xi)*U < finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r*L)
    (hghi : finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r*U < L) (i : ι) :
    |(∫ x : ι → ℝ, sourceSingletonPayoff xi v (Function.update x i b) r K1 K2 i
      ∂Measure.pi (fun _ : ι => G))-
      ((z/2+(1-z)*exposure xi (h0/reciprocalMean G) b)*(v-b))| ≤
      ((W+U)/(xi*L))*finiteHarmonicError xi L U h0 (Fintype.card ι) (K1+K2) r+
      (W+U)*(1/(Fintype.card ι : ℝ)+|((K1+K2 : ℕ) : ℝ)/(Fintype.card ι : ℝ)-z|) := by
  let P := Measure.pi (fun _ : ι => G)
  let Q : (ι → ℝ) → ℝ := fun x => favoredMultiplierError xi h0 (reciprocalMean G)
    (Function.update x i b) r (K1+K2)
  have hQi : Integrable Q P := integrable_favoredMultiplierError G hL hbox hb _ _ _ _ _ i
  have hp : ∀ᵐ x ∂P, |sourceSingletonPayoff xi v (Function.update x i b) r K1 K2 i-
      ((z/2+(1-z)*exposure xi (h0/reciprocalMean G) b)*(v-b))| ≤
      ((W+U)/(xi*L))*Q x+
      (W+U)*(1/(Fintype.card ι : ℝ)+|((K1+K2 : ℕ) : ℝ)/(Fintype.card ι : ℝ)-z|) := by
    filter_upwards [ae_fixedFocalRow_box G hbox hb i] with x hx
    simpa only [Function.update_self] using sourceSingletonPayoff_menu_error G hxi hxi1 hL hbox
      hh0 h0lo h0hi hv (Function.update x i b) hx r K1 K2 hN hK hKN hg hglo hghi i
  have hh := integral_abs_sub_le_of_ae_bound P _ Q _ _ _
    (((measurable_sourceSingletonPayoff xi v r K1 K2 i).comp
      (measurable_fixedFocalRow i b)).aestronglyMeasurable) hQi hp
  have hQ := favored_multiplier_L1 G hL hbox hb hh01 xi r (K1+K2) hN hK hKN i
  have hC : 0 ≤ (W+U)/(xi*L) := div_nonneg
    (add_nonneg ((abs_nonneg _).trans hv) (hL.trans_le (hb.1.trans hb.2)).le) (mul_pos hxi hL).le
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hQ hC) le_rfl)

end FCAppendix.Affine.Hybrid
