import FCAppendix.Affine.Hybrid.RankReciprocalSampling

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Classical
open scoped BigOperators

def reciprocalMean (G : Measure ℝ) : ℝ := ∫ b, b⁻¹ ∂G

lemma integrable_reciprocal_of_box (G : Measure ℝ) [IsProbabilityMeasure G]
    {L U : ℝ} (hL : 0 < L) (hbox : ∀ᵐ b ∂G, b ∈ Icc L U) :
    Integrable (fun b : ℝ => b⁻¹) G := by
  apply Integrable.of_bound measurable_inv.aestronglyMeasurable (1/L)
  filter_upwards [hbox] with b hb
  rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hL.trans_le hb.1).le)]
  exact (reciprocal_box_bounds hL hb).2

lemma reciprocalMean_bounds (G : Measure ℝ) [IsProbabilityMeasure G]
    {L U : ℝ} (hL : 0 < L) (hbox : ∀ᵐ b ∂G, b ∈ Icc L U) :
    1/U ≤ reciprocalMean G ∧ reciprocalMean G ≤ 1/L := by
  have hi := integrable_reciprocal_of_box G hL hbox
  constructor
  · have hh := integral_mono_ae (integrable_const (1/U)) hi
      (hbox.mono (fun b hb => (reciprocal_box_bounds hL hb).1))
    simpa only [integral_const,probReal_univ,one_smul,reciprocalMean] using hh
  · have hh := integral_mono_ae hi (integrable_const (1/L))
      (hbox.mono (fun b hb => (reciprocal_box_bounds hL hb).2))
    simpa only [integral_const,probReal_univ,one_smul,reciprocalMean] using hh

lemma harmonic_stability {H H' U g g' : ℝ}
    (hU : 0 < U) (hH : 1/U ≤ H) (hH' : 1/U ≤ H') (hg' : |g'| ≤ 1) :
    |g/H-g'/H'| ≤ U*|g-g'|+U^2*|H-H'| := by
  have hH0 : 0 < H := (one_div_pos.mpr hU).trans_le hH
  have hH'0 : 0 < H' := (one_div_pos.mpr hU).trans_le hH'
  have hiH : 1/H ≤ U := by
    have hh := one_div_le_one_div_of_le (one_div_pos.mpr hU) hH
    simpa using hh
  have hiH' : 1/H' ≤ U := by
    have hh := one_div_le_one_div_of_le (one_div_pos.mpr hU) hH'
    simpa using hh
  have hid : g/H-g'/H' = (g-g')/H+g'*(H'-H)/(H*H') := by
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |(g-g')/H|+|g'*(H'-H)/(H*H')| := abs_add_le _ _
    _ = |g-g'| *(1/H)+|g'| *|H-H'| *((1/H)*(1/H')) := by
      rw [abs_div,abs_div,abs_mul,abs_mul,abs_of_pos hH0,
        abs_of_pos hH'0,abs_sub_comm H' H]
      field_simp
    _ ≤ |g-g'| *U+1*|H-H'| *(U*U) := by gcongr
    _ = _ := by ring

lemma subset_reciprocalMean_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L U : ℝ} (hL : 0 < L) (b : ι → ℝ) (hb : ∀ i, b i ∈ Icc L U)
    (D : Finset ι) (hD : D.Nonempty) :
    1/U ≤ (∑ i ∈ D, (b i)⁻¹)/(D.card : ℝ) ∧
    (∑ i ∈ D, (b i)⁻¹)/(D.card : ℝ) ≤ 1/L := by
  have hc : (0:ℝ) < D.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
  constructor
  · apply (le_div_iff₀ hc).2
    have hh := Finset.sum_le_sum (s := D) (fun i _ => (reciprocal_box_bounds hL (hb i)).1)
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh
  · apply (div_le_iff₀ hc).2
    have hh := Finset.sum_le_sum (s := D) (fun i _ => (reciprocal_box_bounds hL (hb i)).2)
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh

lemma finiteMultiplier_eq_factor_div_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (xi : ℝ) (b : ι → ℝ) (D : Finset ι) (r : ℕ) (hD : D.Nonempty) :
    finiteMultiplier xi b D r = finiteReceiptFactor xi D.card r /
      ((∑ i ∈ D, (b i)⁻¹)/(D.card : ℝ)) := by
  have hc : (D.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hD)
  unfold finiteMultiplier finiteReceiptFactor
  field_simp

theorem finiteMultiplier_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {L U h0 : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (hbox : ∀ᵐ b ∂G, b ∈ Icc L U) (hh0 : |h0| ≤ 1)
    (xi : ℝ) (b : ι → ℝ) (hb : ∀ i, b i ∈ Icc L U)
    (D : Finset ι) (r : ℕ) (hD : D.Nonempty) :
    |finiteMultiplier xi b D r-h0/reciprocalMean G| ≤
      U*|finiteReceiptFactor xi D.card r-h0|+
      U^2*|(∑ i ∈ D, (b i)⁻¹)/(D.card : ℝ)-reciprocalMean G| := by
  rw [finiteMultiplier_eq_factor_div_mean xi b D r hD]
  exact harmonic_stability (hL.trans_le hLU)
    (subset_reciprocalMean_bounds hL b hb D hD).1
    (reciprocalMean_bounds G hL hbox).1 hh0

lemma exposure_difference_bound {xi L b lam lam' : ℝ} (hxi : 0 < xi)
    (hL : 0 < L) (hb : L ≤ b) :
    |exposure xi lam b-exposure xi lam' b| ≤ |lam-lam'|/(xi*L) := by
  have hb0 : 0 < b := hL.trans_le hb
  have he : exposure xi lam b-exposure xi lam' b = -(lam-lam')/(xi*b) := by
    unfold exposure
    field_simp
    ring
  rw [he,abs_div,abs_neg,abs_of_pos (mul_pos hxi hb0)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hxi hL)
    (mul_le_mul_of_nonneg_left hb hxi.le)

end FCAppendix.Affine.Hybrid
