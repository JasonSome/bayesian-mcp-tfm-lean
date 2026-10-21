import FCAppendix.Affine.Uniform06.FixedPriceCanonicalIntegral

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceCanonicalRegularity

open MeasureTheory Set LowBody
open Uniform07 LiteralExperiment LiteralKernelDecomposition
open LiteralPrefixStieltjes CanonicalPrefixLipschitz FixedPriceCanonicalIntegral

theorem source_canonical_nonnegative (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) :
    0 ≤ sourceCanonicalMarginal i m G g cm b ∧
      0 ≤ sourceCanonicalDuplicate i m G g cm b := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  constructor
  · change 0 ≤ ∫ ω : Fin (m-1) → RowRival,
      rowCanonicalFair (xi i) (capacity m) g cm b ω
        ∂Measure.pi (fun _ => rivalLaw (cutoff i) 0 (1-cutoff i) (G.map Prod.snd))
    exact integral_nonneg fun ω =>
      (row_canonical_bounds (xi_pos i) hξ1 (capacity m) g cm b ω).2.1.1
  · change 0 ≤ ∫ ω : Fin (m-1) → RowRival,
      rowCanonicalDuplicate (xi i) (capacity m) g cm b ω
        ∂Measure.pi (fun _ => rivalLaw (cutoff i) 0 (1-cutoff i) (G.map Prod.snd))
    exact integral_nonneg fun ω =>
      (row_canonical_bounds (xi_pos i) hξ1 (capacity m) g cm b ω).2.2.1

theorem source_canonical_monotone (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hfloor : ∀ᵐ p ∂G,LowChernoff.physicalFloor i p.1 ≤ p.2)
    (g : GuardData) {H : ℝ} (hg : PrefixConditions (xi i) g H)
    (cm : (Fin (m-1) → Fin 4) → ℝ) :
    MonotoneOn (sourceCanonicalMarginal i m G g cm) (Icc (0:ℝ) H) ∧
      MonotoneOn (sourceCanonicalDuplicate i m G g cm) (Icc (0:ℝ) H) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hS := source_canonical_first_monotone i m G hfloor g hg cm
  have hR : MonotoneOn (sourceCanonicalDuplicate i m G g cm) (Icc (0:ℝ) H) :=
    actual_canonical_duplicate_monotone (cutoff_mem i) (xi_pos i)
      (by cases i <;> norm_num [xi,xiQ,etaQ]) (G.map Prod.snd)
      (EqualCanonicalRegularity.source_floor_bid_nonnegative i G hfloor)
      (capacity m) g hg cm
  refine ⟨?_,hR⟩
  intro x hx y hy hxy
  have hs := hS hx hy hxy
  have hr := hR hx hy hxy
  linarith

theorem source_canonical_lipschitz (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hfloor : ∀ᵐ p ∂G,LowChernoff.physicalFloor i p.1 ≤ p.2)
    (g : GuardData) {H a : ℝ} (hg : PrefixConditions (xi i) g H)
    (hH : 0 ≤ H) (ha : 0 < a) (cm : (Fin (m-1) → Fin 4) → ℝ) :
    LipschitzOnWith (Real.nnabs (canonicalConstant (xi i) g H/a))
      (sourceCanonicalMarginal i m G g cm) (Icc a H) := by
  have hK := (canonicalConstant_pos (xi_pos i) hH hg).le
  have hmono := (source_canonical_monotone i m G hfloor g hg cm).1
  apply lipschitz_of_ordered_increments _ _ (div_nonneg hK ha.le)
  intro x hx y hy hxy
  have hx0 := ha.trans_le hx.1
  have hi := source_canonical_increments i m G hfloor g hg cm hx0 hxy hy.2
  have he := div_le_div_of_nonneg_left
    (mul_nonneg hK (sub_nonneg.mpr hxy)) ha hx.1
  have he' : canonicalConstant (xi i) g H*(y-x)/x ≤
      canonicalConstant (xi i) g H/a*(y-x) := by
    convert! he using 1
    ring
  refine ⟨sub_nonneg.mpr (hmono ⟨hx0.le,hx.2⟩
    ⟨(ha.trans_le hy.1).le,hy.2⟩ hxy),?_⟩
  linarith [hi.1.trans he',hi.2.trans he']

end FCAppendix.Affine.Uniform06.SourceCanonicalRegularity
