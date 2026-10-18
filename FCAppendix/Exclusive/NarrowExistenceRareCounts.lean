import FCAppendix.Exclusive.NarrowExistenceNeighborhood
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory Set

theorem integral_curvature_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → ℝ)
    (hK : Integrable K μ) (E : Set Ω) (hE : MeasurableSet E)
    (kappa B : ℝ) (hbound : ∀ᵐ x ∂μ, |K x| ≤ B)
    (hgood : ∀ᵐ x ∂μ, x ∈ E → kappa ≤ K x) :
    kappa-(kappa+B)*μ.real Eᶜ ≤ ∫ x, K x ∂μ := by
  have hi := ((integrable_const (μ := μ) kappa).sub
    ((integrable_const (μ := μ) (kappa+B)).indicator hE.compl))
  have h := integral_mono_ae hi hK (by
    filter_upwards [hbound, hgood] with x hb hg
    change kappa-Eᶜ.indicator (fun _ => kappa+B) x ≤ K x
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_notMem (show x ∉ Eᶜ from fun hc => hc hx), sub_zero]
      exact hg hx
    · simp only [Set.indicator_of_mem (show x ∈ Eᶜ from hx)]
      linarith [(abs_le.mp hb).1])
  change (∫ x, kappa-Eᶜ.indicator (fun _ => kappa+B) x ∂μ) ≤ (∫ x, K x ∂μ) at h
  rw [integral_sub (integrable_const kappa)
    ((integrable_const (kappa+B)).indicator hE.compl), integral_indicator_const _ hE.compl,
    smul_eq_mul] at h
  simpa only [integral_const, probReal_univ, one_smul, mul_comm] using h

theorem integral_influence_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K C : Ω → ℝ)
    (hK : Integrable K μ) (hC : Integrable C μ)
    (E : Set Ω) (hE : MeasurableSet E)
    (a B : ℝ) (ha : 0 ≤ a)
    (hKbound : ∀ᵐ x ∂μ, |K x| ≤ B) (hCbound : ∀ᵐ x ∂μ, |C x| ≤ B)
    (hgood : ∀ᵐ x ∂μ, x ∈ E → |C x| ≤ a*K x) :
    (∫ x, |C x| ∂μ) ≤ a*(∫ x, K x ∂μ)+(1+a)*B*μ.real Eᶜ := by
  have hi := (integrable_const (μ := μ) ((1+a)*B)).indicator hE.compl
  have h := integral_mono_ae (hC.abs.sub (hK.const_mul a)) hi (by
    filter_upwards [hKbound, hCbound, hgood] with x hk hc hg
    change |C x|-a*K x ≤ Eᶜ.indicator (fun _ => (1+a)*B) x
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_notMem (show x ∉ Eᶜ from fun hc => hc hx)]
      linarith [hg hx]
    · simp only [Set.indicator_of_mem (show x ∈ Eᶜ from hx)]
      have hl := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hk) ha
      nlinarith)
  change (∫ x, |C x|-a*K x ∂μ) ≤ (∫ x, Eᶜ.indicator (fun _ => (1+a)*B) x ∂μ) at h
  rw [integral_sub hC.abs (hK.const_mul a), integral_const_mul,
    integral_indicator_const _ hE.compl, smul_eq_mul] at h
  nlinarith only [h]

theorem averaged_curvature_contracts {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K C : Ω → ℝ)
    (hK : Integrable K μ) (hC : Integrable C μ)
    (E : Set Ω) (hE : MeasurableSet E)
    (kappa B : ℝ) (hkappa : 0 < kappa) (hB : 0 ≤ B)
    (hKbound : ∀ᵐ x ∂μ, |K x| ≤ B) (hCbound : ∀ᵐ x ∂μ, |C x| ≤ B)
    (hgoodK : ∀ᵐ x ∂μ, x ∈ E → kappa ≤ K x)
    (hgoodC : ∀ᵐ x ∂μ, x ∈ E → |C x| ≤ (3/4:ℝ)*K x)
    (hrare : 32*(kappa+B)*μ.real Eᶜ ≤ kappa) :
    kappa/2 ≤ (∫ x, K x ∂μ) ∧
      (∫ x, |C x| ∂μ) ≤ (7/8:ℝ)*(∫ x, K x ∂μ) := by
  have hlo := integral_curvature_lower μ K hK E hE kappa B hKbound hgoodK
  have hup := integral_influence_upper μ K C hK hC E hE (3/4:ℝ) B
    (by norm_num) hKbound hCbound hgoodC
  have hp : 0 ≤ μ.real Eᶜ := measureReal_nonneg
  have hkp : 0 ≤ kappa*μ.real Eᶜ := mul_nonneg hkappa.le hp
  have hbp : 0 ≤ B*μ.real Eᶜ := mul_nonneg hB hp
  constructor <;> nlinarith

theorem integral_good_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (E : Set Ω) (hE : MeasurableSet E) (a B : ℝ) (ha : 0 ≤ a)
    (hbound : ∀ᵐ x ∂μ, f x ≤ B) (hgood : ∀ᵐ x ∂μ, x ∈ E → f x ≤ a) :
    (∫ x, f x ∂μ) ≤ a+B*μ.real Eᶜ := by
  have hi := (integrable_const (μ := μ) a).add
    ((integrable_const (μ := μ) B).indicator hE.compl)
  have h := integral_mono_ae hf hi (by
    filter_upwards [hbound, hgood] with x hb hg
    change f x ≤ a+Eᶜ.indicator (fun _ => B) x
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_notMem (show x ∉ Eᶜ from fun hc => hc hx), add_zero]
      exact hg hx
    · simp only [Set.indicator_of_mem (show x ∈ Eᶜ from hx)]
      linarith)
  change (∫ x, f x ∂μ) ≤ (∫ x, a+Eᶜ.indicator (fun _ => B) x ∂μ) at h
  rw [integral_add (integrable_const a) ((integrable_const B).indicator hE.compl),
    integral_const, integral_indicator_const _ hE.compl, smul_eq_mul] at h
  simpa only [probReal_univ, one_smul, smul_eq_mul, mul_one, mul_comm] using h

theorem averaged_reference_contracts {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K C : Ω → ℝ)
    (hK : Integrable K μ) (hC : Integrable C μ)
    (E : Set Ω) (hE : MeasurableSet E)
    (K0 B : ℝ) (hK0 : 0 < K0)
    (hKbound : ∀ᵐ x ∂μ, |K x| ≤ B) (hCbound : ∀ᵐ x ∂μ, |C x| ≤ B)
    (hgoodK : ∀ᵐ x ∂μ, x ∈ E → (11/12:ℝ)*K0 ≤ K x)
    (hgoodC : ∀ᵐ x ∂μ, x ∈ E → |C x| ≤ (17/24:ℝ)*K0)
    (hrare : 24*(K0+B)*μ.real Eᶜ ≤ K0) :
    (7/8:ℝ)*K0 ≤ (∫ x, K x ∂μ) ∧
      (∫ x, |C x| ∂μ) ≤ (3/4:ℝ)*K0 := by
  have hlo := integral_curvature_lower μ K hK E hE ((11/12:ℝ)*K0) B hKbound hgoodK
  have hup := integral_good_upper μ (fun x => |C x|) hC.abs E hE
    ((17/24:ℝ)*K0) B (by positivity) hCbound hgoodC
  have hp : 0 ≤ μ.real Eᶜ := measureReal_nonneg
  have hkp := mul_nonneg hK0.le hp
  constructor <;> nlinarith

end FCAppendix.Exclusive.Narrow.Existence
