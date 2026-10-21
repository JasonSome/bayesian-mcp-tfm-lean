import FCAppendix.Affine.Uniform06.FixedPriceCanonicalIntegral
import FCAppendix.Affine.Uniform06.RawTiltedSource

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.DerivativeUntilting

open MeasureTheory ProbabilityTheory Set LowBody
open scoped BigOperators
open Uniform07 RawMixedSource RawTiltedSource ExactUntilting
open LiteralExperiment LiteralCoarsePath FixedPriceCanonicalRows FixedPriceCanonicalIntegral

theorem source_canonical_derivative_untilt (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (θ : ℝ) :
    Cprime i m G g cm b=
      Real.exp (-cost (source i G) (demand (xi i) b) θ (capacity m) (m-1))*
        ∫ ω : Fin (m-1) → RowRival,
          Real.exp (-θ*deficit i b (capacity m) ω)*
            rowVelocity (xi i) (capacity m) g cm 1 b ω
              ∂Measure.pi (fun _ => tiltedSource i G b θ) ∧
    Rprime i m G g cm b=
      Real.exp (-cost (source i G) (demand (xi i) b) θ (capacity m) (m-1))*
        ∫ ω : Fin (m-1) → RowRival,
          Real.exp (-θ*deficit i b (capacity m) ω)*
            rowVelocity (xi i) (capacity m) g cm 2 b ω
              ∂Measure.pi (fun _ => tiltedSource i G b θ) := by
  constructor
  · exact iid_reverse_tilt (source i G) (measurable_demand _ _)
      (ae_of_all _ (demand_bounds (xi_pos i) hb)) θ (capacity m) (m-1) _
  · exact iid_reverse_tilt (source i G) (measurable_demand _ _)
      (ae_of_all _ (demand_bounds (xi_pos i) hb)) θ (capacity m) (m-1) _

theorem same_finite_factor_all_four (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (θ : ℝ) :
    let A := Real.exp (-cost (source i G) (demand (xi i) b) θ (capacity m) (m-1))
    let P := Measure.pi (fun _ : Fin (m-1) => tiltedSource i G b θ)
    let e := fun ω : Fin (m-1) → RowRival => Real.exp (-θ*deficit i b (capacity m) ω)
    sourceCanonicalMarginal i m G g cm b=
      A*(∫ ω,e ω*originalRowMarginal (xi i) (capacity m) g cm b ω ∂P) ∧
    sourceCanonicalDuplicate i m G g cm b=
      A*(∫ ω,e ω*originalRowDuplicate (xi i) (capacity m) g cm b ω ∂P) ∧
    Cprime i m G g cm b=A*(∫ ω,e ω*rowVelocity (xi i) (capacity m) g cm 1 b ω ∂P) ∧
    Rprime i m G g cm b=A*(∫ ω,e ω*rowVelocity (xi i) (capacity m) g cm 2 b ω ∂P) := by
  exact ⟨source_canonical_marginal_untilt i m G g cm hb θ,
    source_canonical_duplicate_untilt i m G g cm hb θ,
    source_canonical_derivative_untilt i m G g cm hb θ⟩

theorem every_fixed_value_likelihood {V Z : Type*} [MeasurableSpace V] [MeasurableSpace Z]
    (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (K : V → Measure Z) (markSum : Z → ℝ)
    {b : ℝ} (hb : 0< b) (θ cap : ℝ) (N k : ℕ)
    (F : Z → (Fin N → RowRival) → ℝ) :
    ∀ v : V,
      (∫ z,(∫ ω,F z ω ∂Measure.pi (fun _ : Fin N => source i G)) ∂K v)=
        ∫ z,Real.exp (-cost (source i G) (demand (xi i) b) θ cap (N+k))*
          Real.exp (-θ*markSum z-(k:ℝ)*cgf (demand (xi i) b) (source i G) (-θ))*
            (∫ ω,Real.exp (-θ*deficit i b (cap-markSum z) ω)*F z ω
              ∂Measure.pi (fun _ : Fin N => tiltedSource i G b θ)) ∂K v := by
  intro v
  apply integral_congr_ae
  exact ae_of_all _ fun z => original_fixed_marks_untilt i G hb θ cap (markSum z) N k (F z)

end FCAppendix.Affine.Uniform06.DerivativeUntilting
