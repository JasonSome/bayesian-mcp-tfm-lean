import FCAppendix.Affine.Tail04.NativeVersionedAtomless

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

lemma normalized_low_tests (v : ℝ) (hv : v ∈ Icc (0:ℝ) P.d0) (f : Fin 3 → ℝ) :
    Tendsto (fun k => (conditionalTypeCountLaw (normalizedGame s hs V k)
      (by have := large s hs V k;omega) v).expect f) atTop (𝓝 (f 0)) := by
  simp_rw [normalized_count_eq s hs V]
  have h := finiteLaw_expect_tendsto
    (fun k => conditionalTypeCountLaw (originalGame s hs V k) (by have := large s hs V k;omega) v)
    (FiniteLaw.dirac (0:Fin 3)) (low_count_limit s hs V v hv) f
  simpa only [FiniteLaw.expect_dirac] using h

lemma normalized_partial_tests (v : ℝ) (hv : v ∈ P.partialValues) (f : Fin 3 → ℝ) :
    Tendsto (fun k => (conditionalTypeCountLaw (normalizedGame s hs V k)
      (by have := large s hs V k;omega) v).expect f) atTop
      (𝓝 ((s.partialLimit hs v hv).expect f)) := by
  simp_rw [normalized_count_eq s hs V]
  exact finiteLaw_expect_tendsto
    (fun k => conditionalTypeCountLaw (originalGame s hs V k) (by have := large s hs V k;omega) v)
    (s.partialLimit hs v hv) (partial_count_limit s hs V ⟨v,hv⟩) f

lemma normalized_upper_tests (v : ℝ) (hv : P.vA-P.w ≤ v) (f : Fin 3 → ℝ) :
    Tendsto (fun k => (conditionalTypeCountLaw (normalizedGame s hs V k)
      (by have := large s hs V k;omega) v).expect f) atTop (𝓝 (f 1)) := by
  simp_rw [normalized_count_eq s hs V]
  exact upper_expect_limit s hs V v hv f

end FCAppendix.Affine.Tail04.NativeVersionedSource
