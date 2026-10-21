import FCAppendix.Affine.Hybrid.Tail03.Terminal

noncomputable section
namespace FCAppendix.Affine.TailFinish04
open MeasureTheory ProbabilityTheory Set Filter Topology
open Hybrid.Tail03

theorem every_interior_coefficient_pair (eta1 eta2 : ℝ)
    (h1 : 0<eta1) (h12 : eta1<eta2) (h2 : eta2<1) :
    ∃F : ProbabilityMeasure ℝ,∃M : ℝ,
      AtomlessUnboundedPositiveDensity F M ∧
      (∃law : LawInput,law.M=M ∧ mixFourComponents law=F) ∧
      ∃f : ActualTwoCoefficientFamilies F eta1 eta2,
        Nonempty (SourceTailOutcomes M f) :=
  Hybrid.Tail03.aff_tail_result eta1 eta2 h1 h12 h2

theorem appendix_affine_proof_7 (eta1 eta2 : ℝ)
    (h1 : 0<eta1) (h12 : eta1<eta2) (h2 : eta2<1) :
    SourceAffinePartII eta1 eta2 :=
  Hybrid.Tail03.affine_ii_of_tail eta1 eta2 h1 h12 h2

theorem thm_affine_ii (eta1 eta2 : ℝ)
    (h1 : 0<eta1) (h12 : eta1<eta2) (h2 : eta2<1) :
    SourceAffinePartII eta1 eta2 :=
  appendix_affine_proof_7 eta1 eta2 h1 h12 h2

theorem primitive_original_families (eta1 eta2 : ℝ)
    (h1 : 0<eta1) (h12 : eta1<eta2) (h2 : eta2<1) :
    ∃p : Parameters eta1 eta2,Nonempty (BothOriginalFiniteFamiliesAndLimits p) := by
  obtain ⟨p⟩:=exists_parameters eta1 eta2 h1 h12 h2
  exact ⟨p,exists_original_tail_families p⟩

end FCAppendix.Affine.TailFinish04
