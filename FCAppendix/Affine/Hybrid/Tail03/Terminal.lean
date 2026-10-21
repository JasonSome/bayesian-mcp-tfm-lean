import FCAppendix.Affine.Hybrid.Tail03.TerminalCore
import FCAppendix.Affine.Hybrid.Tail03.LawGaps
import FCAppendix.Affine.TailFinish04.OriginalFamilies

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem aff_tail_result (eta1 eta2 : ℝ) (h1 : 0< eta1)
    (h12 : eta1< eta2) (h2 : eta2<1) :
    ∃F : ProbabilityMeasure ℝ,∃M : ℝ,
      AtomlessUnboundedPositiveDensity F M ∧
      (∃law : LawInput,law.M=M ∧ mixFourComponents law=F) ∧
      ∃f : ActualTwoCoefficientFamilies F eta1 eta2,
        Nonempty (SourceTailOutcomes M f) := by
  obtain ⟨p⟩ := exists_parameters eta1 eta2 h1 h12 h2
  obtain ⟨out⟩ := FCAppendix.Affine.TailFinish04.exists_original_tail_families p
  refine ⟨commonLaw p,p.tailFloor,commonLaw_properties p,
    ⟨p.lawInput,rfl,rfl⟩,out.families,?_⟩
  exact source_outcomes_of_finite_output p out

theorem affine_ii_of_tail (eta1 eta2 : ℝ) (h1 : 0< eta1)
    (h12 : eta1< eta2) (h2 : eta2<1) : SourceAffinePartII eta1 eta2 := by
  obtain ⟨F,M,hF,_,f,⟨o⟩⟩ := aff_tail_result eta1 eta2 h1 h12 h2
  exact affine_part_ii_of_outcomes hF.1 o

end FCAppendix.Affine.Hybrid.Tail03
