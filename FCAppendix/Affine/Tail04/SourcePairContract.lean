import FCAppendix.Affine.Tail04.SourceAnalyticContract
import FCAppendix.Affine.Tail04.CoefficientOneFloorSource

noncomputable section
namespace FCAppendix.Affine.Tail04.SourcePairContract

structure Parameters (eta1 eta2 : ℝ) where
  two : SourceAnalyticContract.Parameters
  one : CoefficientOne.BoundedSource two.P
  one_guards : CoefficientOne.BoundedSourceGuards one
  first_coefficient : one.scalar.eta=eta1
  second_coefficient : 1-2*two.ξ=eta2
  coefficient_order : eta1< eta2

namespace Parameters
variable {eta1 eta2 : ℝ} (Q : Parameters eta1 eta2)

include Q in
lemma first_pos : 0< eta1 := Q.first_coefficient ▸ Q.one.scalar.eta_pos
include Q in
lemma second_lt_one : eta2<1 := Q.second_coefficient ▸ Q.two.coefficient_lt_one
lemma source_xi : Q.two.ξ=(1-eta2)/2 := by
  have h:=Q.second_coefficient
  linarith

end Parameters
end FCAppendix.Affine.Tail04.SourcePairContract
