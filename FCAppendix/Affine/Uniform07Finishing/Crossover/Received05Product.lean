import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Family
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05ProductFamily

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Physical

def ReadyLowerFamily.product (F : ReadyLowerFamily) (row : Uniform07.Row) :
    ProductFamily05 (fun k=>(F.market row k).native) row
      (fun _=>sourceLowerPriceCeiling row) :=
  F.toLowerFamily.product row

theorem ReadyLowerFamily.product_error_literal
    (F : ReadyLowerFamily) (row : Uniform07.Row) (k : ℕ) :
    (F.product row).error k=Concrete05.productError row (F.market row k).native
      (sourceLowerPriceCeiling row) := rfl

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
