import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Positive
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Low
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Entry

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Uniform06 Uniform06.LiteralExperiment Physical

namespace ReadyLowerFamily

def low (F : ReadyLowerFamily) (row : Uniform07.Row) :
    LowFamily06 (fun k=>(F.market row k).native) row :=
  Received06.low_family (G row) (g row) (cm row) (fun k=>(F.market row k).native)
    row (earlyMenu row) (roots row) (atoms row)
    (F.law row) (tail_population_tendsto F.start) (F.positive_counts row)
    (F.toLowerFamily.native_zero_duplicate row)

theorem entry (F : ReadyLowerFamily) (row : Uniform07.Row) :
    EntryFullMenu06 (fun k=>(F.market row k).native) row :=
  Received06.entry_full_menu (G row) (g row) (cm row) (fun k=>(F.market row k).native)
    row (earlyMenu row) (roots row) (atoms row) (count_contract row)
    (F.law row) (tail_population_tendsto F.start) (F.positive_counts row)
    (F.low row) (fun _=>rfl) (fun _=>rfl)

end ReadyLowerFamily
end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
