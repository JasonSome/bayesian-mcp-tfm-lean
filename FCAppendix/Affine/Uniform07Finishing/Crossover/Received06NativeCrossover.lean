import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06NativeSplit

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Uniform06 Physical Received06

def BroadcastLowerFamily.crossover (F : BroadcastLowerFamily) (row : Uniform07.Row) :
    SameLawCrossoverKernels06 F.toAuxiliaryData row where
  canonicalEvent:=crossoverEvent F row
  A:=OptimizedPhysicalRate.A row
  Amin:=(sourceRateConstants row).Amin
  Amax:=(sourceRateConstants row).Amax
  Rmax:=receivedRmax row
  Dmax:=receivedDmax row
  AminPositive:=(sourceRateConstants row).Amin_pos
  RmaxNonnegative:=by
    unfold receivedRmax
    exact div_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (Uniform07.xi_pos row).le (source_crossover_geometry row).1.le)
        (sourceRateConstants row).Amin_pos.le)
  DmaxNonnegative:=by
    unfold receivedDmax
    exact div_nonneg (by norm_num)
      (mul_nonneg (Uniform07.xi_pos row).le (source_crossover_geometry row).1.le)
  e19:=fun k=>receivedU19Error row (F.start+k)
  eS:=fun k=>receivedSuccessError row (F.start+k)
  eD:=fun k=>receivedDuplicateError row (F.start+k)
  ell:=fun k=>lowBenchmark (F.start+k)
  nonnegative:=Eventually.of_forall (fun k=>
    ⟨receivedU19Error_nonnegative row _,receivedSuccessError_nonnegative row _,
      receivedDuplicateError_nonnegative row _,lowBenchmark_pos _⟩)
  core:=eventually_native_remote_core F row
  split:=eventually_native_split F row
  e19Small:=(receivedU19Error_tendsto row).comp (tail_population_tendsto F.start)
  successCoefficient:=receivedSuccessCoefficient
  successRate:=receivedSuccessRate row
  successRatePositive:=receivedSuccessRate_pos row
  successChernoff:=Eventually.of_forall (fun k=>receivedSuccessError_chernoff row (F.start+k))
  duplicateSmall:=(receivedDuplicateError_tendsto row).comp (tail_population_tendsto F.start)
  duplicateRentSmall:=(receivedDuplicateError_rent_tendsto row).comp (tail_population_tendsto F.start)

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
