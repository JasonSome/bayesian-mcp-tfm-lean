import FCAppendix.Affine.Uniform07Finishing.Native.MatchedLowerChain
import FCAppendix.Affine.Uniform07Finishing.Native.BoundaryIdentity
import FCAppendix.Affine.Uniform07Finishing.Native.SourcePrimitiveSuccess
import FCAppendix.Affine.Uniform07Finishing.Crossover.NativeFamilyTail

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Crossover.Physical

theorem UniformAuxiliaryData05.eventually_all_matched_lower_chains
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D) :
    ∀ᶠ k in atTop, ∀ row : Uniform07.Row,
      ∃ h : MatchedScalarGuards D row k,
        Nonempty (UniformLowerChain (matchedMarket D row k h)) := by
  filter_upwards [D.eventually_all_matched_scalar_guards K,
    D.eventually_all_auxiliaryBoundary_identity K,
    D.eventually_matched_routes_and_moments K,
    D.eventually_all_success_good_mass_small] with k hscalar hidentity hroutes hbad
  intro row
  exact ⟨hscalar row, D.construct_matched_lower_chain row k (hscalar row)
    (hidentity row) (hroutes row (hscalar row)).1 (hbad row)⟩

def uniform_native_pair_from_lower_producers
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D) :
    UniformNativePair :=
  uniformNativePair_from_eventual_matched_chains D K
    (D.eventually_all_matched_lower_chains K)

theorem aff_uniform_result_from_lower_producers
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D) :
    AffUniformResult :=
  aff_uniform_result_of_native_pair (uniform_native_pair_from_lower_producers D K)

end FCAppendix.Affine.Uniform07Finishing
