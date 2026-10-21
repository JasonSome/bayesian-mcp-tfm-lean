import FCAppendix.Affine.Tail04.SourceAnalyticContract
import FCAppendix.Affine.Tail04.SourceTailOptimizer
import FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceAnalyticAdapter
open MeasureTheory Set Filter Topology
open OriginalValues SourceAnalyticContract

theorem endpoint_eq (ξ : ℝ) : endpoint ξ=Central.B ξ := rfl
theorem partialFloor_eq (ξ : ℝ) : partialFloor ξ=Central.R ξ := rfl
theorem flagBase_eq (P : ValueParameters) (reg : Bool) :
    flagBase P reg=SourceMenuPopulation.baseFlag P reg := rfl
theorem flag_eq (P : ValueParameters) (ξ : ℝ) (reg : Bool) (b : ℝ) :
    flag P ξ reg b=SourceMenuIdentity.mixedProbability P ξ reg b := rfl
theorem success_eq (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) (b : ℝ) :
    success P ξ lam b=SourceMenuIdentity.served P ξ lam.1 lam.2 b := rfl
theorem duplicates_eq (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) (b : ℝ) :
    duplicates P ξ lam b=SourceMenuIdentity.duplicates P ξ lam.1 lam.2 b := rfl
theorem payment_eq (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) (b : ℝ) :
    payment P ξ lam b=SourceMenuIdentity.payment P ξ lam.1 lam.2 b := rfl
theorem utility_eq (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) (v b : ℝ) :
    utility P ξ lam v b=SourceMenuIdentity.menuUtility P ξ lam.1 lam.2 v b := rfl
theorem leading_eq (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) :
    leading P ξ lam=SourceTailTaylor.leadingA P ξ lam.1 lam.2 := rfl
theorem centerMoment_eq (P : ValueParameters) (reg : Bool) :
    centerMoment P reg=SourceMenuPopulation.centerMoment P reg := rfl
theorem numerator_eq (P : ValueParameters) (ξ M : ℝ) (reg : Bool) :
    numerator P ξ M reg=SourceMenuError.meanNumerator P ξ M reg := rfl
theorem relativeError_eq (P : ValueParameters) (ξ u : ℝ) :
    relativeError P ξ u=SourceMomentRectangle.relativeError P.zeta u (Central.B ξ) := rfl

namespace Parameters

variable (S : SourceAnalyticContract.Parameters)

lemma momentInvariant : SourceMultiplierRectangle.MomentInvariant S.P S.ξ S.ρ S.Λ :=
  S.moment_invariant

lemma bulkDerivativeBound :
    SourceBulkAnalyticAdapter.BulkDerivativeBound S.P S.ξ S.κ S.Λ := S.bulk_derivative

lemma derivativeGeometry : SourceTailOptimizer.DerivativeGeometry S.P S.ξ S.Λ :=
  S.tail_derivatives

lemma exposureRectangle : SourceTailOptimizer.ExposureRectangle S.ξ S.Λ :=
  S.exposure_rectangle

lemma leadingBounds : ∀lam∈S.Λ,
    S.Amin≤ SourceTailTaylor.leadingA S.P S.ξ lam.1 lam.2 ∧
      SourceTailTaylor.leadingA S.P S.ξ lam.1 lam.2≤ S.Amax := S.leading_bounds

abbrev Envelope (N : ℕ) :=
  OrderedSourceEndogenousFloor.Envelope S.P S.ξ S.Up S.u S.k S.width S.ξ_pos S.ξ_half
    S.u_pos.le S.partial_floor_lt S.partial_cap_lt_one S.width_pos S.low_gap N

theorem eventually_envelopes :
    ∀ᶠN in atTop,Nonempty (Envelope S (N+1)) :=
  OrderedSourceEndogenousFloor.eventually_construct S.P S.ξ S.Up S.u S.k S.width
    S.ξ_pos S.ξ_half S.u_pos.le S.partial_floor_lt S.partial_cap_lt_one S.width_pos S.low_gap
    S.u_pos S.κ_pos S.Amin_pos S.cap_lower S.cap_upper S.width_small S.partial_value_gap
    S.bulk_box_lt S.partial_width_small S.moment_small S.low_entropy_gap
    (momentInvariant S) (bulkDerivativeBound S) (leadingBounds S) S.moment_tolerance

end Parameters
end FCAppendix.Affine.Tail04.OrderedSourceAnalyticAdapter
