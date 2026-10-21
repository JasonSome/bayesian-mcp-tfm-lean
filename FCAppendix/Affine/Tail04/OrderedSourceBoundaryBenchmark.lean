import FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceBoundaryBenchmark
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedOriginalNoisySequence
open OrderedSourceFiniteStartingPoint SourceMovingScalarGuards OrderedSourceRestrictedNative
open SourceMomentRectangle SourceMenuPopulation SourceMultiplierRectangle
open SourceBulkAnalyticAdapter SourceTailTaylor OrderedSourceEndogenousFloor MenuError

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)
  {N : ℕ} (Z : AtomlessPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)
local notation "D" => OrderedSourceFiniteStartingPoint.data P ξ Up u k width
  hξ hξh hu hRUp hUp hw N Z.point.range
local notation "tN" => cutoff N
local notation "V" => boundaryValue P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
local notation "a" => boundaryBid P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow

variable {ρ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
  (hk0 : 0< k) (hmin : 0< Amin) (hk : k<1/(2*Amax))
  (huB : 1+u< Central.B ξ) (hUpMargin : Up≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000) (hwγ : width≤ γ ξ)
  (hrect : MomentInvariant P ξ ρ Λ)
  (hleading : ∀lam∈Λ,Amin≤ leadingA P ξ lam.1 lam.2 ∧ leadingA P ξ lam.1 lam.2≤ Amax)
  (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ)
  (bud : SourceFloorRates.Budgets P ξ Amin Amax k N)

include hk0 hmin hk huB hUpMargin hsmall hwγ hrect hleading hρ bud in
theorem boundary_above_face : tN-Central.B ξ< V := by
  have hc:=cost_bounds P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
    hk0 hmin hk huB hUpMargin hsmall hwγ hrect hleading hρ bud
  linarith [bud.upper]

include hk0 hmin hk huB hUpMargin hsmall hwγ hrect hleading hρ bud in

theorem final_lower_benchmark
    (hr : Ready P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)
    (i : Fin (N+1)) (v : ℝ) (hv : v≤ tN) :
    v-Central.B ξ<
      (problem ((finalMarket P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr).native hlow) i).payoff v (bandAction (by norm_num) 2 le_rfl a) := by
  let G:=(finalMarket P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr).native hlow
  let act:=bandAction (by norm_num : (0:ℝ)≤1) 2 le_rfl a
  have ht:=(problem G i).payoff_affine v tN act
  have hval:=final_boundary_value P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hr i
  have hs:=mul_le_mul_of_nonneg_left ((problem G i).outcome act).success_le_one
    (sub_nonneg.mpr hv)
  have hB:=boundary_above_face P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow
    hk0 hmin hk huB hUpMargin hsmall hwγ hrect hleading hρ bud
  change (problem G i).payoff tN act=V at hval
  rw [hval] at ht
  linarith

end FCAppendix.Affine.Tail04.OrderedSourceBoundaryBenchmark
