import FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor
import FCAppendix.Affine.Tail04.CanonicalFailure

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceGlobalLower
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceRestrictedNative
open OrderedSourceEndogenousFloor SourceMovingScalarGuards

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {hlow : P.d0<1-ξ} {N : ℕ}

structure RawLower (E : Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N) : Prop where
  band_lower : ∀q : Fin 3,
    ∀ᵐx ∂(ProbabilityMeasure.toMeasure (Subtype.val (E.market.sequence.limit q))),∀i : Fin (N+1),
      ∀a : JointAction 2,a.bid< E.market.H→
        (problem (E.market.native hlow) i).payoff (x.1:ℝ) a≤
          (problem (E.market.native hlow) i).payoff (x.1:ℝ)
            (bandAction (bidLo_pos E.market.D q).le (if q=2 then 1 else 2)
              (by split_ifs <;> omega) x.2)
  boundary_all : ∀i : Fin (N+1),∀a : JointAction 2,a.bid< E.market.H→
    (problem (E.market.native hlow) i).payoff (cutoff N) a≤
      boundaryValue P ξ Up u k width hξ hξh hu hRUp hUp hw E.point hlow
  lower_success : ∀i : Fin (N+1),∀a : JointAction 2,a.bid< E.market.H→
    ((problem (E.market.native hlow) i).outcome a).success≤
      1-CanonicalFailure.movingCoefficient P ξ k/(4*cutoff N^2)

end FCAppendix.Affine.Tail04.OrderedSourceGlobalLower
