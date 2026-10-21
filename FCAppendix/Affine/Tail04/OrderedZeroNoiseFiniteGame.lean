import FCAppendix.Affine.Tail04.ZeroNoiseFiniteGame
import FCAppendix.Affine.Tail04.SourceOrderedNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroNoiseFiniteGame
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint
open scoped BigOperators

variable (D : Data)

def activeRegimeFiber (A H0 H1 : ℕ) (lowPresent : Bool)
    (p : D.ActiveFocal × (Fin A → Icc (1:ℝ) D.U)) : ℝ :=
  ZeroNoiseFiniteGame.activeRegimeFiber D A (min H0 H1) (max H0 H1) lowPresent p

def partialOwnRegimeFiber (A own other : ℕ) (lowPresent : Bool) (j : Fin own)
    (p : D.PartialFocal × (Fin A → Icc (1:ℝ) D.U)) : ℝ :=
  if own ≤ other then ZeroNoiseFiniteGame.partialRegimeFiber D A own other false lowPresent j p
  else ZeroNoiseFiniteGame.partialRegimeFiber D A other own true lowPresent j p

def activeExpected (N : ℕ) (p : D.BidLaws × (ℝ × Icc (1:ℝ) D.U)) : ℝ :=
  ∑ kind : Fin N → Fin 4, (CommonList.iid D.categories N).mass kind *
    ∫ row : Fin (D.count kind 1) → Icc (1:ℝ) D.U,
      activeRegimeFiber D (D.count kind 1) (D.count kind 2) (D.count kind 3)
        (decide (0 < D.count kind 0)) ((p.2.1,p.2.2,p.1.2.2),row)
        ∂(rowLaw (D.count kind 1) (D.commonLaw p.1) : Measure _)

def partialPattern {N : ℕ} (kind : Fin N → Fin 4)
    (p : D.PartialFocal × (Fin (D.count kind 1) → Icc (1:ℝ) D.U)) : ℝ :=
  (1/2:ℝ) * partialOwnRegimeFiber D (D.count kind 1) (D.count kind 2+1)
    (D.count kind 3) (decide (0 < D.count kind 0)) ⟨0,by omega⟩ p +
  (1/2:ℝ) * partialOwnRegimeFiber D (D.count kind 1) (D.count kind 3+1)
    (D.count kind 2) (decide (0 < D.count kind 0)) ⟨0,by omega⟩ p

def partialExpected (N : ℕ) (p : D.BidLaws × (ℝ × Icc D.R D.Up)) : ℝ :=
  ∑ kind : Fin N → Fin 4, (CommonList.iid D.categories N).mass kind *
    ∫ row : Fin (D.count kind 1) → Icc (1:ℝ) D.U,
      partialPattern D kind ((p.2.1,p.2.2,p.1.2.2),row)
        ∂(rowLaw (D.count kind 1) (D.commonLaw p.1) : Measure _)

def sourcePayoff (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∀ i : Fin 3,JointProfile D P t ht×
      (Hybrid.ActiveValue (valueLo P i) (valueHi P t i)×
        Hybrid.ActiveBaseBid (bidLo D i) (bidHi D i))→ℝ := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
  · exact fun p=> activeExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),extendBid D.huU p.2.2))
  · exact fun p=> activeExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),p.2.2))
  · exact fun p=> partialExpected (installOriginal D P t ht) N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),p.2.2))

end FCAppendix.Affine.Tail04.OrderedZeroNoiseFiniteGame
