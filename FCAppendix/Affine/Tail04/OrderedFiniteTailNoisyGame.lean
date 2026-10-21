import FCAppendix.Affine.Tail04.FiniteTailNoisyGame
import FCAppendix.Affine.Tail04.OrderedHigherRoles

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedFiniteTailNoisyGame
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data)

def activeRegimeFiber (A H0 H1 : ℕ) (lowPresent : Bool)
    (p : D.ActiveFocal × (Fin A → Icc (1:ℝ) D.U)) : ℝ :=
  D.activeRegimeFiber A (min H0 H1) (max H0 H1) lowPresent p

lemma continuous_activeRegimeFiber (A H0 H1 : ℕ) (lowPresent : Bool) :
    Continuous (activeRegimeFiber D A H0 H1 lowPresent) :=
  D.continuous_activeRegimeFiber A (min H0 H1) (max H0 H1) lowPresent

def partialOwnRegimeFiber (A own other : ℕ) (lowPresent : Bool) (j : Fin own)
    (p : D.PartialFocal × (Fin A → Icc (1:ℝ) D.U)) : ℝ :=
  if own ≤ other then D.partialRegimeFiber A own other false lowPresent j p
  else D.partialRegimeFiber A other own true lowPresent j p

lemma continuous_partialOwnRegimeFiber (A own other : ℕ) (lowPresent : Bool) (j : Fin own) :
    Continuous (partialOwnRegimeFiber D A own other lowPresent j) := by
  unfold partialOwnRegimeFiber
  split
  · exact D.continuous_partialRegimeFiber A own other false lowPresent j
  · exact D.continuous_partialRegimeFiber A other own true lowPresent j

def activeExpected (N : ℕ) (p : D.BidLaws × (ℝ × Icc (1:ℝ) D.U)) : ℝ :=
  ∑ kind : Fin N → Fin 4, (CommonList.iid D.categories N).mass kind *
    ∫ row : Fin (D.count kind 1) → Icc (1:ℝ) D.U,
      activeRegimeFiber D (D.count kind 1) (D.count kind 2) (D.count kind 3)
        (decide (0 < D.count kind 0)) ((p.2.1,p.2.2,p.1.2.2),row)
        ∂(rowLaw (D.count kind 1) (D.commonLaw p.1) : Measure _)

lemma continuous_activeExpected (N : ℕ) : Continuous (activeExpected D N) := by
  unfold activeExpected
  apply continuous_finsetSum
  intro kind _
  apply continuous_const.mul
  have hi := continuous_law_integral
    (activeRegimeFiber D (D.count kind 1) (D.count kind 2) (D.count kind 3)
      (decide (0 < D.count kind 0)))
    (continuous_activeRegimeFiber D _ _ _ _)
  have hf : Continuous (fun p : D.BidLaws × (ℝ × Icc (1:ℝ) D.U) =>
      (p.2.1,p.2.2,p.1.2.2)) := by fun_prop
  exact hi.comp (hf.prodMk
    ((continuous_rowLaw _).comp (D.continuous_commonLaw.comp continuous_fst)))

def partialPattern {N : ℕ} (kind : Fin N → Fin 4)
    (p : D.PartialFocal × (Fin (D.count kind 1) → Icc (1:ℝ) D.U)) : ℝ :=
  (1/2:ℝ) * partialOwnRegimeFiber D (D.count kind 1) (D.count kind 2+1)
    (D.count kind 3) (decide (0 < D.count kind 0)) ⟨0,by omega⟩ p +
  (1/2:ℝ) * partialOwnRegimeFiber D (D.count kind 1) (D.count kind 3+1)
    (D.count kind 2) (decide (0 < D.count kind 0)) ⟨0,by omega⟩ p

lemma continuous_partialPattern {N : ℕ} (kind : Fin N → Fin 4) :
    Continuous (partialPattern D kind) :=
  (continuous_const.mul (continuous_partialOwnRegimeFiber D _ _ _ _ _)).add
    (continuous_const.mul (continuous_partialOwnRegimeFiber D _ _ _ _ _))

def partialExpected (N : ℕ) (p : D.BidLaws × (ℝ × Icc D.R D.Up)) : ℝ :=
  ∑ kind : Fin N → Fin 4, (CommonList.iid D.categories N).mass kind *
    ∫ row : Fin (D.count kind 1) → Icc (1:ℝ) D.U,
      partialPattern D kind ((p.2.1,p.2.2,p.1.2.2),row)
        ∂(rowLaw (D.count kind 1) (D.commonLaw p.1) : Measure _)

lemma continuous_partialExpected (N : ℕ) : Continuous (partialExpected D N) := by
  unfold partialExpected
  apply continuous_finsetSum
  intro kind _
  apply continuous_const.mul
  have hi := continuous_law_integral (partialPattern D kind) (continuous_partialPattern D kind)
  have hf : Continuous (fun p : D.BidLaws × (ℝ × Icc D.R D.Up) =>
      (p.2.1,p.2.2,p.1.2.2)) := by fun_prop
  exact hi.comp (hf.prodMk
    ((continuous_rowLaw _).comp (D.continuous_commonLaw.comp continuous_fst)))

end FCAppendix.Affine.Tail04.OrderedFiniteTailNoisyGame
