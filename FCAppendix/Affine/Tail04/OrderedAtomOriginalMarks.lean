import FCAppendix.Affine.Tail04.OrderedAtomTwoFocalExpectation
import FCAppendix.Affine.Tail04.NoisyNativeRowLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomOriginalMarks
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues EqualPrivateSignal
open SourceTailNoisyFixedPoint NativeNoisySource OrderedAtomTwoFocalGuard

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v)

local notation "E" => regions D P hdR H hBH
local notation "Ds" => installOriginal D P t ht

theorem originalMarks_eq (K : ℕ) :
    originalMarks P E rfl t ht (bulkPhysicalWidth D) (bulkPhysicalWidth_le D)
      πL (partialPhysical D P t ht π) (bulkPhysical D P t ht π)
      (tailPhysical D P t ht π) upperBid hupperBid hfloor K=(Ds).marksLaw K := by
  apply AtypicalOriginalPosterior.markLaw_eq_of_pushforward
  exact NoisyNativeRowLaws.original_sorted_marks D P t ht hdR H hBH
    πL π upperBid hupperBid hfloor K

theorem actualPhi_eq (ξ : ℝ) (N : ℕ) (width : ℝ) (reg : Bool)
    (r : Fin N→ UserDraw 2) (A : ℕ) :
    OrderedAtomTwoFocalExpectation.actualPhi P E rfl t ht
      (bulkPhysicalWidth D) (bulkPhysicalWidth_le D) πL
      (partialPhysical D P t ht π) (bulkPhysical D P t ht π)
      (tailPhysical D P t ht π) upperBid hupperBid hfloor ξ N width reg r A=
      TypicalGuardStatistics.phi A
        ((min (OrderedAtomTwoFocalExpectation.privateSize E r 2) (OrderedAtomTwoFocalExpectation.privateSize E r 3)))
        ((max (OrderedAtomTwoFocalExpectation.privateSize E r 2) (OrderedAtomTwoFocalExpectation.privateSize E r 3)))
        (MenuError.twoCapacity (99/200) N) ξ D.B D.R D.V width reg
        ((Ds).marksLaw ((min (OrderedAtomTwoFocalExpectation.privateSize E r 2) (OrderedAtomTwoFocalExpectation.privateSize E r 3))))
        ((Ds).marksLaw ((max (OrderedAtomTwoFocalExpectation.privateSize E r 2) (OrderedAtomTwoFocalExpectation.privateSize E r 3)))) := by
  unfold OrderedAtomTwoFocalExpectation.actualPhi
  rw [originalMarks_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor,
    originalMarks_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor]
  rfl

end FCAppendix.Affine.Tail04.OrderedAtomOriginalMarks
