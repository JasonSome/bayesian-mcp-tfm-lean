import FCAppendix.Affine.Tail04.OrderedNativePayoffPartialReduction
import FCAppendix.Affine.Tail04.NativePartialC1Integral
import FCAppendix.Affine.Tail04.SourceOrderedNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffPartialIntegral
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open OrderedNativeNoisySource OrderedNativePayoffBindings SourceTailNoisyFixedPoint
open NativeLocalPolicy NativePartialExperiment NativePartialProductReduction
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy JoinedPartialNoisy
open AtypicalPartialNoisy UnequalPartialOriginalIntegral PrivateRowSorting SortedAllNoise
open OrderedNativePayoffPartialExperiment
open scoped BigOperators

local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

variable (A : ℕ) (own other : Fin ((N+1)+1)) (physical : Fin 2) (low : Bool)
  (j : Fin own.val) (v : ℝ) (price : Icc D.R D.Up)

lemma partialRegime_equal (h : ℕ) (jj : Fin h)
    (p : (installOriginal D P t ht).PartialFocal×(Fin A→Icc (1:ℝ) (installOriginal D P t ht).U)) :
    (installOriginal D P t ht).partialRegimeFiber A h h true low jj p=
      (installOriginal D P t ht).partialRegimeFiber A h h false low jj p := by
  simp only [FiniteTailNoisyGame.Data.partialRegimeFiber,
    FiniteTailNoisyGame.Data.partialFiber]
  rfl

def originalIntegral (base : Fin A→Icc (1:ℝ) D.U) : ℝ :=
  ∫ commonNoise : Fin A→unitInterval,∫ row,∫ a : unitInterval,
    ∫ pub : unitInterval,∫ u : unitInterval,
      OrderedNativePayoffPartialExperiment.noisyValue (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) A own other physical (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor)
        D.heps.le rfl low j v price
        (EqualNoisyUtilities.physical D.heps.le base commonNoise) row a pub u
          ∂(volume : Measure unitInterval) ∂(volume : Measure unitInterval)
          ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) own.val (NoisyNativeFiberProduct.privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor))) ∂(Measure.pi (fun _ : Fin A => (volume : Measure unitInterval)))

theorem originalIntegral_eq (base : Fin A→Icc (1:ℝ) D.U) :
    originalIntegral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      A own other physical low j v price base=
      OrderedFiniteTailNoisyGame.partialOwnRegimeFiber (installOriginal D P t ht) A own.val other.val low j
        ((v,price,(NativePartialC1Integral.partialBidLaw D P t ht π)),base) := by
  by_cases h : OrderedHigherRoles.first physical own.val other.val
  · have he : originalIntegral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
        A own other physical low j v price base=
        NativePartialC1Integral.originalIntegral D P t ht hdR H hBH πL π upperBid
          hupperBid hfloor N hrare A own other false low j v price base := by
      simp only [originalIntegral,NativePartialC1Integral.originalIntegral,
        OrderedNativePayoffPartialExperiment.noisyValue,
        OrderedNativePayoffPartialExperiment.value_first (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) A own other physical (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) h,
        NativePartialExperiment.noisyValue]
      rfl
    rw [he,NativePartialC1Integral.originalIntegral_eq]
    simp only [OrderedFiniteTailNoisyGame.partialOwnRegimeFiber,
      if_pos (OrderedHigherRoles.first_le h)]
  · have he : originalIntegral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
        A own other physical low j v price base=
        NativePartialC1Integral.originalIntegral D P t ht hdR H hBH πL π upperBid
          hupperBid hfloor N hrare A other own true low j v price base := by
      simp only [originalIntegral,NativePartialC1Integral.originalIntegral,
        OrderedNativePayoffPartialExperiment.noisyValue,
        OrderedNativePayoffPartialExperiment.value_second (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) A own other physical (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) h,
        NativePartialExperiment.noisyValue]
      rfl
    rw [he,NativePartialC1Integral.originalIntegral_eq]
    by_cases hle : own.val≤other.val
    · have heq : own=other := Fin.ext (le_antisymm hle (OrderedHigherRoles.second_le h))
      subst other
      rw [OrderedFiniteTailNoisyGame.partialOwnRegimeFiber,if_pos le_rfl]
      exact partialRegime_equal D P t ht A low own.val j _
    · simp only [OrderedFiniteTailNoisyGame.partialOwnRegimeFiber,if_neg hle]

end FCAppendix.Affine.Tail04.OrderedNativePayoffPartialIntegral
