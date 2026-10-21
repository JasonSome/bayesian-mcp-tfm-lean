import FCAppendix.Affine.Tail04.NativeZeroNoiseSource
import FCAppendix.Affine.Tail04.OriginalPrivateSignalLaw
import FCAppendix.Affine.Tail04.ZeroNoiseFiniteGame

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNativeRowLaws
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues EqualPrivateSignal EqualPrivateUpper
open CompactSourceBidLaws SourceTailNoisyFixedPoint NativeZeroNoiseSource
open NoisyPrivateLaws

theorem residualEntry_markLaw {R U : ℝ} (p : unitInterval)
    (μ : ProbabilityMeasure (Icc R U)) :
    (residualEntryLaw p μ : Measure (Unit⊕Icc R U)).map isUpper=
      FiniteLaw.probabilityMeasure (IndependentCounts.bernoulli p p.2.1 p.2.2) := by
  have hi : Measurable (isUpper : Unit⊕Icc R U→ Bool) := continuous_isUpper.measurable
  have hpartial : (ProbabilityMeasure.toMeasure (μ.map (measurable_inr : Measurable (Sum.inr : Icc R U→Unit⊕Icc R U)).aemeasurable)).map isUpper=Measure.dirac false := by
    change ((ProbabilityMeasure.toMeasure μ).map Sum.inr).map isUpper=_
    rw [Measure.map_map hi measurable_inr]
    change (ProbabilityMeasure.toMeasure μ).map (fun _=> false)=_
    rw [Measure.map_const,measure_univ,one_smul]
  unfold residualEntryLaw
  rw [map_mixture _ _ _ _ hi,hpartial]
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_dirac' hi,bernoulli_measure]
  rfl

theorem residualRow_markLaw {R U : ℝ} (p : unitInterval) (K : ℕ)
    (μ : ProbabilityMeasure (Icc R U)) :
    (rowLaw K (residualEntryLaw p μ) : Measure (Signal K R U)).map marks=
      FiniteLaw.probabilityMeasure
        (independentFlagLaw (fun _ : Fin K=>(p:ℝ)) (fun _=> p.2.1) (fun _=> p.2.2)) := by
  let ρ := residualEntryLaw p μ
  let ν := IndependentCounts.bernoulli p p.2.1 p.2.2
  have hi : Measurable (isUpper : Unit⊕Icc R U→ Bool) := continuous_isUpper.measurable
  have hρ : FiniteLaw.ofMeasure (ProbabilityMeasure.toMeasure ρ) isUpper hi=ν :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ isUpper hi ν
      (residualEntry_markLaw p μ)
  have hrow := FiniteLaw.ofMeasure_pi_eq_iid (ProbabilityMeasure.toMeasure ρ) K
    (fun _=> isUpper) (fun _=> hi) ν (fun _=> hρ)
  have he := FiniteLaw.probabilityMeasure_ofMeasure
    (Measure.pi (fun _ : Fin K=>(ProbabilityMeasure.toMeasure ρ))) (fun row i=> isUpper (row i))
    (measurable_pi_lambda _ (fun i=> hi.comp (measurable_pi_apply i)))
  rw [hrow,iid_bernoulli_eq_flags] at he
  simpa only [rowLaw_eq_pi,marks,ρ] using! he.symm

theorem zero_privateBayes_markLaw (D : FiniteTailNoisyGame.Data) (K : ℕ)
    (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    (WeakProbability.toMeasure (ZeroNoiseFiniteGame.privateBayes D K μ)).map marks=
      FiniteLaw.probabilityMeasure (D.marksLaw K) := by
  have hh := SortedPrivateMarks.original_sorted_markLaw
    (ZeroNoiseFiniteGame.sortingRegion D) K
    (ProbabilityMeasure.toMeasure (rowLaw K (residualEntryLaw D.upperShare μ)))
    D.upperShare D.upperShare.2.1 D.upperShare.2.2
    (residualRow_markLaw D.upperShare K μ)
  simpa only [ZeroNoiseFiniteGame.privateBayes,ZeroNoiseFiniteGame.privateRow,
    ZeroNoiseFiniteGame.privateEntry,WeakProbability.toMeasure,WeakProbability.val_mk,
    ProbabilityMeasure.toMeasure_map,FiniteTailNoisyGame.Data.marksLaw] using! hh

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v)

local notation "E" => regions D P hdR H hUH
local notation "πP" => «partial» D P t ht π
local notation "πA" => active D P t ht π
local notation "ρ" => OriginalPrivateSource.originalEntryLaw E P rfl t ht.le πL πP πA
  upperBid hupperBid hfloor
local notation "Ds" => installOriginal D P t ht
local notation "μP" => bidMarginal (Subtype.val (π 2))

theorem original_private_signal :
    (ProbabilityMeasure.toMeasure ρ).map signalEntry=
      (ProbabilityMeasure.toMeasure (ZeroNoiseFiniteGame.privateEntry Ds μP)) := by
  rw [OriginalPrivateSignalLaw.original_signal_law E P rfl t ht.le πL πP πA
    upperBid hupperBid hfloor]
  rfl

theorem original_raw_private_signal (K : ℕ) :
    (ProbabilityMeasure.toMeasure (PrivateRowSorting.originalIid E K ρ)).map signal=
      (ProbabilityMeasure.toMeasure (ZeroNoiseFiniteGame.privateRow Ds K μP)) := by
  rw [OriginalPrivateSignalLaw.original_rawRow_signal_law E P rfl t ht.le πL πP πA
    upperBid hupperBid hfloor K]
  rfl

theorem original_sorted_private_signal (K : ℕ) :
    (ProbabilityMeasure.toMeasure (OriginalPrivateSource.originalPrivateRow E P rfl t ht.le πL πP πA
      upperBid hupperBid hfloor K)).map signal=
      WeakProbability.toMeasure (ZeroNoiseFiniteGame.privateBayes Ds K μP) := by
  rw [OriginalPrivateSignalLaw.original_sortedRow_signal_law E P rfl t ht.le πL πP πA
    upperBid hupperBid hfloor K]
  change (ProbabilityMeasure.toMeasure (rowLaw K (residualEntryLaw (Ds).upperShare μP))).map
    (PrivateRowSorting.sortSignal E K)=
      (ProbabilityMeasure.toMeasure (rowLaw K (residualEntryLaw (Ds).upperShare μP))).map
        (PrivateRowSorting.sortSignal (ZeroNoiseFiniteGame.sortingRegion Ds) K)
  congr 1
  funext row i
  have hkey : (fun k : Fin K=>LocalCoordinates.signalKey E (row k))=
      (fun k : Fin K=>LocalCoordinates.signalKey (ZeroNoiseFiniteGame.sortingRegion Ds) (row k)) := by
    funext k
    cases row k <;> rfl
  exact congrArg (fun keys : Fin K→ℝ => row (PrivateRowSorting.permutation keys i)) hkey

theorem original_sorted_marks (K : ℕ) :
    (ProbabilityMeasure.toMeasure (OriginalPrivateSource.originalPrivateRow E P rfl t ht.le πL πP πA
      upperBid hupperBid hfloor K)).map (fun row=> marks (signal row))=
      FiniteLaw.probabilityMeasure ((Ds).marksLaw K) := by
  have hmap := Measure.map_map
    (measurable_pi_lambda _ fun i=> continuous_isUpper.measurable.comp (measurable_pi_apply i))
    (measurable_pi_lambda _ fun i=> continuous_signalEntry.measurable.comp (measurable_pi_apply i))
    (μ:=ProbabilityMeasure.toMeasure (OriginalPrivateSource.originalPrivateRow E P rfl t ht.le πL πP πA
      upperBid hupperBid hfloor K))
  calc
    _ = ((ProbabilityMeasure.toMeasure (OriginalPrivateSource.originalPrivateRow E P rfl t ht.le πL πP πA
        upperBid hupperBid hfloor K)).map signal).map marks := hmap.symm
    _ = _ := by
      rw [original_sorted_private_signal D P t ht hdR H hUH πL π upperBid hupperBid hfloor K]
      exact zero_privateBayes_markLaw Ds K μP

end FCAppendix.Affine.Tail04.ZeroNativeRowLaws
