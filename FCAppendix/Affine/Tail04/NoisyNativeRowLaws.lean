import FCAppendix.Affine.Tail04.NativeNoisySource
import FCAppendix.Affine.Tail04.OriginalPrivateSignalLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.NoisyNativeRowLaws
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues EqualPrivateSignal EqualPrivateUpper
open CompactSourceBidLaws SourceTailNoisyFixedPoint NativeNoisySource

lemma noisy_joint_bid_projection {vlo vhi L U eps : ℝ}
    (hL : 0< L) (heps : 0≤ eps) (μ : Measure (Icc vlo vhi)) [IsProbabilityMeasure μ]
    (π : Law (A:=Icc L U) μ) :
    bidMarginal (Hybrid.activeNoisyLaw hL heps μ π).1=
      noisyBidLaw hL heps (bidMarginal π.1) := by
  apply Subtype.ext
  have hf : Measurable (fun z : (Icc vlo vhi×Icc L U)×unitInterval =>
      (z.1.1,Hybrid.activeNoisyBid hL heps z)) :=
    (measurable_fst.comp measurable_fst).prodMk (Hybrid.continuous_activeNoisyBid hL heps).measurable
  change (((π.1 : Measure (Icc vlo vhi×Icc L U)).prod (volume : Measure unitInterval)).map
    (fun z => (z.1.1,Hybrid.activeNoisyBid hL heps z))).map Prod.snd=
      (((π.1 : Measure (Icc vlo vhi×Icc L U)).map Prod.snd).prod (volume : Measure unitInterval)).map (noisyBid hL heps)
  rw [Measure.map_map measurable_snd hf]
  calc
    _ = ((π.1 : Measure (Icc vlo vhi×Icc L U)).prod (volume : Measure unitInterval)).map
        ((noisyBid hL heps) ∘ Prod.map Prod.snd id) := rfl
    _ = (((π.1 : Measure (Icc vlo vhi×Icc L U)).prod (volume : Measure unitInterval)).map
        (Prod.map Prod.snd id)).map (noisyBid hL heps) :=
      (Measure.map_map (continuous_noisyBid hL heps).measurable
        (measurable_snd.prodMap measurable_id)).symm
    _ = _ := by
      rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id]

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
    (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
    (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (π : JointProfile D P t ht)
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → H≤ upperBid v)

local notation "E" => regions D P hdR H hBH
local notation "πP" => partialPhysical D P t ht π
local notation "πA" => activePhysical D P t ht π
local notation "ρ" => OriginalPrivateSource.originalEntryLaw E P rfl t ht.le πL πP πA
  upperBid hupperBid hfloor
local notation "Ds" => installOriginal D P t ht

lemma partial_projection :
    bidMarginal πP.1=noisyBidLaw D.hR D.heps.le (bidMarginal (π 2).1) :=
  noisy_joint_bid_projection D.hR D.heps.le P.originalPartialLaw (partialBase D P t ht π)

theorem original_private_signal :
    (ρ : Measure (Ici (E).H⊕Icc (E).R (E).Rp)).map signalEntry=
      ProbabilityMeasure.toMeasure
        (privateEntryLaw D.hR D.heps.le (Ds).upperShare (bidMarginal (π 2).1)) := by
  rw [OriginalPrivateSignalLaw.original_signal_law E P rfl t ht.le πL πP πA
    upperBid hupperBid hfloor]
  exact congrArg (fun ν : ProbabilityMeasure (Icc D.R D.V)=>
    ProbabilityMeasure.toMeasure (NoisyPrivateLaws.residualEntryLaw
      (OriginalPrivateSignalLaw.privateShare P t ht.le) ν)) (partial_projection D P t ht π)

theorem original_raw_private_signal (K : ℕ) :
    (PrivateRowSorting.originalIid E K ρ : Measure (Row K (E).R (E).Rp (E).H)).map signal=
      ProbabilityMeasure.toMeasure ((Ds).privateFocalRow K (bidMarginal (π 2).1)) := by
  change (Measure.pi fun _ : Fin K => (ρ : Measure (Ici (E).H⊕Icc (E).R (E).Rp))).map
    (fun row i => signalEntry (row i))=_
  rw [Measure.pi_map_pi (fun _ => continuous_signalEntry.measurable.aemeasurable)]
  simp only [original_private_signal D P t ht hdR H hBH πL π upperBid hupperBid hfloor]
  exact (rowLaw_eq_pi _ _).symm

theorem original_sorted_private_signal (K : ℕ) :
    (OriginalPrivateSource.originalPrivateRow E P rfl t ht.le πL πP πA
      upperBid hupperBid hfloor K : Measure (Row K (E).R (E).Rp (E).H)).map signal=
      ProbabilityMeasure.toMeasure ((Ds).privateBayes K (bidMarginal (π 2).1)) := by
  rw [OriginalPrivateSource.originalPrivateRow,PrivateRowSorting.sortedOriginalIid,
    PrivateRowSorting.sorted_signal_law,original_raw_private_signal D P t ht hdR H hBH
      πL π upperBid hupperBid hfloor K]
  change (ProbabilityMeasure.toMeasure ((Ds).privateFocalRow K (bidMarginal (π 2).1))).map
    (PrivateRowSorting.sortSignal E K)=_
  change _=(ProbabilityMeasure.toMeasure ((Ds).privateFocalRow K (bidMarginal (π 2).1))).map
    ((PrivateRowSorting.sortSignal (Ds).sortingRegion K) ∘ rowCast rfl K)
  congr 1
  funext row i
  simp only [NoisyPrivateLaws.rowCast_rfl,Function.comp_apply,Function.id_def]
  have hkey : (fun k=>LocalCoordinates.signalKey E (row k))=
      (fun k=>LocalCoordinates.signalKey (Ds).sortingRegion (row k)) := by
    funext k
    cases row k <;> rfl
  unfold PrivateRowSorting.sortSignal
  rw [hkey]

theorem original_sorted_marks (K : ℕ) :
    (OriginalPrivateSource.originalPrivateRow E P rfl t ht.le πL πP πA
      upperBid hupperBid hfloor K : Measure (Row K (E).R (E).Rp (E).H)).map (fun row => marks (signal row))=
      FiniteLaw.probabilityMeasure ((Ds).marksLaw K) := by
  have hsignal : Measurable (signal : Row K (E).R (E).Rp (E).H→Signal K (E).R (E).Rp) :=
    measurable_pi_lambda _ fun i=>continuous_signalEntry.measurable.comp (measurable_pi_apply i)
  have hmarks : Measurable (marks : Signal K (E).R (E).Rp→Marks K) :=
    measurable_pi_lambda _ fun i=>continuous_isUpper.measurable.comp (measurable_pi_apply i)
  have hsig:=original_sorted_private_signal D P t ht hdR H hBH πL π upperBid hupperBid hfloor K
  calc
    _=((OriginalPrivateSource.originalPrivateRow E P rfl t ht.le πL πP πA
        upperBid hupperBid hfloor K : Measure (Row K (E).R (E).Rp (E).H)).map signal).map marks :=
      (Measure.map_map hmarks hsignal).symm
    _=_:=(congrArg (fun ν : Measure (Signal K (E).R (E).Rp)=>ν.map marks) hsig).trans
      (NoisyPrivateLaws.privateBayes_markLaw Ds K (bidMarginal (π 2).1))

end FCAppendix.Affine.Tail04.NoisyNativeRowLaws
