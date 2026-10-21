import FCAppendix.Affine.Tail04.FiniteTailNoisyGame
import FCAppendix.Affine.Tail04.FlagAtomPrimitives
import FCAppendix.Existence.R01PayOnceRowIntegration
import FCAppendix.Game.CommonListSeeds

noncomputable section
namespace FCAppendix.Affine.Tail04.NoisyPrivateLaws
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper Existence.Distributional
open CompactSourceBidLaws
open scoped BigOperators

lemma map_mixture {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (p : unitInterval) (μ ν : ProbabilityMeasure X) (f : X → Y) (hf : Measurable f) :
    (mixture p μ ν : Measure X).map f=
      ENNReal.ofReal (p:ℝ) • (μ : Measure X).map f+
        ENNReal.ofReal (1-(p:ℝ)) • (ν : Measure X).map f := by
  change (ENNReal.ofReal (p:ℝ) • (μ : Measure X)+
    ENNReal.ofReal (1-(p:ℝ)) • (ν : Measure X)).map f=_
  rw [Measure.map_add _ _ hf,Measure.map_smul,Measure.map_smul]

lemma bernoulli_measure (p : unitInterval) :
    FiniteLaw.probabilityMeasure (IndependentCounts.bernoulli p p.2.1 p.2.2)=
      ENNReal.ofReal (p:ℝ) • Measure.dirac true+
        ENNReal.ofReal (1-(p:ℝ)) • Measure.dirac false := by
  apply Measure.ext_of_singleton
  intro b
  cases b <;> simp [FiniteLaw.probabilityMeasure_singleton,IndependentCounts.bernoulli,
    Measure.add_apply,Measure.smul_apply]

theorem privateEntry_markLaw {R U eps : ℝ} (hR : 0< R) (heps : 0≤ eps)
    (p : unitInterval) (μP : ProbabilityMeasure (Icc R U)) :
    (privateEntryLaw hR heps p μP : Measure (Unit⊕Icc R (U*(1+eps)))).map isUpper=
      FiniteLaw.probabilityMeasure (IndependentCounts.bernoulli p p.2.1 p.2.2) := by
  have hi : Measurable (isUpper : Unit⊕Icc R (U*(1+eps)) → Bool) :=
    continuous_isUpper.measurable
  have hpartial : (((noisyBidLaw hR heps μP).map
      continuous_inr.measurable.aemeasurable : ProbabilityMeasure
        (Unit⊕Icc R (U*(1+eps)))) : Measure (Unit⊕Icc R (U*(1+eps)))).map isUpper=Measure.dirac false := by
    change (((noisyBidLaw hR heps μP : ProbabilityMeasure (Icc R (U*(1+eps)))) : Measure (Icc R (U*(1+eps)))).map Sum.inr).map isUpper=_
    rw [Measure.map_map hi continuous_inr.measurable]
    change (noisyBidLaw hR heps μP : Measure (Icc R (U*(1+eps)))).map (fun _ => false)=_
    rw [Measure.map_const,measure_univ,one_smul]
  unfold privateEntryLaw
  rw [map_mixture _ _ _ _ hi,hpartial]
  change ENNReal.ofReal (p:ℝ) • (Measure.dirac (Sum.inl () : Unit⊕Icc R (U*(1+eps)))).map isUpper+
    ENNReal.ofReal (1-(p:ℝ)) • Measure.dirac false=_
  rw [Measure.map_dirac' hi,bernoulli_measure]
  rfl

lemma iid_bernoulli_eq_flags (H : ℕ) (p : unitInterval) :
    CommonList.iid (IndependentCounts.bernoulli p p.2.1 p.2.2) H=
      independentFlagLaw (fun _ : Fin H => (p:ℝ)) (fun _ => p.2.1) (fun _ => p.2.2) := by
  apply FiniteLaw.ext
  intro z
  rfl

theorem rawPrivateRow_markLaw {R U eps : ℝ} (hR : 0< R) (heps : 0≤ eps)
    (p : unitInterval) (H : ℕ) (μP : ProbabilityMeasure (Icc R U)) :
    (rawPrivateRow hR heps p H μP : Measure (Signal H R (U*(1+eps)))).map marks=
      FiniteLaw.probabilityMeasure
        (independentFlagLaw (fun _ : Fin H => (p:ℝ)) (fun _ => p.2.1) (fun _ => p.2.2)) := by
  let ρ := privateEntryLaw hR heps p μP
  let ν := IndependentCounts.bernoulli p p.2.1 p.2.2
  have hi : Measurable (isUpper : Unit⊕Icc R (U*(1+eps)) → Bool) :=
    continuous_isUpper.measurable
  have hρ : FiniteLaw.ofMeasure (ρ : Measure _) isUpper hi=ν :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ isUpper hi ν
      (privateEntry_markLaw hR heps p μP)
  have hrow := FiniteLaw.ofMeasure_pi_eq_iid (ρ : Measure _) H
    (fun _ => isUpper) (fun _ => hi) ν (fun _ => hρ)
  have he := FiniteLaw.probabilityMeasure_ofMeasure
    (Measure.pi fun _ : Fin H => (ρ : Measure _))
    (fun row i => isUpper (row i))
    (measurable_pi_lambda _ fun i => hi.comp (measurable_pi_apply i))
  rw [hrow,iid_bernoulli_eq_flags] at he
  simp only [rawPrivateRow,rowLaw_eq_pi,ρ] at he ⊢
  convert! he.symm using 1

lemma rowCast_rfl {R V : ℝ} (H : ℕ) : rowCast (R:=R) (V:=V) rfl H=id := by
  funext row i
  cases h : row i <;> simp [rowCast,h]

theorem privateBayes_markLaw (D : FiniteTailNoisyGame.Data) (H : ℕ)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) :
    (D.privateBayes H μP : Measure (Signal H D.R D.V)).map marks=
      FiniteLaw.probabilityMeasure (D.marksLaw H) := by
  let μ : ProbabilityMeasure (Signal H D.sortingRegion.R D.sortingRegion.Rp) :=
    rawPrivateRow D.hR D.heps.le D.upperShare H μP
  have h := SortedPrivateMarks.original_sorted_markLaw D.sortingRegion H
    (μ : Measure (Signal H D.sortingRegion.R D.sortingRegion.Rp))
    D.upperShare D.upperShare.2.1 D.upperShare.2.2
    (rawPrivateRow_markLaw D.hR D.heps.le D.upperShare H μP)
  change ((μ : Measure (Signal H D.sortingRegion.R D.sortingRegion.Rp)).map
    (fun row : Signal H D.sortingRegion.R D.sortingRegion.Rp => PrivateRowSorting.sortSignal D.sortingRegion H
      (rowCast (R:=D.sortingRegion.R) (V:=D.sortingRegion.Rp) (W:=D.sortingRegion.Rp) rfl H row))).map marks=_
  rw [rowCast_rfl]
  exact h

def numericalEntryLaw {R V Rm : ℝ} (p : unitInterval)
    (μH : ProbabilityMeasure (Ici Rm)) (μP : ProbabilityMeasure (Icc R V)) :
    ProbabilityMeasure (Ici Rm⊕Icc R V) :=
  mixture p (μH.map continuous_inl.measurable.aemeasurable)
    (μP.map continuous_inr.measurable.aemeasurable)

def residualEntryLaw {R V : ℝ} (p : unitInterval)
    (μP : ProbabilityMeasure (Icc R V)) : ProbabilityMeasure (Unit⊕Icc R V) :=
  mixture p ⟨Measure.dirac (Sum.inl ()),Measure.dirac.isProbabilityMeasure⟩
    (μP.map continuous_inr.measurable.aemeasurable)

theorem numericalEntry_signalLaw {R V Rm : ℝ} (p : unitInterval)
    (μH : ProbabilityMeasure (Ici Rm)) (μP : ProbabilityMeasure (Icc R V)) :
    (numericalEntryLaw p μH μP : Measure (Ici Rm⊕Icc R V)).map signalEntry=
      (residualEntryLaw p μP : Measure (Unit⊕Icc R V)) := by
  have hs : Measurable (signalEntry : Ici Rm⊕Icc R V → Unit⊕Icc R V) :=
    continuous_signalEntry.measurable
  have hh : (((μH.map continuous_inl.measurable.aemeasurable : ProbabilityMeasure
      (Ici Rm⊕Icc R V))) : Measure (Ici Rm⊕Icc R V)).map signalEntry=Measure.dirac (Sum.inl ()) := by
    change ((μH : Measure (Ici Rm)).map Sum.inl).map signalEntry=_
    rw [Measure.map_map hs continuous_inl.measurable]
    change (μH : Measure (Ici Rm)).map (fun _ => Sum.inl ())=_
    rw [Measure.map_const,measure_univ,one_smul]
  have hp : (((μP.map continuous_inr.measurable.aemeasurable : ProbabilityMeasure
      (Ici Rm⊕Icc R V))) : Measure (Ici Rm⊕Icc R V)).map signalEntry=
      (μP : Measure (Icc R V)).map Sum.inr := by
    change ((μP : Measure (Icc R V)).map Sum.inr).map signalEntry=_
    rw [Measure.map_map hs continuous_inr.measurable]
    rfl
  unfold numericalEntryLaw
  rw [map_mixture _ _ _ _ hs,hh,hp]
  rfl

theorem numericalRow_signalLaw {R V Rm : ℝ} (p : unitInterval) (H : ℕ)
    (μH : ProbabilityMeasure (Ici Rm)) (μP : ProbabilityMeasure (Icc R V)) :
    (rowLaw H (numericalEntryLaw p μH μP) : Measure (Row H R V Rm)).map signal=
      (rowLaw H (residualEntryLaw p μP) : Measure (Signal H R V)) := by
  rw [rowLaw_eq_pi,rowLaw_eq_pi]
  change (Measure.pi fun _ : Fin H => (numericalEntryLaw p μH μP : Measure (Ici Rm⊕Icc R V))).map
    (fun row i => signalEntry (row i))=_
  rw [Measure.pi_map_pi (fun _ => continuous_signalEntry.measurable.aemeasurable)]
  simp only [numericalEntry_signalLaw]

theorem sorted_numericalRow_signalLaw (E : Observable.Regions) (p : unitInterval)
    (H : ℕ) (μH : ProbabilityMeasure (Ici E.H))
    (μP : ProbabilityMeasure (Icc E.R E.Rp)) :
    (PrivateRowSorting.sortedLaw E H
      (rowLaw H (numericalEntryLaw p μH μP)) : Measure (Row H E.R E.Rp E.H)).map signal=
      (rowLaw H (residualEntryLaw p μP) : Measure (Signal H E.R E.Rp)).map
        (PrivateRowSorting.sortSignal E H) := by
  rw [PrivateRowSorting.sorted_signal_law,numericalRow_signalLaw]

theorem noisy_numericalRow_signalLaw {R U Rm eps : ℝ}
    (hR : 0< R) (heps : 0≤ eps) (p : unitInterval) (H : ℕ)
    (μH : ProbabilityMeasure (Ici Rm)) (μP : ProbabilityMeasure (Icc R U)) :
    (rowLaw H (numericalEntryLaw p μH (noisyBidLaw hR heps μP)) :
      Measure (Row H R (U*(1+eps)) Rm)).map signal=
      (rawPrivateRow hR heps p H μP : Measure _) := by
  exact numericalRow_signalLaw p H μH (noisyBidLaw hR heps μP)

end FCAppendix.Affine.Tail04.NoisyPrivateLaws
