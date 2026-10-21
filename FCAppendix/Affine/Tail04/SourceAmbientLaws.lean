import FCAppendix.Affine.Tail04.FixedAmbientNoise
import FCAppendix.Affine.Tail04.ZeroNoiseFiniteGame
import FCAppendix.Affine.Tail04.OriginalPrivatePositiveLevels
import FCAppendix.Exclusive.PrimitiveConstruction

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceAmbientLaws
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NoisyPrivateLaws

private lemma map_sort_signal (E : Observable.Regions) (W : ℝ)
    (hVW : E.Rp≤W) (hW : W<1) (H : ℕ) (μ : Measure (Signal H E.R E.Rp)) :
    (μ.map (EqualPrivateAmbient.signal hVW)).map
        (PrivateRowSorting.sortSignal (AmbientSignalSort.region E W hVW hW) H)=
      (μ.map (PrivateRowSorting.sortSignal E H)).map (EqualPrivateAmbient.signal hVW) := by
  have h0 := Measure.map_map
    (PrivateRowSorting.continuous_sortSignal (AmbientSignalSort.region E W hVW hW) H).measurable
    (EqualPrivateAmbient.continuous_signal hVW).measurable (μ:=μ)
  have h1 := Measure.map_map (EqualPrivateAmbient.continuous_signal hVW).measurable
    (PrivateRowSorting.continuous_sortSignal E H).measurable (μ:=μ)
  calc
    _ = μ.map (PrivateRowSorting.sortSignal (AmbientSignalSort.region E W hVW hW) H ∘
        EqualPrivateAmbient.signal hVW) := h0
    _ = μ.map (EqualPrivateAmbient.signal hVW ∘ PrivateRowSorting.sortSignal E H) := by
      congr 1
      funext s
      exact AmbientSignalSort.sortSignal_signal E W hVW hW H s
    _ = _ := h1.symm

variable (D : Data)

def common (e : Noise D.eps) (μ : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    ProbabilityMeasure (Icc (1:ℝ) D.B) := bidLaw (by norm_num) D.hU e μ

def privateRaw (H : ℕ) (e : Noise D.eps) (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    ProbabilityMeasure (Signal H D.R D.V) := privateRow D.hR D.hRUp D.upperShare H e μ

def privateBayes (H : ℕ) (e : Noise D.eps) (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    WeakProbability.Law (Signal H D.R D.V) :=
  WeakProbability.mk (FixedAmbientNoise.privateBayes D.sortingRegion D.hR D.hRUp rfl D.upperShare H e μ)

lemma continuous_common : Continuous
    (fun z : Noise D.eps×ProbabilityMeasure (Icc (1:ℝ) D.U)=> common D z.1 z.2) :=
  continuous_bidLaw (by norm_num) D.hU

lemma continuous_privateRaw (H : ℕ) : Continuous
    (fun z : Noise D.eps×ProbabilityMeasure (Icc D.R D.Up)=> privateRaw D H z.1 z.2) :=
  continuous_privateRow D.hR D.hRUp D.upperShare H

lemma continuous_privateBayes (H : ℕ) : Continuous
    (fun z : Noise D.eps×ProbabilityMeasure (Icc D.R D.Up)=> privateBayes D H z.1 z.2) :=
  WeakProbability.continuous_mk.comp
    (FixedAmbientNoise.continuous_privateBayes D.sortingRegion D.hR D.hRUp rfl D.upperShare H)

theorem common_positive (e : Noise D.eps) (he : 0<(e:ℝ)) (_hes : (e:ℝ)< D.eps)
    (μ : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    common D e μ=(noisyBidLaw (by norm_num) he.le μ).map
      (EqualPrivateAmbient.continuous_widen (upper_mono (by norm_num) D.hU e)).measurable.aemeasurable :=
  bidLaw_eq (by norm_num) D.hU e μ

theorem raw_positive (H : ℕ) (e : Noise D.eps) (he : 0<(e:ℝ)) (hes : (e:ℝ)< D.eps)
    (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    (privateRaw D H e μ : Measure (Signal H D.R D.V))=
      ((atNoise D e he hes).privateFocalRow H μ :
        Measure (Signal H (atNoise D e he hes).R (atNoise D e he hes).V)).map
        (EqualPrivateAmbient.signal (upper_mono D.hR D.hRUp e)) :=
  privateRow_eq D.hR D.hRUp D.upperShare H e μ

theorem bayes_positive (H : ℕ) (e : Noise D.eps) (he : 0<(e:ℝ)) (hes : (e:ℝ)< D.eps)
    (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    privateBayes D H e μ=EqualPrivateAmbient.law (upper_mono D.hR D.hRUp e)
      (WeakProbability.mk ((atNoise D e he hes).privateBayes H μ)) := by
  apply WeakProbability.homeomorph.injective
  apply Subtype.ext
  change (privateRaw D H e μ : Measure (Signal H D.R D.V)).map (PrivateRowSorting.sortSignal D.sortingRegion H ∘
    rowCast rfl H)=
    (((atNoise D e he hes).privateFocalRow H μ :
      Measure (Signal H (atNoise D e he hes).R (atNoise D e he hes).V)).map
      (PrivateRowSorting.sortSignal (atNoise D e he hes).sortingRegion H ∘ rowCast rfl H)).map _
  rw [rowCast_rfl,Function.comp_id,raw_positive D H e he hes μ]
  simpa only [rowCast_rfl,Function.comp_id] using!
    map_sort_signal (atNoise D e he hes).sortingRegion D.V
      (upper_mono D.hR D.hRUp e) D.hRp H
      ((atNoise D e he hes).privateFocalRow H μ :
        Measure (Signal H (atNoise D e he hes).R (atNoise D e he hes).V))

theorem common_zero (μ : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    common D (zero D.eps D.heps.le) μ=μ.map
      (EqualPrivateAmbient.continuous_widen (base_le_upper (by norm_num) D.hU D.heps.le)).measurable.aemeasurable :=
  bidLaw_zero (by norm_num) D.hU D.heps.le μ

lemma entry_zero (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    (entryLaw D.hR D.hRUp D.upperShare (zero D.eps D.heps.le) μ :
      Measure (Unit⊕Icc D.R (D.Up*(1+D.eps))))=
      (ZeroNoiseFiniteGame.privateEntry D μ : Measure (Unit⊕Icc D.R D.Up)).map
        (EqualPrivateAmbient.entry (base_le_upper D.hR D.hRUp D.heps.le)) := by
  unfold ZeroNoiseFiniteGame.privateEntry
  unfold entryLaw residualEntryLaw
  rw [bidLaw_zero]
  change ENNReal.ofReal (D.upperShare:ℝ) • Measure.dirac (Sum.inl ())+
      ENNReal.ofReal (1-(D.upperShare:ℝ)) •
        (((μ : Measure (Icc D.R D.Up)).map
          (EqualPrivateAmbient.widen (base_le_upper D.hR D.hRUp D.heps.le))).map Sum.inr)=
    (ENNReal.ofReal (D.upperShare:ℝ) • Measure.dirac (Sum.inl ())+
      ENNReal.ofReal (1-(D.upperShare:ℝ)) • (μ : Measure (Icc D.R D.Up)).map Sum.inr).map
      (EqualPrivateAmbient.entry (base_le_upper D.hR D.hRUp D.heps.le))
  rw [Measure.map_add _ _ (EqualPrivateAmbient.continuous_entry _).measurable,
    Measure.map_smul,Measure.map_smul,
    Measure.map_dirac' (EqualPrivateAmbient.continuous_entry _).measurable,
    Measure.map_map measurable_inr (EqualPrivateAmbient.continuous_widen _).measurable,
    Measure.map_map (EqualPrivateAmbient.continuous_entry _).measurable measurable_inr]
  rfl

theorem raw_zero (H : ℕ) (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    (privateRaw D H (zero D.eps D.heps.le) μ : Measure (Signal H D.R D.V))=
      (ZeroNoiseFiniteGame.privateRow D H μ : Measure (Signal H D.R D.Up)).map
        (EqualPrivateAmbient.signal (base_le_upper D.hR D.hRUp D.heps.le)) := by
  have he : entryLaw D.hR D.hRUp D.upperShare (zero D.eps D.heps.le) μ=
      (ZeroNoiseFiniteGame.privateEntry D μ).map
        (EqualPrivateAmbient.continuous_entry (base_le_upper D.hR D.hRUp D.heps.le)).measurable.aemeasurable :=
    Subtype.ext (entry_zero D μ)
  unfold privateRaw FixedAmbientNoise.privateRow
  rw [he]
  exact Existence.PayOnceBounded.rowLaw_map H _ _ (EqualPrivateAmbient.continuous_entry _).measurable

theorem bayes_zero (H : ℕ) (μ : ProbabilityMeasure (Icc D.R D.Up)) :
    privateBayes D H (zero D.eps D.heps.le) μ=
      EqualPrivateAmbient.law (base_le_upper D.hR D.hRUp D.heps.le)
        (ZeroNoiseFiniteGame.privateBayes D H μ) := by
  apply WeakProbability.homeomorph.injective
  apply Subtype.ext
  change (privateRaw D H (zero D.eps D.heps.le) μ : Measure (Signal H D.R D.V)).map
      (PrivateRowSorting.sortSignal D.sortingRegion H ∘ rowCast rfl H)=
    (((ZeroNoiseFiniteGame.privateRow D H μ : Measure (Signal H D.R D.Up)).map
      (PrivateRowSorting.sortSignal (ZeroNoiseFiniteGame.sortingRegion D) H)).map _)
  rw [rowCast_rfl,Function.comp_id,raw_zero]
  exact map_sort_signal (ZeroNoiseFiniteGame.sortingRegion D) D.V
    (base_le_upper D.hR D.hRUp D.heps.le) D.hRp H
    (ZeroNoiseFiniteGame.privateRow D H μ : Measure (Signal H D.R D.Up))

lemma raw_zero_positiveLevels (H : ℕ) (μ : ProbabilityMeasure (Icc D.R D.Up))
    [NullSingletonClass ((μ : Measure (Icc D.R D.Up)).map Subtype.val)] :
    OriginalPrivatePositiveLevels.PositiveLevelNull
      (privateRaw D H (zero D.eps D.heps.le) μ : Measure (Signal H D.R D.V)) := by
  intro a ha
  rw [raw_zero]
  apply (ae_map_iff (EqualPrivateAmbient.continuous_signal _).measurable.aemeasurable
    (OriginalPrivatePositiveLevels.measurableSet_avoid a)).mpr
  filter_upwards [OriginalPrivatePositiveLevels.raw_row H D.upperShare μ a ha] with s hs
  intro i
  simpa only [EqualPrivateAmbient.signal,EqualPrivateAmbient.partialBid_entry] using hs i

lemma bayes_zero_positiveLevels (H : ℕ) (μ : ProbabilityMeasure (Icc D.R D.Up))
    [NullSingletonClass ((μ : Measure (Icc D.R D.Up)).map Subtype.val)] :
    OriginalPrivatePositiveLevels.PositiveLevelNull
      (WeakProbability.toMeasure (privateBayes D H (zero D.eps D.heps.le) μ)) := by
  intro a ha
  change ∀ᵐ s ∂(privateRaw D H (zero D.eps D.heps.le) μ : Measure (Signal H D.R D.V)).map
    (PrivateRowSorting.sortSignal D.sortingRegion H ∘ rowCast rfl H),_
  rw [rowCast_rfl,Function.comp_id]
  apply (ae_map_iff (PrivateRowSorting.continuous_sortSignal D.sortingRegion H).measurable.aemeasurable
    (OriginalPrivatePositiveLevels.measurableSet_avoid a)).mpr
  filter_upwards [raw_zero_positiveLevels D H μ a ha] with s hs
  intro i
  exact hs (PrivateRowSorting.permutation (fun k=> LocalCoordinates.signalKey D.sortingRegion (s k)) i)

lemma common_zero_atomless (μ : ProbabilityMeasure (Icc (1:ℝ) D.U))
    [NullSingletonClass (μ : Measure (Icc (1:ℝ) D.U))] :
    NullSingletonClass (common D (zero D.eps D.heps.le) μ : Measure (Icc (1:ℝ) D.B)) := by
  rw [common_zero]
  exact Bayes.ExclusiveConstruction.nullSingletonClass_map_of_injective (μ : Measure (Icc (1:ℝ) D.U))
    (EqualPrivateAmbient.continuous_widen _).measurable
    (fun a b he=> Subtype.ext (congrArg (fun x : Icc (1:ℝ) D.B=>x.val) he))

end FCAppendix.Affine.Tail04.SourceAmbientLaws
