import FCAppendix.Affine.Tail04.SourceAmbientLaws
import FCAppendix.Affine.Tail04.ZeroNoiseActive
import FCAppendix.Affine.Tail04.UnequalZeroNoisePrivate
import FCAppendix.Affine.Tail04.OrderedOriginalNoisySequence
import FCAppendix.Exclusive.PrimitiveConstruction

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceAmbientSequence
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues EqualPrivateSignal CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint FixedAmbientNoise SourceAmbientLaws
open OrderedOriginalNoisySequence

lemma subtype_atomless_of_real {L U : ℝ} (μ : ProbabilityMeasure (Icc L U))
    [NullSingletonClass ((μ : Measure (Icc L U)).map Subtype.val)] :
    NullSingletonClass (μ : Measure (Icc L U)) := by
  constructor
  intro b
  have he : (μ : Measure (Icc L U)) {b}=((μ : Measure (Icc L U)).map Subtype.val) {(b:ℝ)} := by
    rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)]
    congr 1
    ext x
    simp only [Set.mem_singleton_iff,Set.mem_preimage,Subtype.ext_iff]
  rw [he,measure_singleton]

lemma bidMarginal_real {T : Type*} [MeasurableSpace T] [TopologicalSpace T] [BorelSpace T]
    {L U : ℝ} (π : ProbabilityMeasure (T×Icc L U)) :
    ((bidMarginal π : ProbabilityMeasure (Icc L U)) : Measure (Icc L U)).map Subtype.val=
      (π : Measure (T×Icc L U)).map (fun x=>(x.2:ℝ)) := by
  change ((π : Measure (T×Icc L U)).map Prod.snd).map Subtype.val=_
  rw [Measure.map_map measurable_subtype_coe measurable_snd]
  rfl

lemma activeBaseLaw_atomless {u U : ℝ} (h : 1+u≤ U) (p : unitInterval)
    (μB : ProbabilityMeasure (Icc (1:ℝ) (1+u))) (μT : ProbabilityMeasure (Icc (1:ℝ) U))
    [NullSingletonClass (μB : Measure (Icc (1:ℝ) (1+u)))]
    [NullSingletonClass (μT : Measure (Icc (1:ℝ) U))] :
    NullSingletonClass (activeBaseLaw h p μB μT : Measure (Icc (1:ℝ) U)) := by
  letI : NullSingletonClass ((μB : Measure (Icc (1:ℝ) (1+u))).map (extendBid h)) :=
    Bayes.ExclusiveConstruction.nullSingletonClass_map_of_injective (μB : Measure (Icc (1:ℝ) (1+u)))
      (continuous_extendBid h).measurable
      (fun a b he=> Subtype.ext (congrArg (fun x : Icc (1:ℝ) U=>x.val) he))
  constructor
  intro b
  simp [activeBaseLaw,mixture,Measure.add_apply,Measure.smul_apply]

private lemma raw_pair_tendsto (D : Data) (H : ℕ)
    (q : ℕ→Noise D.eps×ProbabilityMeasure (Icc D.R D.Up))
    (q0 : Noise D.eps×ProbabilityMeasure (Icc D.R D.Up))
    (hq : Tendsto q atTop (𝓝 q0)) :
    Tendsto (fun j => SourceAmbientLaws.privateRaw D H (q j).1 (q j).2) atTop
      (𝓝 (SourceAmbientLaws.privateRaw D H q0.1 q0.2)) :=
  (SourceAmbientLaws.continuous_privateRaw D H).continuousAt.tendsto.comp hq

private lemma bayes_pair_tendsto (D : Data) (H : ℕ)
    (q : ℕ→Noise D.eps×ProbabilityMeasure (Icc D.R D.Up))
    (q0 : Noise D.eps×ProbabilityMeasure (Icc D.R D.Up))
    (hq : Tendsto q atTop (𝓝 q0)) :
    Tendsto (fun j => SourceAmbientLaws.privateBayes D H (q j).1 (q j).2) atTop
      (𝓝 (SourceAmbientLaws.privateBayes D H q0.1 q0.2)) :=
  (SourceAmbientLaws.continuous_privateBayes D H).continuousAt.tendsto.comp hq

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
  (S : Sequence D P t ht N)

abbrev F := installOriginal D P t ht

def noise (j : ℕ) : Noise D.eps := ⟨S.eps j,(S.noise_positive j).le,(S.noise_small j).le⟩

lemma noise_tendsto : Tendsto (noise D P t ht N S) atTop (𝓝 (zero D.eps D.heps.le)) :=
  tendsto_subtype_rng.mpr S.noise_real_tendsto

def commonLaw (π : JointProfile D P t ht) : ProbabilityMeasure (Icc (1:ℝ) D.U) :=
  (F D P t ht).commonLaw (bidLaws D P t ht π)

def partialLaw (π : JointProfile D P t ht) : ProbabilityMeasure (Icc D.R D.Up) :=
  (bidLaws D P t ht π).2.2

lemma continuous_commonLaw : Continuous (commonLaw D P t ht) :=
  (Data.continuous_commonLaw (F D P t ht)).comp (continuous_bidLaws D P t ht)

lemma continuous_partialLaw : Continuous (partialLaw D P t ht) :=
  (continuous_snd.comp continuous_snd).comp (continuous_bidLaws D P t ht)

def commonN (j : ℕ) : ProbabilityMeasure (Icc (1:ℝ) (F D P t ht).B) :=
  SourceAmbientLaws.common (F D P t ht) (noise D P t ht N S j)
  (commonLaw D P t ht (S.law j))

def commonLimit : ProbabilityMeasure (Icc (1:ℝ) (F D P t ht).B) :=
  SourceAmbientLaws.common (F D P t ht) (zero D.eps D.heps.le)
  (commonLaw D P t ht S.limit)

def rawN (H : ℕ) (j : ℕ) : ProbabilityMeasure (Signal H (F D P t ht).R (F D P t ht).V) :=
  SourceAmbientLaws.privateRaw (F D P t ht) H (noise D P t ht N S j)
  (partialLaw D P t ht (S.law j))

def rawLimit (H : ℕ) : ProbabilityMeasure (Signal H (F D P t ht).R (F D P t ht).V) :=
  SourceAmbientLaws.privateRaw (F D P t ht) H (zero D.eps D.heps.le)
  (partialLaw D P t ht S.limit)

def bayesN (H : ℕ) (j : ℕ) : WeakProbability.Law (Signal H (F D P t ht).R (F D P t ht).V) :=
  SourceAmbientLaws.privateBayes (F D P t ht) H
  (noise D P t ht N S j) (partialLaw D P t ht (S.law j))

def bayesLimit (H : ℕ) : WeakProbability.Law (Signal H (F D P t ht).R (F D P t ht).V) :=
  SourceAmbientLaws.privateBayes (F D P t ht) H (zero D.eps D.heps.le)
  (partialLaw D P t ht S.limit)

lemma common_tendsto : Tendsto (commonN D P t ht N S) atTop (𝓝 (commonLimit D P t ht N S)) :=
  (SourceAmbientLaws.continuous_common (F D P t ht)).continuousAt.tendsto.comp
    ((noise_tendsto D P t ht N S).prodMk_nhds
      ((continuous_commonLaw D P t ht).continuousAt.tendsto.comp S.law_tendsto))

lemma raw_tendsto (H : ℕ) : Tendsto (rawN D P t ht N S H) atTop (𝓝 (rawLimit D P t ht N S H)) :=
  raw_pair_tendsto (F D P t ht) H
    (fun j => (noise D P t ht N S j,partialLaw D P t ht (S.law j)))
    (zero D.eps D.heps.le,partialLaw D P t ht S.limit)
    ((noise_tendsto D P t ht N S).prodMk_nhds
      ((continuous_partialLaw D P t ht).continuousAt.tendsto.comp S.law_tendsto))

lemma bayes_tendsto (H : ℕ) : Tendsto (bayesN D P t ht N S H) atTop (𝓝 (bayesLimit D P t ht N S H)) :=
  bayes_pair_tendsto (F D P t ht) H
    (fun j => (noise D P t ht N S j,partialLaw D P t ht (S.law j)))
    (zero D.eps D.heps.le,partialLaw D P t ht S.limit)
    ((noise_tendsto D P t ht N S).prodMk_nhds
      ((continuous_partialLaw D P t ht).continuousAt.tendsto.comp S.law_tendsto))

lemma common_atomless
    [NullSingletonClass (((S.limit 0).1 : Measure
      (Hybrid.ActiveValue (valueLo P 0) (valueHi P t 0)×Hybrid.ActiveBaseBid (bidLo D 0) (bidHi D 0))).map (fun x=>(x.2:ℝ)))]
    [NullSingletonClass (((S.limit 1).1 : Measure
      (Hybrid.ActiveValue (valueLo P 1) (valueHi P t 1)×Hybrid.ActiveBaseBid (bidLo D 1) (bidHi D 1))).map (fun x=>(x.2:ℝ)))] :
    NullSingletonClass (commonLimit D P t ht N S : Measure (Icc (1:ℝ) (F D P t ht).B)) := by
  let μ0 : ProbabilityMeasure (Icc (1:ℝ) (1+D.u)) := bidMarginal (S.limit 0).1
  let μ1 : ProbabilityMeasure (Icc (1:ℝ) D.U) := bidMarginal (S.limit 1).1
  letI : NullSingletonClass ((μ0 : Measure (Icc (1:ℝ) (1+D.u))).map Subtype.val) := by
    rw [bidMarginal_real]
    exact (inferInstance : NullSingletonClass (((S.limit 0).1 : Measure
      (Hybrid.ActiveValue (valueLo P 0) (valueHi P t 0)×Hybrid.ActiveBaseBid (bidLo D 0) (bidHi D 0))).map
        (fun x=>(x.2:ℝ))))
  letI : NullSingletonClass ((μ1 : Measure (Icc (1:ℝ) D.U)).map Subtype.val) := by
    rw [bidMarginal_real]
    exact (inferInstance : NullSingletonClass (((S.limit 1).1 : Measure
      (Hybrid.ActiveValue (valueLo P 1) (valueHi P t 1)×Hybrid.ActiveBaseBid (bidLo D 1) (bidHi D 1))).map
        (fun x=>(x.2:ℝ))))
  letI : NullSingletonClass (μ0 : Measure (Icc (1:ℝ) (1+D.u))):=subtype_atomless_of_real μ0
  letI : NullSingletonClass (μ1 : Measure (Icc (1:ℝ) D.U)):=subtype_atomless_of_real μ1
  letI : NullSingletonClass (commonLaw D P t ht S.limit : Measure (Icc (1:ℝ) D.U)):=
    activeBaseLaw_atomless D.huU (F D P t ht).bulkShare μ0 μ1
  exact @SourceAmbientLaws.common_zero_atomless (F D P t ht) (commonLaw D P t ht S.limit)
    (inferInstance : NullSingletonClass (commonLaw D P t ht S.limit : Measure (Icc (1:ℝ) D.U)))

lemma partial_real_atomless
    [NullSingletonClass (((S.limit 2).1 : Measure
      (Hybrid.ActiveValue (valueLo P 2) (valueHi P t 2)×Hybrid.ActiveBaseBid (bidLo D 2) (bidHi D 2))).map (fun x=>(x.2:ℝ)))] :
    NullSingletonClass ((partialLaw D P t ht S.limit : Measure (Icc D.R D.Up)).map Subtype.val) := by
  change NullSingletonClass (((bidMarginal (S.limit 2).1 : ProbabilityMeasure (Icc D.R D.Up)) :
    Measure (Icc D.R D.Up)).map Subtype.val)
  rw [bidMarginal_real]
  exact (inferInstance : NullSingletonClass (((S.limit 2).1 : Measure
    (Hybrid.ActiveValue (valueLo P 2) (valueHi P t 2)×Hybrid.ActiveBaseBid (bidLo D 2) (bidHi D 2))).map
      (fun x=>(x.2:ℝ))))

lemma raw_positiveLevels (H : ℕ)
    [NullSingletonClass (((S.limit 2).1 : Measure
      (Hybrid.ActiveValue (valueLo P 2) (valueHi P t 2)×Hybrid.ActiveBaseBid (bidLo D 2) (bidHi D 2))).map (fun x=>(x.2:ℝ)))] :
    OriginalPrivatePositiveLevels.PositiveLevelNull (rawLimit D P t ht N S H :
      Measure (Signal H (F D P t ht).R (F D P t ht).V)) := by
  exact @SourceAmbientLaws.raw_zero_positiveLevels (F D P t ht) H (partialLaw D P t ht S.limit)
    (partial_real_atomless D P t ht N S)

lemma bayes_positiveLevels (H : ℕ)
    [NullSingletonClass (((S.limit 2).1 : Measure
      (Hybrid.ActiveValue (valueLo P 2) (valueHi P t 2)×Hybrid.ActiveBaseBid (bidLo D 2) (bidHi D 2))).map (fun x=>(x.2:ℝ)))] :
    OriginalPrivatePositiveLevels.PositiveLevelNull
      (WeakProbability.toMeasure (bayesLimit D P t ht N S H)) := by
  exact @SourceAmbientLaws.bayes_zero_positiveLevels (F D P t ht) H (partialLaw D P t ht S.limit)
    (partial_real_atomless D P t ht N S)

end FCAppendix.Affine.Tail04.OrderedSourceAmbientSequence
