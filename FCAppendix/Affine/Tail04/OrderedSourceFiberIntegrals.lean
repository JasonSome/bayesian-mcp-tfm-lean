import FCAppendix.Affine.Tail04.AmbientZeroContinuity
import FCAppendix.Affine.Tail04.OrderedSourceFinitePayoffTests
import FCAppendix.Affine.Tail04.ZeroFiberBounds
import FCAppendix.Affine.Tail04.FinitePayoffLinearity

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceFiberIntegrals
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Hybrid
open Existence.Distributional OriginalValues EqualPrivateSignal CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedOriginalNoisySequence
open OrderedSourceFinitePayoffTests OrderedSourceAmbientSequence FixedAmbientNoise

variable (D : Data)

def active (A H0 H1 : ℕ) (reg low : Bool)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc (1:ℝ) D.U) : ℝ :=
  ∫b,D.activeFiber A H0 H1 low reg ((v,price,μP),b) ∂(rowLaw A μA : Measure _)

def zeroActive (A H0 H1 : ℕ) (reg low : Bool)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc (1:ℝ) D.U) : ℝ :=
  ∫b,ZeroNoiseFiniteGame.activeFiber D A H0 H1 low reg ((v,price,μP),b)
    ∂(rowLaw A μA : Measure _)

def «partial» (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  ∫b,D.partialFiber A H0 H1 side low reg j ((v,price,μP),b) ∂(rowLaw A μA : Measure _)

def zeroPartial (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) : ℝ :=
  ∫b,ZeroNoiseFiniteGame.partialFiber D A H0 H1 side low reg j ((v,price,μP),b)
    ∂(rowLaw A μA : Measure _)

lemma continuous_active (A H0 H1 : ℕ) (reg low : Bool)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    Continuous (fun x : ℝ×Icc (1:ℝ) D.U=> active D A H0 H1 reg low μP μA x.1 x.2) :=
  (continuous_law_integral (D.activeFiber A H0 H1 low reg)
    (D.continuous_activeFiber A H0 H1 low reg)).comp
      ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).prodMk continuous_const)

lemma continuous_partial (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    Continuous (fun x : ℝ×Icc D.R D.Up=> «partial» D A H0 H1 side reg low j μP μA x.1 x.2) :=
  (continuous_law_integral (D.partialFiber A H0 H1 side low reg j)
    (D.continuous_partialFiber A H0 H1 side low reg j)).comp
      ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).prodMk continuous_const)

lemma active_row_integrable (A H0 H1 : ℕ) (reg low : Bool)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc (1:ℝ) D.U) :
    Integrable (fun b=> D.activeFiber A H0 H1 low reg ((v,price,μP),b)) (rowLaw A μA : Measure _) :=
  FinitePayoffLinearity.continuous_integrable _ _
    ((D.continuous_activeFiber A H0 H1 low reg).comp (continuous_const.prodMk continuous_id))

lemma partial_row_integrable (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (v : ℝ) (price : Icc D.R D.Up) :
    Integrable (fun b=> D.partialFiber A H0 H1 side low reg j ((v,price,μP),b))
      (rowLaw A μA : Measure _) :=
  FinitePayoffLinearity.continuous_integrable _ _
    ((D.continuous_partialFiber A H0 H1 side low reg j).comp (continuous_const.prodMk continuous_id))

variable (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
  (S : Sequence D P t ht N)
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))]

local notation "Ds"=> installOriginal D P t ht

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
theorem continuous_zero_active (k : Fin 3) (A H0 H1 : ℕ) (reg low : Bool)
    (action : C(Own D P t k,Icc (1:ℝ) D.U)) :
    Continuous (fun x=> zeroActive Ds A H0 H1 reg low (partialLaw D P t ht S.limit)
      (commonLaw D P t ht S.limit) (x.1:ℝ) (action x)) := by
  letI : NullSingletonClass (ProbabilityMeasure.toMeasure
      (SourceAmbientLaws.common Ds (zero (Ds).eps (Ds).heps.le) (commonLaw D P t ht S.limit))) :=
    OrderedSourceAmbientSequence.common_atomless D P t ht N S
  simpa only [SourceAmbientPayoff.active_zero,zeroActive] using!
    AmbientZeroContinuity.active Ds A H0 H1 reg low (value D P t k) action
      (partialLaw D P t ht S.limit) (commonLaw D P t ht S.limit)

theorem continuous_zero_partial (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (action : C(Own D P t 2,Icc D.R D.Up)) :
    Continuous (fun x=> zeroPartial Ds A H0 H1 side reg low j (partialLaw D P t ht S.limit)
      (commonLaw D P t ht S.limit) (x.1:ℝ) (action x)) := by
  letI : NullSingletonClass (ProbabilityMeasure.toMeasure
      (SourceAmbientLaws.common Ds (zero (Ds).eps (Ds).heps.le) (commonLaw D P t ht S.limit))) :=
    OrderedSourceAmbientSequence.common_atomless D P t ht N S
  letI : NullSingletonClass ((ProbabilityMeasure.toMeasure (partialLaw D P t ht S.limit)).map
      (fun x : Icc (Ds).R (Ds).Up => (x:ℝ))) :=
    OrderedSourceAmbientSequence.partial_real_atomless D P t ht N S
  simpa only [SourceAmbientPartialPayoff.partial_zero,zeroPartial] using!
    @AmbientZeroContinuity.«partial» Ds A (valueLo P 2) (valueHi P t 2) action
      (partialLaw D P t ht S.limit) (commonLaw D P t ht S.limit)
      (OrderedSourceAmbientSequence.partial_real_atomless D P t ht N S)
      (OrderedSourceAmbientSequence.common_atomless D P t ht N S) H0 H1 side reg low j

end FCAppendix.Affine.Tail04.OrderedSourceFiberIntegrals
