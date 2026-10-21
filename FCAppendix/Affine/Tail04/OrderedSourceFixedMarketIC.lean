import FCAppendix.Affine.Tail04.OrderedSourcePayoffPassage
import FCAppendix.Affine.Tail04.FixedMarketLimitIC

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceFixedMarketIC
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Hybrid
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open OrderedOriginalNoisySequence OrderedSourceFinitePayoffTests

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
  (S : Sequence D P t ht N)
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))]

def limitPayoff (k : Fin 3) : C(Own D P t k,ℝ) :=
  ⟨fun x=> OrderedZeroNoiseFiniteGame.sourcePayoff D P t ht N k (S.limit,x),
    OrderedSourcePayoffPassage.continuous_zero D P t ht N S k⟩

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))] [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma continuous_noisy_payoff (n : ℕ) (k : Fin 3) :
    Continuous (fun x : Own D P t k=>
      SourceOrderedNoisyFixedPoint.payoff (S.data n) P t ht N k (S.law n,x)) :=
  (SourceOrderedNoisyFixedPoint.continuous_payoff (S.data n) P t ht N k).comp
    (continuous_const.prodMk continuous_id)

theorem gain_test_passage (k : Fin 3)
    (b : ActiveBaseBid (bidLo D k) (bidHi D k)) (a : C(Own D P t k,ℝ)) :
    Tendsto (fun n=> FixedMarketLimitIC.gainTest (originalValueLaw P t ht k)
      (fun n=> S.law n k)
      (fun n x=> SourceOrderedNoisyFixedPoint.payoff (S.data n) P t ht N k (S.law n,x)) n b a)
      atTop (𝓝 (FixedMarketLimitIC.limitGainTest (originalValueLaw P t ht k) (S.limit k)
        (limitPayoff D P t ht N S k) b a)) := by
  let incumbent : C(Own D P t k,ActiveBaseBid (bidLo D k) (bidHi D k)):=⟨Prod.snd,continuous_snd⟩
  let comparison : C(Own D P t k,ActiveBaseBid (bidLo D k) (bidHi D k)):=ContinuousMap.const _ b
  have hc:=OrderedSourcePayoffPassage.localized D P t ht N S k comparison a
  have hi:=OrderedSourcePayoffPassage.localized D P t ht N S k incumbent a
  have hnc (n : ℕ) := FinitePayoffLinearity.continuous_integrable
    (ProbabilityMeasure.toMeasure (S.law n k).1) _
    (a.continuous.mul ((continuous_noisy_payoff D P t ht N S n k).comp
      (continuous_fst.prodMk (continuous_const (y:=b)))))
  have hni (n : ℕ) := FinitePayoffLinearity.continuous_integrable
    (ProbabilityMeasure.toMeasure (S.law n k).1) _
    (a.continuous.mul (continuous_noisy_payoff D P t ht N S n k))
  have hzc:=FinitePayoffLinearity.continuous_integrable (ProbabilityMeasure.toMeasure (S.limit k).1) _
    (a.continuous.mul ((limitPayoff D P t ht N S k).continuous.comp
      (continuous_fst.prodMk (continuous_const (y:=b)))))
  have hzi:=FinitePayoffLinearity.continuous_integrable (ProbabilityMeasure.toMeasure (S.limit k).1) _
    (a.continuous.mul (limitPayoff D P t ht N S k).continuous)
  have hh:=hc.sub hi
  convert! hh using 1
  · funext n
    simpa only [FixedMarketLimitIC.gainTest,mul_sub,incumbent,comparison,
      ContinuousMap.coe_mk,ContinuousMap.const_apply] using! integral_sub (hnc n) (hni n)
  · exact congrArg (fun y : ℝ=>𝓝 y) (by
      simpa only [FixedMarketLimitIC.limitGainTest,mul_sub,limitPayoff,incumbent,comparison,
        ContinuousMap.coe_mk,ContinuousMap.const_apply] using! integral_sub hzc hzi)

theorem all_action_optimal (k : Fin 3) :
    AllActionOptimal (S.limit k)
      (fun x=> OrderedZeroNoiseFiniteGame.sourcePayoff D P t ht N k (S.limit,x)) := by
  exact FixedMarketLimitIC.all_actions_from_actual_tests
    (originalValueLaw P t ht k) (fun n=> S.law n k) (S.limit k)
    (fun n x=> SourceOrderedNoisyFixedPoint.payoff (S.data n) P t ht N k (S.law n,x))
    (limitPayoff D P t ht N S k) (fun n=> S.optimal n k)
    (fun b a _=> gain_test_passage D P t ht N S k b a)

theorem all_species : ∀k : Fin 3,AllActionOptimal (S.limit k)
    (fun x=> OrderedZeroNoiseFiniteGame.sourcePayoff D P t ht N k (S.limit,x)) :=
  all_action_optimal D P t ht N S

end FCAppendix.Affine.Tail04.OrderedSourceFixedMarketIC
