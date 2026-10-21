import FCAppendix.Affine.Tail04.AmbientLocalizedTests
import FCAppendix.Affine.Tail04.OrderedSourceAmbientSequence

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceFinitePayoffTests
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Hybrid
open Existence.Distributional OriginalValues EqualPrivateSignal CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedOriginalNoisySequence
open OrderedSourceAmbientSequence FixedAmbientNoise AmbientFiniteGame

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
  (S : Sequence D P t ht N)
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))]

local notation "Ds" => installOriginal D P t ht
local notation "μP" π => partialLaw D P t ht π
local notation "μA" π => commonLaw D P t ht π

lemma atNoise_installOriginal (e : ℝ) (he : 0< e) (hes : e< D.eps) :
    installOriginal (atNoise D e he hes) P t ht=atNoise Ds e he hes := rfl

abbrev Own (k : Fin 3) := ActiveValue (valueLo P k) (valueHi P t k)×
  ActiveBaseBid (bidLo D k) (bidHi D k)

def value (k : Fin 3) : C(Own D P t k,ℝ):=⟨fun x=>(x.1:ℝ),by fun_prop⟩

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 0).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 1).1).map (fun x=>(x.2:ℝ)))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
lemma own_tendsto (k : Fin 3) :
    Tendsto (fun n=>(S.law n k).1) atTop (𝓝 (S.limit k).1) := by
  have hc : Continuous (fun π : JointProfile D P t ht => (π k).1) :=
    continuous_subtype_val.comp (continuous_apply k)
  simpa only [Function.comp_def] using! hc.continuousAt.tendsto.comp S.law_tendsto

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (S.limit 2).1).map (fun x=>(x.2:ℝ)))] in
theorem active_fiber (k : Fin 3) (A H0 H1 : ℕ) (reg low : Bool)
    (action : C(Own D P t k,Icc (1:ℝ) D.U)) (a : C(Own D P t k,ℝ)) :
    Tendsto (fun n=>∫x,a x*(∫b,(installOriginal (S.data n) P t ht).activeFiber A H0 H1 low reg
      (((x.1:ℝ),action x,μP (S.law n)),b) ∂(ProbabilityMeasure.toMeasure (rowLaw A (μA (S.law n)))))
      ∂((S.law n k).1 : Measure _)) atTop
    (𝓝 (∫x,a x*(∫b,ZeroNoiseFiniteGame.activeFiber Ds A H0 H1 low reg
      (((x.1:ℝ),action x,μP S.limit),b) ∂(ProbabilityMeasure.toMeasure (rowLaw A (μA S.limit))))
      ∂((S.limit k).1 : Measure _))) := by
  letI:=OrderedSourceAmbientSequence.common_atomless D P t ht N S
  have hh:=ZeroNoiseActive.tendsto_payoff_test Ds A H0 H1 reg low
    (value D P t k) action a (noise D P t ht N S) (noise_tendsto D P t ht N S)
    (bayesN D P t ht N S H0) (bayesLimit D P t ht N S H0) (bayes_tendsto D P t ht N S H0)
    (commonN D P t ht N S) (commonLimit D P t ht N S) (common_tendsto D P t ht N S)
    (fun n=>(S.law n k).1) (S.limit k).1 (own_tendsto D P t ht N S k)
  have hn (n : ℕ) :
      (∫x,a x*(∫b,(installOriginal (S.data n) P t ht).activeFiber A H0 H1 low reg
        (((x.1:ℝ),action x,μP (S.law n)),b) ∂(ProbabilityMeasure.toMeasure (rowLaw A (μA (S.law n)))))
        ∂((S.law n k).1 : Measure _))=
      ∫z,a z.1*ZeroNoiseActive.payoff Ds A H0 H1 reg low (value D P t k) action
        ((noise D P t ht N S n,bayesN D P t ht N S H0 n),z)
        ∂(ZeroNoiseActive.sampleLaw Ds A (S.law n k).1 (commonN D P t ht N S n) : Measure _) := by
    calc
      _ = ∫x,a x*active Ds A H0 H1 reg low (noise D P t ht N S n)
          (μP (S.law n)) (μA (S.law n)) (value D P t k x) (action x)
          ∂((S.law n k).1 : Measure _) := by
        apply integral_congr_ae
        refine ae_of_all _ fun x => congrArg (fun y : ℝ => a x*y) ?_
        exact (SourceAmbientPayoff.active_positive Ds A H0 H1 reg low
          (noise D P t ht N S n) (S.noise_positive n) (S.noise_small n)
          (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x)).symm
      _ = _ := AmbientLocalizedTests.active_test Ds A H0 H1 reg low (value D P t k) action a
        (noise D P t ht N S n) (μP (S.law n)) (μA (S.law n)) (S.law n k).1
  have hzero :
      (∫x,a x*(∫b,ZeroNoiseFiniteGame.activeFiber Ds A H0 H1 low reg
        (((x.1:ℝ),action x,μP S.limit),b) ∂(ProbabilityMeasure.toMeasure (rowLaw A (μA S.limit))))
        ∂((S.limit k).1 : Measure _))=
      ∫z,a z.1*ZeroNoiseActive.payoff Ds A H0 H1 reg low (value D P t k) action
        ((zero D.eps D.heps.le,bayesLimit D P t ht N S H0),z)
        ∂(ZeroNoiseActive.sampleLaw Ds A (S.limit k).1 (commonLimit D P t ht N S) : Measure _) := by
    calc
      _ = ∫x,a x*active Ds A H0 H1 reg low (zero D.eps D.heps.le)
          (μP S.limit) (μA S.limit) (value D P t k x) (action x)
          ∂((S.limit k).1 : Measure _) := by
        apply integral_congr_ae
        refine ae_of_all _ fun x => congrArg (fun y : ℝ => a x*y) ?_
        exact (SourceAmbientPayoff.active_zero Ds A H0 H1 reg low
          (μP S.limit) (μA S.limit) (x.1:ℝ) (action x)).symm
      _ = _ := AmbientLocalizedTests.active_test Ds A H0 H1 reg low (value D P t k) action a
        (zero D.eps D.heps.le) (μP S.limit) (μA S.limit) (S.limit k).1
  convert! hh using 1
  · funext n
    exact hn n
  · exact congrArg (fun y : ℝ => 𝓝 y) hzero

theorem partial_fiber (A H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (action : C(Own D P t 2,Icc D.R D.Up)) (a : C(Own D P t 2,ℝ)) :
    Tendsto (fun n=>∫x,a x*(∫b,(installOriginal (S.data n) P t ht).partialFiber A H0 H1 side low reg j
      (((x.1:ℝ),action x,μP (S.law n)),b) ∂(ProbabilityMeasure.toMeasure (rowLaw A (μA (S.law n)))))
      ∂((S.law n 2).1 : Measure _)) atTop
    (𝓝 (∫x,a x*(∫b,ZeroNoiseFiniteGame.partialFiber Ds A H0 H1 side low reg j
      (((x.1:ℝ),action x,μP S.limit),b) ∂(ProbabilityMeasure.toMeasure (rowLaw A (μA S.limit))))
      ∂((S.limit 2).1 : Measure _))) := by
  letI:=OrderedSourceAmbientSequence.common_atomless D P t ht N S
  have hrewrite (n : ℕ) :
      (∫x,a x*(∫b,(installOriginal (S.data n) P t ht).partialFiber A H0 H1 side low reg j
        (((x.1:ℝ),action x,μP (S.law n)),b) ∂(ProbabilityMeasure.toMeasure (rowLaw A (μA (S.law n)))))
        ∂((S.law n 2).1 : Measure _))=
      ∫x,a x*«partial» Ds A H0 H1 side reg low j (noise D P t ht N S n)
        (μP (S.law n)) (μA (S.law n)) (x.1:ℝ) (action x) ∂((S.law n 2).1 : Measure _) := by
    apply integral_congr_ae
    refine ae_of_all _ fun x => congrArg (fun y : ℝ => a x*y) ?_
    exact (SourceAmbientPartialPayoff.partial_positive Ds A H0 H1 side reg low j
      (μP (S.law n)) (μA (S.law n)) (noise D P t ht N S n)
      (S.noise_positive n) (S.noise_small n) (x.1:ℝ) (action x)).symm
  have hzero :
      (∫x,a x*(∫b,ZeroNoiseFiniteGame.partialFiber Ds A H0 H1 side low reg j
        (((x.1:ℝ),action x,μP S.limit),b) ∂(ProbabilityMeasure.toMeasure (rowLaw A (μA S.limit))))
        ∂((S.limit 2).1 : Measure _))=
      ∫x,a x*«partial» Ds A H0 H1 side reg low j (zero D.eps D.heps.le)
        (μP S.limit) (μA S.limit) (x.1:ℝ) (action x) ∂((S.limit 2).1 : Measure _) := by
    apply integral_congr_ae
    refine ae_of_all _ fun x => congrArg (fun y : ℝ => a x*y) ?_
    exact (SourceAmbientPartialPayoff.partial_zero Ds A H0 H1 side reg low j
      (μP S.limit) (μA S.limit) (x.1:ℝ) (action x)).symm
  simp_rw [hrewrite,hzero]
  by_cases h : H0=H1
  · subst H1
    let jj : Fin H0:=Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount]) j
    have hh:=EqualZeroNoisePrivate.tendsto_payoff_test Ds A H0 (valueLo P 2) (valueHi P t 2)
      jj action a (noise D P t ht N S) (noise_tendsto D P t ht N S)
      (bayesN D P t ht N S H0) (bayesLimit D P t ht N S H0) (bayes_tendsto D P t ht N S H0)
      (bayes_positiveLevels D P t ht N S H0)
      (commonN D P t ht N S) (commonLimit D P t ht N S) (common_tendsto D P t ht N S)
      (rawN D P t ht N S H0) (rawLimit D P t ht N S H0) (raw_tendsto D P t ht N S H0)
      (raw_positiveLevels D P t ht N S H0)
      (fun n=>(S.law n 2).1) (S.limit 2).1 (own_tendsto D P t ht N S 2)
    convert! hh using 1
    · funext n
      simpa only [«partial»,dif_pos rfl,dite_true,jj] using!
        AmbientLocalizedTests.equal_test Ds A (valueLo P 2) (valueHi P t 2)
          action a (noise D P t ht N S n) (μP (S.law n)) (μA (S.law n))
          (S.law n 2).1 H0 jj
    · congr 1
      simpa only [«partial»,dif_pos rfl,dite_true,jj] using!
        AmbientLocalizedTests.equal_test Ds A (valueLo P 2) (valueHi P t 2)
          action a (zero D.eps D.heps.le) (μP S.limit) (μA S.limit)
          (S.limit 2).1 H0 jj
  · have hh:=UnequalZeroNoisePrivate.tendsto_payoff_test Ds A H0 H1 side reg low
      (valueLo P 2) (valueHi P t 2) j action a (noise D P t ht N S) (noise_tendsto D P t ht N S)
      (commonN D P t ht N S) (commonLimit D P t ht N S) (common_tendsto D P t ht N S)
      (rawN D P t ht N S (AllCountAtypical.ownCount H0 H1 side))
      (rawLimit D P t ht N S (AllCountAtypical.ownCount H0 H1 side))
      (raw_tendsto D P t ht N S (AllCountAtypical.ownCount H0 H1 side))
      (raw_positiveLevels D P t ht N S (AllCountAtypical.ownCount H0 H1 side))
      (fun n=>(S.law n 2).1) (S.limit 2).1 (own_tendsto D P t ht N S 2)
    convert! hh using 1
    · funext n
      exact AmbientLocalizedTests.unequal_test Ds A H0 H1 side reg low
        (valueLo P 2) (valueHi P t 2) j action a (noise D P t ht N S n)
        (μP (S.law n)) (μA (S.law n)) (S.law n 2).1 h
    · congr 1
      exact AmbientLocalizedTests.unequal_test Ds A H0 H1 side reg low
        (valueLo P 2) (valueHi P t 2) j action a (zero D.eps D.heps.le)
        (μP S.limit) (μA S.limit) (S.limit 2).1 h

end FCAppendix.Affine.Tail04.OrderedSourceFinitePayoffTests
