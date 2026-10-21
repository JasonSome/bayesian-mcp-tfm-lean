import FCAppendix.Affine.Tail04.OrderedNativePayoffPartialReduction
import FCAppendix.Affine.Tail04.OrderedZeroNativeBindings
import FCAppendix.Affine.Tail04.ZeroPartialC1Integral
import FCAppendix.Affine.Tail04.OrderedZeroNoiseFiniteGame
import FCAppendix.Affine.Tail04.ZeroPrivateScalar
import FCAppendix.Affine.Tail04.ZeroCommonRowLaw
import FCAppendix.Affine.Tail04.ZeroNoiseFiniteGame

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroPartialIntegral
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open OrderedNativeZeroNoiseSource OrderedZeroNativeBindings SourceTailNoisyFixedPoint
open NativeLocalPolicy NativePartialExperiment NativePartialProductReduction
open EqualPrivateSignal EqualPrivateUpper PrivatePayoffContinuity PrivatePartialSorting
open PrivateRowSorting SortedAllNoise ZeroPrivateScalar
open OrderedNativePayoffPartialExperiment
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

local notation "E" => regions D P hdR H hUH
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "Ds" => installOriginal D P t ht
private lemma region_d : (regions D P hdR H hUH).d=P.d0 := rfl
local notation "ρ" => OriginalPrivateSource.originalEntryLaw E P (region_d D P hdR H hUH) t ht.le πL
  (partialLaw D P t ht π) (active D P t ht π) upperBid hupperBid hfloor
set_option quotPrecheck false in
local notation "μP" => bidMarginal (π 2).1
set_option quotPrecheck false in
local notation "μA" => bidMarginal (active D P t ht π).1
set_option quotPrecheck false in
local notation "C" => IndependentCounts.bernoulli (Q).θ (Q).θ_nonneg (Q).θ_le_one

variable (A : ℕ) (own other : Fin (N+2)) (physical : Fin 2) (low : Bool)
  (j : Fin own.val) (v : ℝ) (price : Icc D.R D.Up)
set_option quotPrecheck false in
local notation "θ" => (ProbabilityMeasure.toMeasure (originalIid E own.val ρ))

def originalIntegral (common : Fin A→Icc (1:ℝ) D.U) : ℝ :=
  ∫row,∫pub : unitInterval,∫u : unitInterval,
    OrderedNativePayoffPartialExperiment.value K A own other physical Q low j v price common
      (Function.update row j (Sum.inr price)) pub u
        ∂(volume : Measure unitInterval) ∂(volume : Measure unitInterval) ∂θ

lemma measurable_originalIntegral : Measurable
    (originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A own other physical low j v price) := by
  let Common := Fin A→Icc (1:ℝ) D.U
  let Raw := Row own.val D.R D.Up H
  let f : ((Common×Raw)×unitInterval)×unitInterval→ℝ := fun x=>
    OrderedNativePayoffPartialExperiment.value K A own other physical Q low j v price x.1.1.1
      (Function.update x.1.1.2 j (Sum.inr price)) x.1.2 x.2
  have hf : Measurable f := (OrderedNativePayoffPartialExperiment.measurable_value K A
    own other physical Q low j v).comp
    (by fun_prop : Measurable (fun x : ((Common×Raw)×unitInterval)×unitInterval=>
      (price,(x.1.1.1,(Function.update x.1.1.2 j (Sum.inr price),(x.1.2,x.2))))))
  exact measurable_integral θ _ (measurable_integral volume _ (measurable_integral volume f hf))

lemma originalIntegral_bound (common : Fin A→Icc (1:ℝ) D.U) :
    ‖originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A own other physical low j v price common‖≤|v|+D.Up :=
  integral_bound θ _ _ (fun _row=>integral_bound volume _ _ (fun pub=>
    integral_bound volume _ _ (fun u=>OrderedNativePayoffPartialExperiment.value_bound
      K A own other physical Q low j v price common _ pub u)))

lemma partialRegime_equal (h : ℕ) (jj : Fin h)
    (p : (Ds).PartialFocal×(Fin A→Icc (1:ℝ) (Ds).U)) :
    ZeroNoiseFiniteGame.partialRegimeFiber Ds A h h true low jj p=
      ZeroNoiseFiniteGame.partialRegimeFiber Ds A h h false low jj p := by
  simp only [ZeroNoiseFiniteGame.partialRegimeFiber,ZeroNoiseFiniteGame.partialFiber ]
  rfl

variable [NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (active D P t ht π).1))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (π 2).1).map (fun x=>(x.2:ℝ)))]

theorem originalIntegral_eq : ∀ᵐcommon ∂Measure.pi (fun _ : Fin A=>(μA : Measure _)),
    originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A own other physical low j v price common=
      OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds A own.val other.val low j
        ((v,price,μP),common) := by
  letI : NullSingletonClass (ProbabilityMeasure.toMeasure
      (bidMarginal (NativeZeroNoiseSource.active D P t ht π).1)) := by
    change NullSingletonClass (ProbabilityMeasure.toMeasure
      (bidMarginal (active D P t ht π).1))
    infer_instance
  by_cases h : OrderedHigherRoles.first physical own.val other.val
  · filter_upwards [ZeroPartialC1Integral.originalIntegral_eq D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor N hrare A own other false low j v price] with common hc
    simpa only [originalIntegral,ZeroPartialC1Integral.originalIntegral,
      OrderedNativePayoffPartialExperiment.value_first K A own other physical Q h,
      OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber,if_pos (OrderedHigherRoles.first_le h)]
      using! hc
  · filter_upwards [ZeroPartialC1Integral.originalIntegral_eq D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor N hrare A other own true low j v price] with common hc
    have he : originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        A own other physical low j v price common=
        ZeroNoiseFiniteGame.partialRegimeFiber Ds A other.val own.val true low j
          ((v,price,μP),common) := by
      simpa only [originalIntegral,ZeroPartialC1Integral.originalIntegral,
        OrderedNativePayoffPartialExperiment.value_second K A own other physical Q h] using! hc
    rw [he]
    by_cases hle : own.val≤other.val
    · have heq : own=other := Fin.ext (le_antisymm hle (OrderedHigherRoles.second_le h))
      subst other
      rw [OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber,if_pos le_rfl]
      exact partialRegime_equal D P t ht A low own.val j _
    · simp only [OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber,if_neg hle]

include hdR H hUH πL upperBid hupperBid hfloor hrare physical in
theorem integrable_regime : Integrable (fun common : Fin A→Icc (1:ℝ) D.U=>
    OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds A own.val other.val low j
      ((v,price,μP),common)) (Measure.pi (fun _ : Fin A=>(μA : Measure _))) := by
  have hi := integrable_bounded (Measure.pi (fun _ : Fin A=>ProbabilityMeasure.toMeasure μA))
    (originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A own other physical low j v price)
    (measurable_originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A own other physical low j v price) (|v|+D.Up)
    (originalIntegral_bound D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A own other physical low j v price)
  exact hi.congr (originalIntegral_eq D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
    A own other physical low j v price)

end FCAppendix.Affine.Tail04.OrderedZeroPartialIntegral
