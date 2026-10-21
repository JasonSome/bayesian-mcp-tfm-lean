import FCAppendix.Affine.Tail04.OrderedZeroPartialIntegral
import FCAppendix.Affine.Tail04.OrderedZeroPartialFiberLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroPartialNumericalPayoff
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open OrderedNativeZeroNoiseSource OrderedZeroNativeBindings SourceTailNoisyFixedPoint
open NativeLocalPolicy NativePartialExperiment NativePartialTerminal
open NativePartialProductReduction NativeActiveFiberCoordinates NativeFiberEnumerations
open PartialNativeCoordinates EqualPrivateUpper PrivateRowSorting NativeHighExperiment
open OrderedNativePayoffPartialExperiment OrderedNativePayoffPartialTerminal
open OrderedNativePayoffPartialReduction

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "m" => N+1
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)
include hrare in
private lemma fiberRare : (1-D.ξ)*D.U+D.ξ*D.U*(((N:ℝ)+1)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R := by
  simpa only [Nat.cast_add,Nat.cast_one] using hrare
local notation "hfr" => fiberRare D P t N hrare
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "Ds" => installOriginal D P t ht
local notation "ρ" => OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π
  upperBid hupperBid hfloor N hfr
set_option quotPrecheck false in
local notation "ρA" => OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π
set_option quotPrecheck false in
local notation "μA" => (Ds).commonLaw (bidLaws D P t ht π)
set_option quotPrecheck false in
local notation "μP" => bidMarginal (π 2).1

variable (i : Fin (N+1)) (kind : Fin N → Fin 4) (side : Bool)
local notation "A" => commonSize i kind
set_option quotPrecheck false in
local notation "H0" => (K).finiteCount (rivalSet i kind 2)
set_option quotPrecheck false in
local notation "H1" => (K).finiteCount (rivalSet i kind 3)
local notation "G0" => post0 K i kind side
local notation "G1" => post1 K i kind side
local notation "own" => ownTotal K i kind side
local notation "other" => otherTotal K i kind side
local notation "physical" => OrderedNativePayoffPartialTerminal.physical side
local notation "j" => focalIndex K i kind side
local notation "low" => OrderedZeroPartialFiberLaw.lowPresent D P t ht kind
local notation "ν" => rawPayloadLaw K ρ H0 H1
local notation "M" => Measure.pi (fun _ : Fin A => (ProbabilityMeasure.toMeasure ρA))
local notation "M0" => Measure.pi (fun _ : Fin A => (ProbabilityMeasure.toMeasure μA))
local notation "Z" => Measure.pi (fun _ : Fin A => (volume : Measure unitInterval))
set_option quotPrecheck false in
local notation "θ" => (ProbabilityMeasure.toMeasure (originalIid E (ownH G0 G1 side).val ρ))
set_option quotPrecheck false in
local notation "Ξ" => (M).prod ((volume : Measure unitInterval).prod ν)

lemma numericalValue_inserted (v : ℝ) (price : Icc (E).R (E).Rp)
    (b : Fin A→ Icc (1:ℝ) (E).U) (pub : unitInterval) (payload : RawPayload K H0 H1) :
    OrderedZeroPartialFiberLaw.numericalValue D P t ht hdR H hUH πL π upperBid hupperBid hfloor
      N hfr i kind side v price (b,(pub,payload))=
    insertedValue K A H0 H1 own other physical Q side low (post_card K i kind side)
      v price b pub payload := by
  cases side <;> rfl

lemma numerical_payload_integral (v : ℝ) (price : Icc (E).R (E).Rp) :
    (∫ x,OrderedZeroPartialFiberLaw.numericalValue D P t ht hdR H hUH πL π upperBid hupperBid
      hfloor N hfr i kind side v price x ∂Ξ)=
      ∫ b,∫ pub : unitInterval,∫ row,∫ u : unitInterval,
        value K A own other physical Q low j v price b
          (Function.update row j (Sum.inr price)) pub u
            ∂(volume : Measure unitInterval) ∂θ ∂(volume : Measure unitInterval) ∂M := by
  let f := OrderedZeroPartialFiberLaw.numericalValue D P t ht hdR H hUH πL π upperBid hupperBid
    hfloor N hfr i kind side v price
  have hf : Measurable f := (OrderedZeroPartialFiberLaw.measurable_numericalValue D P t ht hdR H hUH
    πL π upperBid hupperBid hfloor N hfr i kind side v).comp
      (measurable_const.prodMk measurable_id)
  have hb (x) : ‖f x‖≤|v|+D.Up :=
    OrderedZeroPartialFiberLaw.numericalValue_bound D P t ht hdR H hUH πL π upperBid hupperBid
      hfloor N hfr i kind side v price x
  rw [integral_prod _ (integrable_bounded Ξ f hf _ hb)]
  apply integral_congr_ae
  refine ae_of_all _ fun b => ?_
  dsimp only
  rw [integral_prod _ (integrable_bounded ((volume : Measure unitInterval).prod ν)
    (fun x => f (b,x)) (hf.comp (measurable_const.prodMk measurable_id)) _ (fun x => hb (b,x)))]
  apply integral_congr_ae
  refine ae_of_all _ fun pub => ?_
  change (∫ payload,OrderedZeroPartialFiberLaw.numericalValue D P t ht hdR H hUH πL π upperBid
    hupperBid hfloor N hfr i kind side v price (b,(pub,payload)) ∂ν)=_
  simp_rw [numericalValue_inserted D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    N hrare i kind side v price b pub]
  simpa only [focalIndex_eq_cast] using!
    payload_integral K ρ A H0 H1 own other physical Q side low (post_card K i kind side) v price b pub

variable [NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (active D P t ht π).1))]
  [NullSingletonClass ((ProbabilityMeasure.toMeasure (π 2).1).map (fun x=>(x.2:ℝ)))]

theorem numerical_integral_eq (v : ℝ) (price : Icc D.R D.Up) :
    (∫ x,OrderedZeroPartialFiberLaw.numericalValue D P t ht hdR H hUH πL π upperBid hupperBid
      hfloor N hfr i kind side v price x ∂Ξ)=
    ∫ common : Fin A→ Icc (1:ℝ) D.U,
      OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds A (own).val (other).val low j
        ((v,price,μP),common) ∂M0 := by
  rw [numerical_payload_integral D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    N hrare i kind side v price]
  let f := fun (common : Fin A→ Icc (1:ℝ) D.U)
      (x : unitInterval×Row (ownH G0 G1 side).val (E).R (E).Rp (E).H)=>
    ∫ u : unitInterval,value K A own other physical Q low j v price common
      (Function.update x.2 j (Sum.inr price)) x.1 u
  have hf (common) : Measurable (f common) := measurable_integral volume _
    ((OrderedNativePayoffPartialExperiment.measurable_value K A own other physical Q low j v).comp
      (by fun_prop : Measurable (fun x :
        (unitInterval×Row (ownH G0 G1 side).val (E).R (E).Rp (E).H)×unitInterval=>
        (price,(common,(Function.update x.1.2 j (Sum.inr price),(x.1.1,x.2)))))))
  have hb (common x) : ‖f common x‖≤|v|+D.Up := integral_bound volume _ _
    (fun u=> value_bound K A own other physical Q low j v price common _ x.1 u)
  calc
    _=∫ common,OrderedZeroPartialIntegral.originalIntegral D P t ht hdR H hUH πL π upperBid
        hupperBid hfloor N hrare A own other physical low j v price common ∂M := by
      apply integral_congr_ae
      exact ae_of_all _ fun common=> integral_swap_bounded volume θ (f common) (hf common)
        (|v|+D.Up) (hb common)
    _=∫ common,OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds A (own).val (other).val low j
        ((v,price,μP),common) ∂M := integral_congr_ae
      (OrderedZeroPartialIntegral.originalIntegral_eq D P t ht hdR H hUH πL π upperBid hupperBid
        hfloor N hrare A own other physical low j v price)
    _=_ := by
      have he : ρA=μA := ZeroCommonRowLaw.original_common_base_law D P t ht π
      exact congrArg (fun law : ProbabilityMeasure (Icc (1:ℝ) D.U)=>
        ∫ common : Fin A→Icc (1:ℝ) D.U,
          OrderedZeroNoiseFiniteGame.partialOwnRegimeFiber Ds A (own).val (other).val low j
            ((v,price,μP),common) ∂Measure.pi (fun _ : Fin A=>ProbabilityMeasure.toMeasure law)) he

end FCAppendix.Affine.Tail04.OrderedZeroPartialNumericalPayoff
