import FCAppendix.Affine.Tail04.NativeSourcePolicy
import FCAppendix.Affine.Tail04.NativeBayesianReceipts

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeSourcePosterior
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open OriginalValues OriginalPopulation OriginalPrivateSource NativeSourcePolicy
open NativeLocalPolicy Existence.Distributional EqualPrivateSignal EqualPrivateUpper

variable (E : Observable.Regions) (P : ValueParameters) (hd : E.d=P.d0)
    (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
    (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → E.H≤ upperBid v)
    (m c : ℕ) (ξ width θ eA eR B0 : ℝ)
    (hξ0 : 0< ξ) (hξ1 : ξ<1) (hwidth : 0< width)
    (hθ0 : 0≤ θ) (hθ1 : θ≤1)

local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "π" => z/(partialMass+z)
variable (hrare : (1-ξ)*E.U+ξ*E.U*((m:ℝ)*(activeMass P.theta*P.zeta*powerTail P.M 10 t / (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ E.R)
    (hdup : (1-ξ)*E.U<1)
local notation "D" => NativeSourcePolicy.data E P hd t ht πL πP πA upperBid hupperBid hfloor m c
  ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup
local notation "J" => originalJoint P t ht E.R E.Rp E.U
  (E.d_nonneg.trans E.d_lt_R.le) πL πP πA upperBid hupperBid

section GivenGame
variable (Γ : FiniteGame m 2 c Seed)
    (hjoint : Γ.F ⊗ₘ Γ.σ=(originalJoint P t ht E.R E.Rp E.U
      (E.d_nonneg.trans E.d_lt_R.le) πL πP πA upperBid hupperBid : Measure (ℝ×JointAction 2)))
    (hseed : Γ.seedLaw=seedLaw)
    (hpolicy : ∀ j,Γ.policy j=(NativeSourcePolicy.data E P hd t ht πL πP πA
      upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup).completedPolicy j)
    (B : PosteriorSystem Γ)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hcoef : (1-η)/2=ξ)

include hjoint hseed hpolicy η hη0 hη1 hA hcoef in
theorem receipt_vector (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j,
      NonnegativeList L ∧ (D).offCommon L=∅ ∧
      beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L=(D).completedNumericalReceipt j L :=
  NativeBayesianReceipts.original_receipt_vector D P hd t ht πL πP πA
    upperBid hupperBid hfloor (fun _ => rfl) Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef j

include P hd t ht πL πP πA upperBid hupperBid hfloor width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup hjoint hseed hpolicy η hη0 hη1 hA hcoef in
theorem proposer_onPath (hlow : E.d<1-ξ) (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j,∀ u : Seed,
      Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L)
        ((Γ.policy j L u).val) :=
  NativeBayesianReceipts.original_proposer_onPath D P hd t ht πL πP πA
    upperBid hupperBid hfloor (fun _ => rfl) Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef hlow j

include P hd t ht πL πP πA upperBid hupperBid hfloor width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup hjoint hseed hpolicy B η hη0 hη1 hA hcoef in
theorem rationalOnPath (hlow : E.d<1-ξ) (j : Fin 2) : ProposerRationalOnPath Γ j :=
  NativeBayesianReceipts.original_rationalOnPath D P hd t ht πL πP πA
    upperBid hupperBid hfloor (fun _ => rfl) Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef hlow j

end GivenGame

variable (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)

def game : FiniteGame m 2 c Seed :=
  OriginalPopulation.nativeGame P t ht E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le)
    πL πP πA upperBid hupperBid m c seedLaw (D).completedPolicy (D).completedPolicy_measurable η hη0 hη1

local notation "Γ₀" => game E P hd t ht πL πP πA upperBid hupperBid hfloor m c
  ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1

theorem game_original_value : (Γ₀).F=valueLaw P := rfl

theorem game_original_joint : (Γ₀).F ⊗ₘ (Γ₀).σ=(J : Measure (ℝ×JointAction 2)) :=
  OriginalPopulation.native_joint P t ht E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le)
    πL πP πA upperBid hupperBid m c seedLaw (D).completedPolicy (D).completedPolicy_measurable η hη0 hη1

theorem game_original_user : userLaw Γ₀=(J : Measure (ℝ×JointAction 2)).prod (permLaw 2) := by
  rw [userLaw,game_original_joint]

theorem game_original_profile : userProfileLaw Γ₀=
    Measure.pi (fun _ : Fin m => (J : Measure (ℝ×JointAction 2)).prod (permLaw 2)) := by
  simp only [userProfileLaw,game_original_user]

theorem game_receipt_vector (B : PosteriorSystem Γ₀) (hcoef : (1-η)/2=ξ) (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ₀ j,
      NonnegativeList L ∧ (D).offCommon L=∅ ∧
      beliefReceipts (Γ₀).A (posteriorCountBelief Γ₀ B j L) L=(D).completedNumericalReceipt j L :=
  receipt_vector E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup Γ₀
    (game_original_joint E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    rfl (fun _ => rfl) B η hη0 hη1 rfl hcoef j

theorem game_rationalOnPath (B : PosteriorSystem Γ₀) (hcoef : (1-η)/2=ξ)
    (hlow : E.d<1-ξ) (j : Fin 2) : ProposerRationalOnPath Γ₀ j :=
  rationalOnPath E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup Γ₀
    (game_original_joint E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    rfl (fun _ => rfl) B η hη0 hη1 rfl hcoef hlow j

end FCAppendix.Affine.Tail04.NativeSourcePosterior
