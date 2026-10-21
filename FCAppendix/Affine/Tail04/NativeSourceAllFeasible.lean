import FCAppendix.Affine.Tail04.NativeSourcePosterior
import FCAppendix.Affine.Tail04.NativeFallbackReceipts
import FCAppendix.Affine.Tail04.FeasibleListNormalization

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeSourceAllFeasible
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open OriginalValues OriginalPopulation OriginalPrivateSource NativeLocalPolicy
open NativeSourcePolicy Existence.Distributional EqualPrivateSignal EqualPrivateUpper
open PosteriorReceiptNormalization

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

variable (hrare : (1-ξ)*E.U+ξ*E.U*((m:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ E.R)
    (hdup : (1-ξ)*E.U<1)

section GivenGame
variable (Γ : FiniteGame m 2 c Seed)
    (hjoint : Γ.F ⊗ₘ Γ.σ=(originalJoint P t ht E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le) πL πP πA upperBid hupperBid : Measure (ℝ×JointAction 2)))
    (hseed : Γ.seedLaw=seedLaw)
    (hpolicy : ∀ j,Γ.policy j=(NativeSourcePolicy.data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup).completedPolicy j)
    (B : PosteriorSystem Γ)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hcoef : (1-η)/2=ξ)

include hseed hpolicy η hη0 hη1 hA hcoef in
theorem completion_receipts (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    receipts Γ (PrivateFallbackKernel.kernel E (OriginalPrivateSource.originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor)) j L=((NativeSourcePolicy.data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).completedNumericalReceipt (j) L :=
  NativeFallbackReceipts.receipts_eq (NativeSourcePolicy.data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup) (OriginalPrivateSource.originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor) (fun _ => rfl) Γ hseed hpolicy η hη0 hη1 hA hcoef j L hL

include ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup hjoint hseed hpolicy η hη0 hη1 hA hcoef in
theorem original_completion_agree (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j,receipts Γ B.posterior j L=receipts Γ (PrivateFallbackKernel.kernel E (OriginalPrivateSource.originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor)) j L := by
  filter_upwards [NativeSourcePosterior.receipt_vector E P hd t ht πL πP πA
    upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup
    Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef j] with L hL
  exact hL.2.2.trans (completion_receipts E P hd t ht πL πP πA upperBid hupperBid hfloor
    m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup
    Γ hseed hpolicy η hη0 hη1 hA hcoef j L hL.1).symm

def posterior : PosteriorSystem Γ :=
  PosteriorReceiptNormalization.normalized Γ (PrivateFallbackKernel.kernel E (OriginalPrivateSource.originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor)) B
    (original_completion_agree E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup
      Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef)
    (PrivateFallbackKernel.kernel_feasible E (OriginalPrivateSource.originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor))

theorem posterior_receipts (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    beliefReceipts Γ.A (posteriorCountBelief Γ (posterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef) j L) L=((NativeSourcePolicy.data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).completedNumericalReceipt (j) L := by
  rw [posterior,PosteriorReceiptNormalization.normalized_receipts]
  exact completion_receipts E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup
    Γ hseed hpolicy η hη0 hη1 hA hcoef j L hL

theorem optimal_every_seed (hlow : E.d<1-ξ) (j : Fin 2) (L : LocalList m)
    (hL : FeasibleObservedList j L) (u : Seed) :
    Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ (posterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef) j L) L)
      ((Γ.policy j L u).val) := by
  have hn := (feasibleObservedList_iff_nonnegative j L).mp hL
  rw [posterior_receipts E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup
    Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef j L hn,hpolicy j]
  exact (NativeSourcePolicy.data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup).completed_numerical_optimal hlow j L hn u

theorem optimal_all_feasible (hlow : E.d<1-ξ) : PosteriorProposerOptimalAE Γ (posterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef) := by
  intro j L hL
  exact ae_of_all _ (optimal_every_seed E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup
    Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef hlow j L hL)

theorem optimal_all_lists (hlow : E.d<1-ξ) :
    PosteriorProposerOptimal (FeasibleListNormalization.game Γ)
      (FeasibleListNormalization.posterior Γ (posterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef)) :=
  FeasibleListNormalization.proposers Γ (posterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef)
    (optimal_every_seed E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup
      Γ hjoint hseed hpolicy B η hη0 hη1 hA hcoef hlow)

end GivenGame

variable (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)

def initialPosterior : PosteriorSystem (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) := Classical.choice (exists_posteriorSystem (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1))

variable (hcoef : (1-η)/2=ξ)

def nativePosterior : PosteriorSystem (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) :=
  posterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    (NativeSourcePosterior.game_original_joint E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    rfl (fun _ => rfl)
    (initialPosterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    η hη0 hη1 rfl hcoef

theorem native_optimal_all_feasible (hlow : E.d<1-ξ) : PosteriorProposerOptimalAE (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) (nativePosterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1 hcoef) :=
  optimal_all_feasible E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    (NativeSourcePosterior.game_original_joint E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    rfl (fun _ => rfl)
    (initialPosterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    η hη0 hη1 rfl hcoef hlow

def nativeGame : FiniteGame m 2 c Seed := FeasibleListNormalization.game (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)

def nativeAllListPosterior : PosteriorSystem
    (nativeGame E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) :=
  FeasibleListNormalization.posterior (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) (nativePosterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1 hcoef)

theorem native_all_list_optimal (hlow : E.d<1-ξ) :
    PosteriorProposerOptimal
      (nativeGame E P hd t ht πL πP πA upperBid hupperBid hfloor m c
        ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
      (nativeAllListPosterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c
        ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1 hcoef) :=
  optimal_all_lists E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    (NativeSourcePosterior.game_original_joint E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    rfl (fun _ => rfl)
    (initialPosterior E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1)
    η hη0 hη1 rfl hcoef hlow

theorem native_original_value :
    (nativeGame E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1).F=valueLaw P := rfl

theorem native_all_raw_problem (i : Fin m) :
    problem (nativeGame E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) i=problem (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) i :=
  FeasibleListNormalization.problem_eq (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) i

theorem native_fixed_value_count (hm : 0< m) (v : ℝ) :
    conditionalTypeCountLaw (nativeGame E P hd t ht πL πP πA upperBid hupperBid hfloor m c
      ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) hm v=
      conditionalTypeCountLaw (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) hm v :=
  FeasibleListNormalization.conditionalCount_eq (NativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1) hm v

end FCAppendix.Affine.Tail04.NativeSourceAllFeasible
