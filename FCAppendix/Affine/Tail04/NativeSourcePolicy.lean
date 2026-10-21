import FCAppendix.Affine.Tail04.CompletedNativePolicy
import FCAppendix.Affine.Tail04.NativePrivatePosterior
import FCAppendix.Affine.Tail04.PublicScenario

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeSourcePolicy
open MeasureTheory ProbabilityTheory Set Game Bayes
open OriginalValues OriginalPopulation OriginalPrivateSource
open Existence.Distributional EqualPrivateSignal EqualPrivateUpper

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

def publicData : PublicScenario.Data where
  c := c
  ξ := ξ
  θ := θ
  eA := eA
  eR := eR
  B0 := B0
  θ_nonneg := hθ0
  θ_le_one := hθ1
  marksLaw H := AtypicalOriginalPosterior.markLaw (((originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor) H) : Measure (Row H E.R E.Rp E.H))

variable (hrare : (1-ξ)*E.U+ξ*E.U*((m:ℝ)*(activeMass P.theta*P.zeta*powerTail P.M 10 t / (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ E.R)
    (hdup : (1-ξ)*E.U<1)

def data : NativeLocalPolicy.Data m c where
  E := E
  ξ := ξ
  width := width
  π := (activeMass P.theta*P.zeta*powerTail P.M 10 t / (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t))
  xi_pos := hξ0
  xi_lt_one := hξ1
  width_pos := hwidth
  pi_nonneg := div_nonneg (P.tailMass_nonneg t ht)
    (by have hz:=P.tailMass_nonneg t ht;norm_num [partialMass] at *;linarith)
  rare_upper := hrare
  duplicate_below_active := hdup
  originalPrivateRow H := (originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor) H.val
  any_upper H := originalPrivateRow_anyUpper E P hd t ht πL πP πA upperBid hupperBid hfloor H.val
  publicChoice N := PublicScenario.localChoice E
    (publicData E P hd t ht πL πP πA upperBid hupperBid hfloor c ξ θ eA eR B0 hθ0 hθ1)
    (LowBody.realLowBidLaw πL.1) N
  publicChoice_measurable N := PublicScenario.measurable_localChoice E
    (publicData E P hd t ht πL πP πA upperBid hupperBid hfloor c ξ θ eA eR B0 hθ0 hθ1)
    (LowBody.realLowBidLaw πL.1) N m

@[simp] theorem data_privateRow (H : Fin (m+1)) : ((data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).originalPrivateRow H=(originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor) H.val := rfl

@[simp] theorem data_marksLaw (H : Fin (m+1)) :
    ((data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).marksLaw H=AtypicalOriginalPosterior.markLaw (((originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor) H.val) : Measure (Row H.val E.R E.Rp E.H)) := rfl

@[simp] theorem data_common_choice (N : ℕ) : ((data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).publicChoice N=
    PublicScenario.localChoice (m:=m) E
      (publicData E P hd t ht πL πP πA upperBid hupperBid hfloor c ξ θ eA eR B0 hθ0 hθ1)
      (LowBody.realLowBidLaw πL.1) N := rfl

def policy (j : Fin 2) : LocalPolicy m c NativeLocalPolicy.Seed := ((data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).completedPolicy j

theorem policy_measurable (j : Fin 2) :
    Measurable (fun z : LocalList m×NativeLocalPolicy.Seed => (policy E P hd t ht πL πP πA
      upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup j z.1 z.2).val) :=
  ((data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).completedPolicy_measurable j

theorem policy_on_menu (j : Fin 2) (L : LocalList m) (hL : ((data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).offCommon L=∅)
    (u : NativeLocalPolicy.Seed) :
    policy E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0
      hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup j L u=((data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).policy j L u :=
  ((data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup)).completed_on_menu j L hL u

theorem data_original_private_posterior {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed)
    (hjoint : Γ.F ⊗ₘ Γ.σ=(originalJoint P t ht E.R E.Rp E.U
      (E.d_nonneg.trans E.d_lt_R.le) πL πP πA upperBid hupperBid : Measure _))
    (B : PosteriorSystem Γ) (j : Fin 2)
    (k : Fin m → Bool) (H : Fin (m+1))
    (e : Fin H.val ≃ {i : Fin m // k i=true}) :
    ∀ᵐ L ∂observedListLaw Γ j,L∈MissingRowPosterior.patternEvent k →
      (B.posterior j L).map
        (MissingRowPosterior.sortedMissingRow E (NativePrivatePosterior.observedEntry j)
          k H.val e (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid))=
        (↑(show ProbabilityMeasure (Row H.val E.R E.Rp E.H) from
          (data E P hd t ht πL πP πA upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup).originalPrivateRow H) : Measure _) :=
  NativePrivatePosterior.original_finite_private_posterior E P hd t ht πL πP πA
    upperBid hupperBid hfloor Γ hjoint B j k H.val e

end FCAppendix.Affine.Tail04.NativeSourcePolicy
