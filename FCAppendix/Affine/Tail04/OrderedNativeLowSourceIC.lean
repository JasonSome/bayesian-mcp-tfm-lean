import FCAppendix.Affine.Tail04.OrderedNativeLowTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeLowSourceIC
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid LowBody NativeLocalPolicy NativeLowSourceIC
open OriginalValues OriginalPopulation Existence.Distributional

variable (P : ValueParameters) (t : ℝ) (ht : P.M≤t)

variable (E : Observable.Regions) (hd : E.d=P.d0) (N c : ℕ)
  (ξ width θ eA eR B0 : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1) (hwidth : 0< width)
  (hθ0 : 0≤ θ) (hθ1 : θ≤1)
  (L : ActualAtomlessLowLimit N P.d0 ξ c (categories P t ht) P.originalLowLaw)

local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht

variable (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ E.H≤ upperBid v)

variable (hrare : (1-ξ)*E.U+ξ*E.U*((N+1:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ E.R)
  (hdup : (1-ξ)*E.U<1)
  (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1) (hcoef : (1-η)/2=ξ)

variable (hell : 0<(CommonList.iid (categories P t ht) N).prob (LocalUnderflow c 0))
  (hsmall : (CommonList.iid (categories P t ht) N).prob (BothUnderflow c)≤
    (CommonList.iid (categories P t ht) N).prob (LocalUnderflow c 0)/4)

set_option quotPrecheck false in
local notation "D" => NativeSourcePolicy.data E P hd t ht L.joint πP πA upperBid hupperBid hfloor (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup
set_option quotPrecheck false in
local notation "Γ" => NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1
set_option quotPrecheck false in
local notation "Γo" => OrderedNativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1

lemma ordered_game_eq : Γo=OrderedNativeLowTransport.orderedGame D Γ := rfl

include hcoef hell hsmall in
theorem original_low_all_labels :
    ∀ᵐx ∂(lowJoint P.originalLowLaw L.joint : Measure (ℝ×JointAction 2)),
      ∀i : Fin (N+1),(problem Γo i).BestResponse x.1 x.2 := by
  have hbest:=NativeLowSourceIC.original_low_all_labels P t ht E hd N c
    ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 L πP πA upperBid hupperBid hfloor
    hrare hdup η hη0 hη1 hcoef hell hsmall
  have hprof:=NativeLowSourceIC.original_profiles_on_menu P t ht E hd N c
    ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 L πP πA upperBid hupperBid hfloor
    hrare hdup η hη0 hη1
  have hs : ∀ᵐx ∂(lowJoint P.originalLowLaw L.joint : Measure (ℝ×JointAction 2)),
      x.1≤P.d0 ∧ x.2.bid≤P.d0 := by
    apply (measurableEmbedding_lowJointPoint P.d0).ae_map_iff.mpr
    exact ae_of_all _ (fun x=>⟨x.1.2.2,x.2.2.2⟩)
  filter_upwards [hbest,hs] with x hx hsx
  intro i
  change (problem (OrderedNativeLowTransport.orderedGame D Γ) i).BestResponse x.1 x.2
  apply OrderedNativeLowTransport.bestResponse D Γ rfl hprof i x.1
    (by change x.1≤E.d;simpa only [hd] using hsx.1) x.2
    (by change x.2.bid≤E.d;simpa only [hd] using hsx.2)
  exact hx i

include hcoef hell hsmall in

theorem normalized_low_all_labels :
    ∀ᵐx ∂(lowJoint P.originalLowLaw L.joint : Measure (ℝ×JointAction 2)),
      ∀i : Fin (N+1),
        (problem (FeasibleListNormalization.game Γo) i).BestResponse x.1 x.2 := by
  simpa only [FeasibleListNormalization.problem_eq] using
    original_low_all_labels P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1 hcoef hell hsmall

end FCAppendix.Affine.Tail04.OrderedNativeLowSourceIC
