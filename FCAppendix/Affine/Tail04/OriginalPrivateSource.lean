import FCAppendix.Affine.Tail04.OriginalPrivateEntry
import FCAppendix.Affine.Hybrid.CollapsedProfile

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalPrivateSource
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open Existence.Distributional OriginalPopulation OriginalValues OriginalPrivateEntry
open EqualPrivateSignal EqualPrivateUpper Hybrid

lemma event_real_from_original_value (Q : ProbabilityMeasure (ℝ × JointAction 2))
    (F : Measure ℝ) (hF : (Q : Measure (ℝ × JointAction 2)).map Prod.fst=F)
    (E : Set (ℝ × JointAction 2)) (V : Set ℝ) (hV : MeasurableSet V)
    (hshape : ∀ᵐ x ∂(Q : Measure (ℝ × JointAction 2)),x∈E ↔ x.1∈V) :
    (Q : Measure (ℝ × JointAction 2)).real E=F.real V := by
  have he : (Q : Measure (ℝ × JointAction 2)) E=
      (Q : Measure (ℝ × JointAction 2)) (Prod.fst ⁻¹' V) :=
    measure_congr (hshape.mono (fun _ hx=>propext hx))
  rw [measureReal_def,he,← Measure.map_apply measurable_fst hV,hF]
  rfl

variable (E : Observable.Regions) (P : ValueParameters) (hd : E.d=P.d0)
variable (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
    (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → E.H≤ upperBid v)
local notation "hR" => E.d_nonneg.trans E.d_lt_R.le
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "J" => originalJoint P t ht E.R E.Rp E.U hR πL πP πA upperBid hupperBid

include hd hfloor in
theorem original_private_mass :
    (J : Measure (ℝ × JointAction 2)).real E.privateJointEvent=partialMass+z := by
  have hshape := originalJoint_role_correspondence P E hd t ht πL πP πA upperBid hupperBid hfloor
  rw [event_real_from_original_value J (valueLaw P)
    (originalJoint_value P t ht E.R E.Rp E.U hR πL πP πA upperBid hupperBid)
    E.privateJointEvent (P.privateValues t) (measurableSet_Icc.union measurableSet_Ioi)
    (hshape.mono (fun _ hx => hx.2.1)),P.private_mass t ht]

include hd hfloor in
theorem original_upper_mass :
    (J : Measure (ℝ × JointAction 2)).real E.upperJointEvent=z := by
  have hshape := originalJoint_role_correspondence P E hd t ht πL πP πA upperBid hupperBid hfloor
  rw [event_real_from_original_value J (valueLaw P)
    (originalJoint_value P t ht E.R E.Rp E.U hR πL πP πA upperBid hupperBid)
    E.upperJointEvent (Ioi t) measurableSet_Ioi
    (hshape.mono (fun _ hx => hx.2.2)),P.real_tail t ht]

include hd hfloor in
lemma original_private_positive :
    0<(J : Measure (ℝ × JointAction 2)).real E.privateJointEvent := by
  rw [original_private_mass E P hd t ht πL πP πA upperBid hupperBid hfloor]
  have hz := P.tailMass_nonneg t ht
  norm_num [partialMass] at *
  linarith

def originalEntryLaw : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp) :=
  entryLaw E J (original_private_positive E P hd t ht πL πP πA upperBid hupperBid hfloor)

theorem native_originalEntryLaw {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (hjoint : Γ.F ⊗ₘ Γ.σ=(J : Measure (ℝ × JointAction 2)))
    (j : Fin 2) :
    (cond (userLaw Γ) (E.coarseTag ⁻¹' {Hybrid.NativeContinuation.upperTag j})).map
      (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid)=
      (originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor :
        Measure (Ici E.H ⊕ Icc E.R E.Rp)) :=
  native_entryLaw_given_tag E Γ J hjoint
    (original_private_positive E P hd t ht πL πP πA upperBid hupperBid hfloor) j

theorem original_upperProbability :
    PrivateRowSorting.upperProbability E
      (originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor)=
      z/(partialMass+z) := by
  rw [originalEntryLaw,upperProbability_entryLaw,
    original_upper_mass E P hd t ht πL πP πA upperBid hupperBid hfloor,
    original_private_mass E P hd t ht πL πP πA upperBid hupperBid hfloor]

def originalPrivateRow (H : ℕ) : ProbabilityMeasure (Row H E.R E.Rp E.H) :=
  PrivateRowSorting.sortedOriginalIid E H
    (originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor)

theorem originalPrivateRow_anyUpper (H : ℕ) :
    (AtypicalOriginalPosterior.markLaw
      (originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor H :
        Measure (Row H E.R E.Rp E.H))).prob
        AtypicalOriginalPosterior.anyUpper≤(H:ℝ)*(z/(partialMass+z)) := by
  have h := PrivateRowSorting.sortedOriginalIid_anyUpper E H
    (originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor)
  rw [original_upperProbability E P hd t ht πL πP πA upperBid hupperBid hfloor] at h
  exact h

theorem originalPrivateRow_countMean (H : ℕ) :
    (AtypicalOriginalPosterior.markLaw
      (originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor H :
        Measure (Row H E.R E.Rp E.H))).expect
        (fun marks => (upperCount marks:ℝ))=(H:ℝ)*(z/(partialMass+z)) := by
  have h := PrivateRowSorting.sortedOriginalIid_countMean E H
    (originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor)
  rw [original_upperProbability E P hd t ht πL πP πA upperBid hupperBid hfloor] at h
  exact h

include hd hfloor in
theorem original_low_broadcast :
    ∀ᵐ x ∂(J : Measure (ℝ × JointAction 2)),x.2.bid≤ E.d → x.2.routeCount=2 :=
  (originalJoint_sourceBands P E hd t ht πL πP πA upperBid hupperBid hfloor).mono
    (fun x hx => ObservedScenario.sourceBands_low_broadcast E P t x hx)

end FCAppendix.Affine.Tail04.OriginalPrivateSource
