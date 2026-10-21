import FCAppendix.Affine.Tail04.OriginalFixedNative
import FCAppendix.Affine.Tail04.ClosedUpperPosterior
import FCAppendix.Affine.Tail04.GlobalLowerRoutes

noncomputable section
namespace FCAppendix.Affine.Tail04.ValueParameters
open OriginalValues
open MeasureTheory ProbabilityTheory Set Filter Game Bayes Classical
open Existence.RankEnvelope

variable (P : ValueParameters)

theorem originalFixed_rank_at_floor (m : ℕ) (hm : 200≤ m) :
    rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w)=
      binomBelow (m-1) (activeMass P.theta/2) (marketCapacity m) := by
  have hgt : ∀ᵐ v ∂P.fixedUpperMeasure, P.vA-P.w< v := by
    filter_upwards [P.fixedUpperMeasure_support,
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ:=P.fixedUpperMeasure) (P.vA-P.w))]
      with v hv hne
    exact lt_of_le_of_ne hv (by simpa only [mem_singleton_iff] using Ne.symm hne)
  have htail : P.fixedUpperMeasure.real (Ioi (P.vA-P.w))=activeMass P.theta := by
    rw [←P.fixedUpperMeasure_mass]
    apply measureReal_congr
    filter_upwards [hgt] with v hv
    change (v ∈ Ioi (P.vA-P.w)) = (v ∈ univ)
    simp only [mem_Ioi,hv,mem_univ]
  have hp : activeMass P.theta/2∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg P.active_mass_pos.le (by norm_num),by linarith [P.activeMass_le_one]⟩
  have hc := capacity_bounds m hm
  simp only [rank,contactTail,htail,Nat.cast_ofNat]
  rw [rankSuccess_eq_prob _ _ hp,binomBelow_eq_prob _ _ (by omega) _ hp.1 hp.2]

variable {m : ℕ} (hm : 200≤ m)
  (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
  (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
  (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
  (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1)

def originalFixedReference (PH0 : ProbabilityMeasure (ℝ×JointAction 2)) :
    FiniteGame m 2 (marketCapacity m) unitInterval :=
  ClosedUpperPriority.populationGame C U R (lowMass P.theta) partialMass
    (activeMass P.theta) P.low_mass_pos.le (by norm_num [partialMass])
    P.active_mass_pos.le (mass_sum P.theta) PL PA PH0 η hη0 hη1

theorem originalFixedGame_lower_count
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (i : Fin m) (act : JointAction 2) (ha : act.bid< R) :
    (problem (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) i).outcome act=
      (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).outcome act := by
  exact (ClosedUpperPriority.population_lower_count_law_invariant C U R
    (lowMass P.theta) partialMass (activeMass P.theta) hR.le P.low_mass_pos.le
    (by norm_num [partialMass]) P.active_mass_pos.le (mass_sum P.theta)
    PL PA PH0 (P.originalFixedUpperJoint m hm R hR hRt) hH0
    (P.originalFixedUpperJoint_properties m hm R hR hRt).2.2.1 η hη0 hη1 i act ha).symm

theorem originalFixedGame_lower_payoff
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (i : Fin m) (v : ℝ) (act : JointAction 2) (ha : act.bid< R) :
    (problem (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) i).payoff v act=
      (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).payoff v act := by
  exact (ClosedUpperPriority.population_lower_payoff_invariant C U R
    (lowMass P.theta) partialMass (activeMass P.theta) hR.le P.low_mass_pos.le
    (by norm_num [partialMass]) P.active_mass_pos.le (mass_sum P.theta)
    PL PA PH0 (P.originalFixedUpperJoint m hm R hR hRt) hH0
    (P.originalFixedUpperJoint_properties m hm R hR hRt).2.2.1 η hη0 hη1 i v act ha).symm

theorem originalFixedVersionGame_lower_count
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (i : Fin m) (act : JointAction 2) (ha : act.bid< R) :
    (problem (P.originalFixedVersionGame hm C U R hR hRt PL PA η hη0 hη1) i).outcome act=
      (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).outcome act := by
  rw [P.originalFixedVersionGame_problem hm C U R hR hRt PL PA hVL hVA η hη0 hη1 i]
  exact P.originalFixedGame_lower_count hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 i act ha

theorem originalFixedVersionGame_lower_payoff
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (i : Fin m) (v : ℝ) (act : JointAction 2) (ha : act.bid< R) :
    (problem (P.originalFixedVersionGame hm C U R hR hRt PL PA η hη0 hη1) i).payoff v act=
      (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).payoff v act := by
  rw [P.originalFixedVersionGame_problem hm C U R hR hRt PL PA hVL hVA η hη0 hη1 i]
  exact P.originalFixedGame_lower_payoff hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 i v act ha

theorem originalFixedGame_closedProfiles
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2) :
    ∀ᵐ d ∂userProfileLaw (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1),
      d∈ClosedUpperPriority.closedProfiles m R :=
  ClosedUpperPriority.population_closedProfiles C U R (lowMass P.theta) partialMass
    (activeMass P.theta) P.low_mass_pos.le (by norm_num [partialMass]) P.active_mass_pos.le
    (mass_sum P.theta) PL PA (P.originalFixedUpperJoint m hm R hR hRt) hL hA
    (P.originalFixedUpperJoint_properties m hm R hR hRt).2.2.1 η hη0 hη1

theorem originalFixedReference_closedProfiles
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1) :
    ∀ᵐ d ∂userProfileLaw (P.originalFixedReference C U R PL PA η hη0 hη1 PH0),
      d∈ClosedUpperPriority.closedProfiles m R :=
  ClosedUpperPriority.population_closedProfiles C U R (lowMass P.theta) partialMass
    (activeMass P.theta) P.low_mass_pos.le (by norm_num [partialMass]) P.active_mass_pos.le
    (mass_sum P.theta) PL PA PH0 hL hA hH0 η hη0 hη1

def originalFixedPosterior
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2) :
    PosteriorSystem (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) :=
  ClosedUpperPriority.closedPosterior _ R
    (P.originalFixedGame_closedProfiles hm C U R hR hRt PL PA η hη0 hη1 hL hA)

theorem originalFixedGame_proposers_transfer
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (h02 : PosteriorProposerOptimal (P.originalFixedReference C U R PL PA η hη0 hη1 PH0)
      (ClosedUpperPriority.closedPosterior _ R
        (P.originalFixedReference_closedProfiles C U R PL PA η hη0 hη1 PH0 hL hA hH0))) :
    PosteriorProposerOptimal (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)
      (P.originalFixedPosterior hm C U R hR hRt PL PA η hη0 hη1 hL hA) := by
  exact ClosedUpperPriority.closedPosterior_proposers_transfer C
    (P.originalFixedReference C U R PL PA η hη0 hη1 PH0)
    (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) R hR.le rfl
    (P.originalFixedReference_closedProfiles C U R PL PA η hη0 hη1 PH0 hL hA hH0)
    (P.originalFixedGame_closedProfiles hm C U R hR hRt PL PA η hη0 hη1 hL hA)
    η hη0 hη1.le rfl rfl h02

theorem originalFixedGame_feasible_proposers_transfer
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid< R ∧ x.2.routeCount=2)
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (h02 : ∀ j L,FeasibleObservedList j L → ∀ s,
      Finite.Optimal (marketCapacity m)
        (beliefReceipts (P.originalFixedReference C U R PL PA η hη0 hη1 PH0).A
          (posteriorCountBelief (P.originalFixedReference C U R PL PA η hη0 hη1 PH0)
            (ClosedUpperPriority.closedPosterior _ R
              (P.originalFixedReference_closedProfiles C U R PL PA η hη0 hη1 PH0 hL hA hH0)) j L) L)
        ((P.originalFixedReference C U R PL PA η hη0 hη1 PH0).policy j L s).val) :
    ∀ j L,FeasibleObservedList j L → ∀ s,
      Finite.Optimal (marketCapacity m)
        (beliefReceipts (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1).A
          (posteriorCountBelief (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)
            (P.originalFixedPosterior hm C U R hR hRt PL PA η hη0 hη1 hL hA) j L) L)
        ((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1).policy j L s).val := by
  exact ClosedUpperPriority.closedPosterior_feasible_proposers_transfer C
    (P.originalFixedReference C U R PL PA η hη0 hη1 PH0)
    (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) R hR.le rfl
    (P.originalFixedReference_closedProfiles C U R PL PA η hη0 hη1 PH0 hL hA hH0)
    (P.originalFixedGame_closedProfiles hm C U R hR hRt PL PA η hη0 hη1 hL hA)
    η hη0 hη1.le rfl rfl h02

include hm in
theorem originalFixedReference_floor_payoff
    (hUR : U< R)
    (hLcap : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hAcap : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (hnull0 : ∀ y : ℝ,(PH0 : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0)
    (i : Fin m) (v : ℝ) :
    (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).payoff v
      (⟨R,hR.le,1,by norm_num⟩ : JointAction 2)=
        (v-R)*rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w) := by
  rw [singleton_payoff _ (by norm_num) i _ rfl v]
  change (v-0-R)*meanAcceptProb (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i R=_
  rw [sub_zero,P.originalFixed_rank_at_floor m hm]
  rw [originalFixedReference,ClosedUpperPriority.population_floor_mean C U R (lowMass P.theta) partialMass
    (activeMass P.theta) hR hUR P.low_mass_pos.le (by norm_num [partialMass])
    P.active_mass_pos.le (mass_sum P.theta) PL PA PH0 hLcap hAcap hH0 hnull0 η hη0 hη1 i]

theorem originalFixed_lower_bestResponse_of_reference
    (hUR : U< R)
    (hLcap : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hAcap : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (hnull0 : ∀ y : ℝ,(PH0 : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0)
    (hguard : error (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2) (P.vA-P.w) R<
      η*R*(1-2*(1-rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w))))
    (i : Fin m) (v : ℝ) (hv : v≤ P.vA-P.w) (act : JointAction 2) (ha : act.bid< R)
    (h02 : (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).BestResponse v act) :
    (problem (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) i).BestResponse v act := by
  have hc := capacity_bounds m hm
  apply lower_bestResponse_from_floor_comparison _ η hη0 hη1.le rfl rfl P.fixedUpperMeasure
    (by omega) hc.2.2.1 hc.2.2.2 (P.fixedUpperMeasure_mass_small.trans (by norm_num))
    (P.vA-P.w) R hR hRt P.fixedUpperMeasure_support hguard
    (P.originalFixedGame_mean hm C U R hR hRt hUR PL PA hLcap hAcap η hη0 hη1) i v hv act
  · intro alt hb
    rw [P.originalFixedGame_lower_payoff hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 i v alt hb,
      P.originalFixedGame_lower_payoff hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 i v act ha]
    exact h02 alt
  · rw [P.originalFixedGame_lower_payoff hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 i v act ha]
    rw [←P.originalFixedReference_floor_payoff hm C U R hR PL PA η hη0 hη1
      hUR hLcap hAcap PH0 hH0 hnull0 i v]
    exact h02 _

theorem originalFixed_lower_bestResponse
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (i : Fin m) (v : ℝ) (act : JointAction 2) (ha : act.bid< R)
    (h02restricted : ∀ alt : JointAction 2, alt.bid< R →
      (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).payoff v alt≤
        (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).payoff v act)
    (h02floorCost : max (v-R) 0≤
      (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).payoff v act) :
    (problem (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) i).BestResponse v act := by
  intro alt
  rw [P.originalFixedGame_lower_payoff hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 i v act ha]
  by_cases hb : alt.bid< R
  · rw [P.originalFixedGame_lower_payoff hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 i v alt hb]
    exact h02restricted alt hb
  · exact (GlobalLower.payoff_le_bid_positive_part _ v alt).trans
      ((max_le_max (by change v-0-alt.bid≤ v-R;linarith [le_of_not_gt hb]) le_rfl).trans h02floorCost)

theorem originalFixed_upper_bestResponse
    (hUR : U< R)
    (hLcap : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hAcap : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (PH0 : ProbabilityMeasure (ℝ×JointAction 2))
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (σ : ℝ)
    (hσ : σ< rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w))
    (h02boundary : ∀ (i : Fin m) (act : JointAction 2), act.bid< R →
      (problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).payoff (P.vA-P.w) act≤
        (P.vA-P.w-R)*rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w))
    (h02slopes : ∀ (i : Fin m) (act : JointAction 2), act.bid< R →
      ((problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).outcome act).success≤ σ)
    (hguard : error (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2) (P.vA-P.w) R<
      η*R*(1-2*(1-rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w))))
    (i : Fin m) (v : ℝ) (hv : P.vA-P.w≤ v) :
    (problem (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) i).BestResponse v
      (Hybrid.upperAction (P.originalFixedUpperBid m R) v) := by
  have hc := capacity_bounds m hm
  apply native_original_upper_all_actions _ η hη0 hη1.le rfl rfl P.fixedUpperMeasure
    (by omega) hc.2.2.1 hc.2.2.2 (P.fixedUpperMeasure_mass_small.trans (by norm_num))
    (P.vA-P.w) R σ hR hRt P.fixedUpperMeasure_support
    (original_fixed_upper_integrable_error P.fixedUpperMeasure P.fixedUpperMeasure_mass_small
      (P.vA-P.w) R P.M (activeMass P.theta*P.zeta) P.fixedUpperBase_pos hRt.le
      P.fixedUpperBase_le_tail P.original_tail_weight_bounds P.fixedUpperMeasure_tail m hm).1 hguard
    (P.originalFixedGame_mean hm C U R hR hRt hUR PL PA hLcap hAcap η hη0 hη1) hσ
    _ _ i v hv
  · intro j act ha
    rw [P.originalFixedGame_lower_payoff hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 j (P.vA-P.w) act ha]
    exact h02boundary j act ha
  · intro j act ha
    rw [P.originalFixedGame_lower_count hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 j act ha]
    exact h02slopes j act ha

end FCAppendix.Affine.Tail04.ValueParameters
namespace FCAppendix.Affine.Tail04.OriginalValues
export FCAppendix.Affine.Tail04.ValueParameters (originalFixed_rank_at_floor originalFixedReference originalFixedGame_lower_count originalFixedGame_lower_payoff originalFixedVersionGame_lower_count originalFixedVersionGame_lower_payoff originalFixedGame_closedProfiles originalFixedReference_closedProfiles originalFixedPosterior originalFixedGame_proposers_transfer originalFixedGame_feasible_proposers_transfer originalFixedReference_floor_payoff originalFixed_lower_bestResponse_of_reference originalFixed_lower_bestResponse originalFixed_upper_bestResponse)
end FCAppendix.Affine.Tail04.OriginalValues
