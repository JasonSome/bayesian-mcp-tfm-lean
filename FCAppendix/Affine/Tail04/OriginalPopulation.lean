import FCAppendix.Affine.Tail04.SourceValuePartition
import FCAppendix.Affine.Hybrid.PopulationLaw
import FCAppendix.Affine.Hybrid.UpperLaw
import FCAppendix.Game.PosteriorBeliefs

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalPopulation
open MeasureTheory ProbabilityTheory Set Filter Game Bayes
open Existence.Distributional OriginalValues Hybrid

local instance : Nonempty (JointAction 2) := ⟨Interim.abstain 2⟩

def bandAction {L U : ℝ} (hL : 0 ≤ L) (k : ℕ) (hk : k ≤ 2)
    (b : Icc L U) : JointAction 2 :=
  ⟨b.1, hL.trans b.2.1, k, hk⟩

theorem measurable_bandAction {L U : ℝ} (hL : 0 ≤ L) (k : ℕ) (hk : k ≤ 2) :
    Measurable (bandAction (U:=U) hL k hk) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  exact (measurable_subtype_coe.prodMk measurable_const).comap_le

def bandJoint {vL vU L U : ℝ} (hL : 0 ≤ L) (k : ℕ) (hk : k ≤ 2)
    (μ : Measure (Icc vL vU)) [IsProbabilityMeasure μ]
    (π : Law (A:=Icc L U) μ) : ProbabilityMeasure (ℝ × JointAction 2) :=
  π.1.map (measurable_fst.subtype_val.prodMk
    ((measurable_bandAction hL k hk).comp measurable_snd)).aemeasurable

theorem bandJoint_value {vL vU L U : ℝ} (hL : 0 ≤ L) (k : ℕ) (hk : k ≤ 2)
    (μ : Measure (Icc vL vU)) [IsProbabilityMeasure μ]
    (π : Law (A:=Icc L U) μ) :
    (bandJoint hL k hk μ π : Measure (ℝ × JointAction 2)).map Prod.fst =
      μ.map Subtype.val := by
  change ((π.1 : Measure (Icc vL vU × Icc L U)).map
    (fun x => ((x.1:ℝ), bandAction hL k hk x.2))).map Prod.fst = _
  have hf : Measurable (fun x : Icc vL vU × Icc L U =>
      ((x.1:ℝ), bandAction hL k hk x.2)) :=
    measurable_fst.subtype_val.prodMk ((measurable_bandAction hL k hk).comp measurable_snd)
  rw [Measure.map_map measurable_fst hf]
  calc
    _ = ((π.1 : Measure (Icc vL vU × Icc L U)).map Prod.fst).map Subtype.val :=
      (Measure.map_map measurable_subtype_coe measurable_fst).symm
    _ = _ := by rw [π.2]

theorem bandJoint_support {vL vU L U : ℝ} (hL : 0 ≤ L) (k : ℕ) (hk : k ≤ 2)
    (μ : Measure (Icc vL vU)) [IsProbabilityMeasure μ]
    (π : Law (A:=Icc L U) μ) :
    ∀ᵐ x ∂(bandJoint hL k hk μ π : Measure (ℝ × JointAction 2)),
      x.1 ∈ Icc vL vU ∧ x.2.bid ∈ Icc L U ∧ x.2.routeCount = k := by
  apply (ae_map_iff
    (measurable_fst.subtype_val.prodMk
      ((measurable_bandAction hL k hk).comp measurable_snd)).aemeasurable
    ((measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_Icc.preimage ((measurable_bid 2).comp measurable_snd)).inter
        (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd)
          measurable_const)))).mpr
  exact Eventually.of_forall (fun x => ⟨x.1.2, x.2.2, rfl⟩)

def fourJoint (s h a z : ℝ)
    (PL PP PA PH : ProbabilityMeasure (ℝ × JointAction 2)) :
    Measure (ℝ × JointAction 2) :=
  ENNReal.ofReal s • (PL : Measure (ℝ × JointAction 2)) +
    ENNReal.ofReal h • (PP : Measure (ℝ × JointAction 2)) +
    ENNReal.ofReal a • (PA : Measure (ℝ × JointAction 2)) +
    ENNReal.ofReal z • (PH : Measure (ℝ × JointAction 2))

theorem fourJoint_probability (s h a z : ℝ)
    (hs : 0 ≤ s) (hh : 0 ≤ h) (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hsum : s+h+a+z=1)
    (PL PP PA PH : ProbabilityMeasure (ℝ × JointAction 2)) :
    IsProbabilityMeasure (fourJoint s h a z PL PP PA PH) := by
  constructor
  simp only [fourJoint, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_add hs hh,
    ← ENNReal.ofReal_add (add_nonneg hs hh) ha,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hs hh) ha) hz,
    hsum, ENNReal.ofReal_one]

theorem fourJoint_value (s h a z : ℝ)
    (PL PP PA PH : ProbabilityMeasure (ℝ × JointAction 2)) :
    (fourJoint s h a z PL PP PA PH).map Prod.fst =
      ENNReal.ofReal s • (PL : Measure (ℝ × JointAction 2)).map Prod.fst +
      ENNReal.ofReal h • (PP : Measure (ℝ × JointAction 2)).map Prod.fst +
      ENNReal.ofReal a • (PA : Measure (ℝ × JointAction 2)).map Prod.fst +
      ENNReal.ofReal z • (PH : Measure (ℝ × JointAction 2)).map Prod.fst := by
  simp only [fourJoint, Measure.map_add _ _ measurable_fst, Measure.map_smul]

section Source
variable (P : ValueParameters) (t : ℝ) (ht : P.M ≤ t)
  (R Rp U : ℝ) (hR : 0 ≤ R)

local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht

variable
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc R Rp) P.originalPartialLaw)
  (πA : Law (A:=Icc (1:ℝ) U) (P.originalMovingActiveLaw t ht))
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)

def originalJoint : ProbabilityMeasure (ℝ × JointAction 2) := by
  let z := activeMass P.theta*P.zeta*powerTail P.M 10 t
  let PL := lowJoint P.originalLowLaw πL
  let PP := bandJoint hR 1 (by norm_num) P.originalPartialLaw πP
  let PA := bandJoint (by norm_num : (0:ℝ) ≤ 1) 2 le_rfl
    (P.originalMovingActiveLaw t ht) πA
  let FH : ProbabilityMeasure ℝ :=
    ⟨P.originalMovingUpperLaw t, P.originalMovingUpperLaw_probability t⟩
  let PH := upperJoint FH upperBid hupperBid
  refine ⟨fourJoint (lowMass P.theta) partialMass (activeMass P.theta-z) z PL PP PA PH, ?_⟩
  apply fourJoint_probability
  · exact P.low_mass_pos.le
  · norm_num [partialMass]
  · exact (P.movingActiveMass_positive t ht).le
  · exact P.tailMass_nonneg t ht
  · linarith [mass_sum P.theta]

theorem originalJoint_value :
    (originalJoint P t ht R Rp U hR πL πP πA upperBid hupperBid :
      Measure (ℝ × JointAction 2)).map Prod.fst = valueLaw P := by
  dsimp only [originalJoint,ProbabilityMeasure.coe_mk]
  rw [fourJoint_value, lowJoint_value_marginal,
    bandJoint_value, bandJoint_value, upperJoint_value_marginal]
  exact P.moving_weighted_value_partition t ht

section Native
variable (m c : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Fin 2 → LocalPolicy m c Seed)
    (hpolicy : ∀ j, Measurable (fun p : LocalList m × Seed => (policy j p.1 p.2).val))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)

def nativeGame : FiniteGame m 2 c Seed where
  F := valueLaw P
  hF := inferInstance
  σ := (originalJoint P t ht R Rp U hR πL πP πA upperBid hupperBid :
    Measure (ℝ × JointAction 2)).condKernel
  hσ := inferInstance
  seedLaw := ν
  hseed := inferInstance
  policy := policy
  policy_measurable := hpolicy
  A := Schedule.affine 2 η hη0 hη1
  G := Schedule.once 2
  g := 0
  g_nonneg := le_rfl

theorem native_joint : (nativeGame P t ht R Rp U hR πL πP πA upperBid hupperBid m c ν policy hpolicy η hη0 hη1).F ⊗ₘ (nativeGame P t ht R Rp U hR πL πP πA upperBid hupperBid m c ν policy hpolicy η hη0 hη1).σ =
    (originalJoint P t ht R Rp U hR πL πP πA upperBid hupperBid :
      Measure (ℝ × JointAction 2)) := by
  change valueLaw P ⊗ₘ (originalJoint P t ht R Rp U hR πL πP πA upperBid hupperBid :
    Measure (ℝ × JointAction 2)).condKernel = _
  rw [← originalJoint_value P t ht R Rp U hR πL πP πA upperBid hupperBid]
  exact Measure.disintegrate _ _

theorem native_original_value : (nativeGame P t ht R Rp U hR πL πP πA upperBid hupperBid m c ν policy hpolicy η hη0 hη1).F = valueLaw P := rfl

theorem native_original_user_draw : userLaw (nativeGame P t ht R Rp U hR πL πP πA upperBid hupperBid m c ν policy hpolicy η hη0 hη1) =
    (originalJoint P t ht R Rp U hR πL πP πA upperBid hupperBid :
      Measure (ℝ × JointAction 2)).prod (permLaw 2) := by
  rw [userLaw, native_joint]

theorem native_original_profile : userProfileLaw (nativeGame P t ht R Rp U hR πL πP πA upperBid hupperBid m c ν policy hpolicy η hη0 hη1) =
    Measure.pi (fun _ : Fin m =>
      (originalJoint P t ht R Rp U hR πL πP πA upperBid hupperBid :
        Measure (ℝ × JointAction 2)).prod (permLaw 2)) := by
  simp only [userProfileLaw, native_original_user_draw]

end Native
end Source
end FCAppendix.Affine.Tail04.OriginalPopulation
