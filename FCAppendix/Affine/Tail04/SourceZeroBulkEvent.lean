import FCAppendix.Affine.Tail04.ZeroSourceCommonMoments
import FCAppendix.Affine.Tail04.NativeWeightedFlagBound

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceZeroBulkEvent
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeZeroNoiseSource Hybrid

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)

def jointEvent : Set (ℝ×JointAction 2) :=
  {x | x.1∈P.bulkValues ∧ x.2.bid∈Icc (1:ℝ) (1+D.u) ∧ x.2.routeCount=2}

lemma measurable_jointEvent : MeasurableSet (jointEvent D P) :=
  (measurable_fst measurableSet_Icc).inter
    ((((measurable_bid 2).comp measurable_snd) measurableSet_Icc).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))

theorem joint_bulk_shape :
    ∀ᵐx ∂(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)),
      x.1∈P.bulkValues → x.2.bid∈Icc (1:ℝ) (1+D.u) ∧ x.2.routeCount=2 := by
  let Q := fun x : ℝ×JointAction 2=> x.1∈P.bulkValues →
    x.2.bid∈Icc (1:ℝ) (1+D.u) ∧ x.2.routeCount=2
  have hL : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (lowJoint P.originalLowLaw πL)),Q x := by
    have hval : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (lowJoint P.originalLowLaw πL)),x.1∈Icc 0 P.d0 := by
      apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp
      rw [lowJoint_value_marginal]
      apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
      exact ae_of_all _ (fun v=> v.2)
    filter_upwards [hval] with x hx hb
    exfalso
    linarith [hx.2,hb.1,P.low_partial_gap,P.partial_active_gap,P.w_pos]
  have hP : ∀ᵐx ∂(bandJoint D.hR.le 1 (by norm_num) P.originalPartialLaw
      («partial» D P t ht π) : Measure _),Q x := by
    filter_upwards [bandJoint_support D.hR.le 1 (by norm_num) P.originalPartialLaw
      («partial» D P t ht π)] with x hx hb
    exfalso
    exact (not_le.mpr P.partial_active_gap) (hb.1.trans hx.1.2)
  have hB : ∀ᵐx ∂(bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl
      P.originalBulkLaw (π 0) : Measure _),Q x := by
    filter_upwards [bandJoint_support (by norm_num : (0:ℝ)≤1) 2 le_rfl
      P.originalBulkLaw (π 0)] with x hx _
    exact hx.2
  have hT : ∀ᵐx ∂(bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl
      (P.originalTruncatedTailLaw t ht) (π 1) : Measure _),Q x := by
    filter_upwards [bandJoint_support (by norm_num : (0:ℝ)≤1) 2 le_rfl
      (P.originalTruncatedTailLaw t ht) (π 1)] with x hx hb
    exfalso
    exact (not_le.mpr P.active_tail_gap) (hx.1.1.trans hb.2)
  let FH : ProbabilityMeasure ℝ:=⟨P.originalMovingUpperLaw t,P.originalMovingUpperLaw_probability t⟩
  have hH : ∀ᵐx ∂(upperJoint FH upperBid hupperBid : Measure _),Q x := by
    have hQ : MeasurableSet {x : ℝ×JointAction 2 | Q x} := by
      simpa only [Q,ValueParameters.bulkValues,imp_iff_not_or,setOf_or,setOf_and] using!
       (measurable_fst measurableSet_Icc).compl.union
        ((((measurable_bid 2).comp measurable_snd) measurableSet_Icc).inter
          (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))
    apply (ae_map_iff (measurable_id.prodMk
      (measurable_upperAction upperBid hupperBid)).aemeasurable hQ).mpr
    filter_upwards [P.originalMovingUpperLaw_support t] with v hv hb
    exfalso
    exact (not_le.mpr (P.active_tail_gap.trans ht)) (hv.le.trans hb.2)
  letI : IsProbabilityMeasure (P.originalMovingActiveLaw t ht.le) :=
    P.originalMovingActiveLaw_probability t ht.le
  change ∀ᵐx ∂(
    ENNReal.ofReal (lowMass P.theta) • (ProbabilityMeasure.toMeasure (lowJoint P.originalLowLaw πL))+
    ENNReal.ofReal partialMass • (bandJoint D.hR.le 1 (by norm_num)
      P.originalPartialLaw («partial» D P t ht π) : Measure _)+
    ENNReal.ofReal (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t) •
      (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl (P.originalMovingActiveLaw t ht.le)
        (active D P t ht π) : Measure _)+
    ENNReal.ofReal (activeMass P.theta*P.zeta*powerTail P.M 10 t) •
      (upperJoint FH upperBid hupperBid : Measure _)),Q x
  rw [joint_active_components D P t ht π]
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hL _,Measure.ae_smul_measure hP _⟩,
      ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hB _,Measure.ae_smul_measure hT _⟩⟩,
      Measure.ae_smul_measure hH _⟩

theorem joint_event_mass :
    (joint D P t ht πL π upperBid hupperBid : Measure _).real (jointEvent D P)=P.bulkWeight := by
  have he : jointEvent D P=ᵐ[(joint D P t ht πL π upperBid hupperBid : Measure _)]
      Prod.fst ⁻¹' P.bulkValues := by
    filter_upwards [joint_bulk_shape D P t ht πL π upperBid hupperBid] with x hx
    exact propext ⟨fun h=> h.1,fun h=>⟨h,hx h⟩⟩
  rw [measureReal_def,measure_congr he]
  rw [←Measure.map_apply measurable_fst measurableSet_Icc,joint_value]
  exact P.bulk_mass

def event : Set (UserDraw 2) := jointEvent D P ×ˢuniv

lemma measurable_event : MeasurableSet (event D P) :=
  (measurable_jointEvent D P).prod MeasurableSet.univ

variable (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (hfloor : ∀v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    (activeMass P.theta*P.zeta*powerTail P.M 10 t/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

local notation "E" => regions D P hdR H hUH
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH

theorem original_mass : (userLaw Γ).real (event D P)=P.bulkWeight := by
  rw [game_original_user]
  change (((joint D P t ht πL π upperBid hupperBid : Measure _).prod (permLaw 2))
    (jointEvent D P ×ˢuniv)).toReal=P.bulkWeight
  rw [Measure.prod_prod,measure_univ,mul_one]
  exact joint_event_mass D P t ht πL π upperBid hupperBid

theorem member_shape (x : UserDraw 2) (hx : x∈event D P) :
    (E).coarseTag x=1 ∧ (decode x:ℝ)=x.1.2.bid ∧ (decode x:ℝ)≤1+D.u := by
  have hbox : x.1.2.bid∈Icc (1:ℝ) (E).U :=
    ⟨hx.1.2.1.1,hx.1.2.1.2.trans D.huU⟩
  have hlow : ¬x.1.2.bid≤ (E).d := not_le.mpr ((E).d_lt_one.trans_le hbox.1)
  have hpriv : x.1.2.bid∉(E).privateBids := by
    rintro (hp|hu)
    · linarith [hp.2,hbox.1,(E).Rp_lt_one]
    · exact (not_le.mpr (E).U_lt_H) (hu.trans hbox.2)
  have he : (decode x:ℝ)=x.1.2.bid :=
    clipToBand_eq 1 (E).U (E).one_le_U hbox
  refine ⟨?_,he,?_⟩
  · simp only [Observable.Regions.coarseTag,Observable.Regions.collapse,
      if_neg hlow,if_neg hpriv]
  · rw [he]
    exact hx.1.2.1.2

theorem original_iid_bulk_lower_tail (hN : 0< N) :
    (Measure.pi (fun _ : Fin N=> userLaw Γ)).real
      {r | (Probability.sampleCount (event D P) r:ℝ)< P.bulkWeight*N/2}≤
        Real.exp (-(N:ℝ)*P.bulkWeight^2/2) := by
  exact NativeFlag.iid_bulk_count_lower_tail (userLaw Γ) (event D P)
    (measurable_event D P) N hN P.bulkWeight_pos
    (original_mass D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare).ge

end FCAppendix.Affine.Tail04.SourceZeroBulkEvent
