import FCAppendix.Affine.Tail04.OriginalLowRow
import FCAppendix.Affine.Tail04.PrivateRowSorting
import FCAppendix.Affine.Tail04.ObservedScenario
import FCAppendix.Affine.Hybrid.CollapsedProfile

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalPrivateEntry
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open OriginalPopulation OriginalValues Hybrid LocalCoordinates EqualPrivateSignal EqualPrivateUpper

lemma measure_ne_zero_of_real_pos {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (h : 0< μ.real E) : μ E≠0 := by
  intro he
  simp only [measureReal_def,he,ENNReal.toReal_zero] at h
  exact lt_irrefl _ h

theorem cond_real_eq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : Set X) (hP : MeasurableSet P)
    (hp : 0< μ.real P) (B : Set X) :
    (cond μ P).real B=μ.real (P∩B)/μ.real P := by
  have hh := congrArg ENNReal.toReal (ProbabilityTheory.cond_mul_eq_inter hP B μ)
  simp only [ENNReal.toReal_mul] at hh
  exact (eq_div_iff hp.ne').mpr hh

theorem conditioned_product_projection {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (P : Set X) (T : Set Y) (hP : MeasurableSet P) (hT : MeasurableSet T)
    (hp : 0< μ.real P) (ht : 0< ν.real T) (f : X → Z) (hf : Measurable f) :
    (cond (μ.prod ν) (P×ˢT)).map (fun z => f z.1)=(cond μ P).map f := by
  have hprod : 0<(μ.prod ν).real (P×ˢT) := by
    simpa only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul] using mul_pos hp ht
  letI : IsProbabilityMeasure (cond μ P) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos μ P hp)
  letI : IsProbabilityMeasure (cond (μ.prod ν) (P×ˢT)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ _ hprod)
  apply Measure.ext
  intro B hB
  change ((cond (μ.prod ν) (P×ˢT)).map (f ∘ Prod.fst)) B=((cond μ P).map f) B
  rw [Measure.map_apply (hf.comp measurable_fst) hB,Measure.map_apply hf hB]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (cond (μ.prod ν) (P×ˢT)).real ((fun z : X×Y => f z.1) ⁻¹' B)=
    (cond μ P).real (f ⁻¹' B)
  rw [cond_real_eq _ _ (hP.prod hT) hprod,cond_real_eq μ P hP hp]
  have he : (P×ˢT)∩((fun z : X×Y => f z.1) ⁻¹' B)=(P∩f ⁻¹' B)×ˢT := by
    ext z;simp only [mem_inter_iff,mem_prod,mem_preimage];tauto
  rw [he]
  simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul]
  change (μ.real (P∩f ⁻¹' B)*ν.real T)/(μ.real P*ν.real T)=
    μ.real (P∩f ⁻¹' B)/μ.real P
  field_simp [hp.ne',ht.ne']

variable (E : Observable.Regions)

def jointDecode (x : ℝ × JointAction 2) : Ici E.H ⊕ Icc E.R E.Rp := LocalCoordinates.decode E x.2.bid

lemma measurable_jointDecode : Measurable (jointDecode E) :=
  (LocalCoordinates.measurable_decode E).comp ((measurable_bid 2).comp measurable_snd)

lemma decode_upper_iff (b : ℝ) :
    isUpper (signalEntry (LocalCoordinates.decode E b))=true ↔ E.H≤ b := by
  by_cases hb : E.H≤ b <;> simp [LocalCoordinates.decode,hb,signalEntry,isUpper]

def entryLaw (Q : ProbabilityMeasure (ℝ × JointAction 2))
    (hp : 0<(Q : Measure (ℝ × JointAction 2)).real E.privateJointEvent) :
    ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp) := by
  letI : IsProbabilityMeasure (cond (Q : Measure (ℝ × JointAction 2)) E.privateJointEvent) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ _ hp)
  exact ⟨(cond (Q : Measure (ℝ × JointAction 2)) E.privateJointEvent).map (jointDecode E),
    Measure.isProbabilityMeasure_map (measurable_jointDecode E).aemeasurable⟩

theorem entryLaw_given_recipient (Q : ProbabilityMeasure (ℝ × JointAction 2))
    (hp : 0<(Q : Measure (ℝ × JointAction 2)).real E.privateJointEvent) (j : Fin 2) :
    (cond ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2))
      (E.privateJointEvent ×ˢ oneRouteEvent j)).map
      (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid)=
        (entryLaw E Q hp : Measure (Ici E.H ⊕ Icc E.R E.Rp)) :=
  conditioned_product_projection _ _ _ _ E.measurableSet_privateJointEvent
    (measurableSet_oneRouteEvent j) hp (by rw [original_fair_route_mass];norm_num)
    (jointDecode E) (measurable_jointDecode E)

theorem private_tag_event (j : Fin 2) :
    E.coarseTag ⁻¹' {Hybrid.NativeContinuation.upperTag j}=E.privateJointEvent ×ˢ oneRouteEvent j := by
  ext x
  have h0 : Hybrid.NativeContinuation.upperTag j≠0 := Hybrid.NativeContinuation.upperTag_ne_zero j
  have h1 : Hybrid.NativeContinuation.upperTag j≠1 := Hybrid.NativeContinuation.upperTag_ne_one j
  by_cases hp : x.1.2.bid∈E.privateBids
  · have hd := not_le.mpr (E.private_above_low hp)
    simp only [mem_preimage,mem_singleton_iff,Observable.Regions.coarseTag,
      Observable.Regions.collapse,if_neg hd,if_pos hp]
    simpa only [mem_prod,Observable.Regions.privateJointEvent,mem_setOf_eq,oneRouteEvent,hp,
      true_and] using Hybrid.NativeContinuation.upperRow_tag x.2 j
  · by_cases hd : x.1.2.bid≤ E.d <;>
      simp [Observable.Regions.coarseTag,Observable.Regions.collapse,hd,hp,
        Observable.Regions.privateJointEvent,Ne.symm h0,Ne.symm h1]

theorem native_entryLaw_given_tag {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (Q : ProbabilityMeasure (ℝ × JointAction 2))
    (hjoint : Γ.F ⊗ₘ Γ.σ=(Q : Measure (ℝ × JointAction 2)))
    (hp : 0<(Q : Measure (ℝ × JointAction 2)).real E.privateJointEvent) (j : Fin 2) :
    (cond (userLaw Γ) (E.coarseTag ⁻¹' {Hybrid.NativeContinuation.upperTag j})).map
      (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid)=
        (entryLaw E Q hp : Measure (Ici E.H ⊕ Icc E.R E.Rp)) := by
  rw [private_tag_event E j]
  change (cond ((Γ.F ⊗ₘ Γ.σ).prod (permLaw 2)) _).map _=_
  rw [hjoint]
  exact entryLaw_given_recipient E Q hp j

theorem upperProbability_entryLaw (Q : ProbabilityMeasure (ℝ × JointAction 2))
    (hp : 0<(Q : Measure (ℝ × JointAction 2)).real E.privateJointEvent) :
    PrivateRowSorting.upperProbability E (entryLaw E Q hp)=
      (Q : Measure (ℝ × JointAction 2)).real E.upperJointEvent /
        (Q : Measure (ℝ × JointAction 2)).real E.privateJointEvent := by
  let μ := cond (Q : Measure (ℝ × JointAction 2)) E.privateJointEvent
  letI : IsProbabilityMeasure μ :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ _ hp)
  have hi : Measurable (fun x : Ici E.H ⊕ Icc E.R E.Rp =>
      if isUpper (signalEntry x)=true then (1:ℝ) else 0) :=
    (measurable_of_countable (fun z : Bool => if z=true then (1:ℝ) else 0)).comp
      (continuous_isUpper.measurable.comp continuous_signalEntry.measurable)
  unfold PrivateRowSorting.upperProbability
  change (∫ x : Ici E.H ⊕ Icc E.R E.Rp,
    if isUpper (signalEntry x)=true then (1:ℝ) else 0 ∂μ.map (jointDecode E))=_
  rw [integral_map (measurable_jointDecode E).aemeasurable hi.aestronglyMeasurable]
  have he : (fun x : ℝ × JointAction 2 =>
      if isUpper (signalEntry (jointDecode E x))=true then (1:ℝ) else 0)=
      E.upperJointEvent.indicator (fun _ => (1:ℝ)) := by
    funext x
    simp only [jointDecode,decode_upper_iff,Set.indicator,Observable.Regions.upperJointEvent,
      mem_setOf_eq]
  rw [he]
  calc
    _=μ.real E.upperJointEvent := by
      convert! (integral_indicator_one (μ:=μ) E.measurableSet_upperJointEvent) using 1
    _=_ := by
      change (cond (Q : Measure (ℝ × JointAction 2)) E.privateJointEvent).real E.upperJointEvent=_
      rw [cond_real_eq _ _ E.measurableSet_privateJointEvent hp,
        inter_eq_right.mpr E.upperJointEvent_subset]

theorem private_restriction (s h a z : ℝ)
    (PL PP PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),x.2.bid≤ E.d)
    (hP : ∀ᵐ x ∂(PP : Measure (ℝ × JointAction 2)),x∈E.privateJointEvent)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),x∉E.privateJointEvent)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)),x∈E.privateJointEvent) :
    (fourJoint s h a z PL PP PA PH).restrict E.privateJointEvent=
      ENNReal.ofReal h•(PP : Measure (ℝ × JointAction 2))+
        ENNReal.ofReal z•(PH : Measure (ℝ × JointAction 2)) := by
  have hl0 : (PL : Measure (ℝ × JointAction 2)).restrict E.privateJointEvent=0 := by
    apply Measure.restrict_eq_zero.mpr
    exact measure_eq_zero_iff_ae_notMem.mpr
      (hL.mono (fun x hx hp => (not_lt.mpr hx) (E.private_above_low hp)))
  have ha0 : (PA : Measure (ℝ × JointAction 2)).restrict E.privateJointEvent=0 := by
    apply Measure.restrict_eq_zero.mpr
    exact measure_eq_zero_iff_ae_notMem.mpr hA
  rw [fourJoint,Measure.restrict_add,Measure.restrict_add,Measure.restrict_add]
  simp only [Measure.restrict_smul,hl0,ha0,
    Measure.restrict_eq_self_of_ae_mem hP,Measure.restrict_eq_self_of_ae_mem hH,
    smul_zero,zero_add,add_zero]

end FCAppendix.Affine.Tail04.OriginalPrivateEntry
