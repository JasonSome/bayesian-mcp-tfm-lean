import FCAppendix.Affine.Tail04.OriginalPrivateSignalLaw
import FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalCommonLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation OriginalPrivateEntry Hybrid
open CompactSourceBidLaws

variable (E : Observable.Regions)

def event : Set (ℝ×JointAction 2) := {x | E.d< x.2.bid ∧ x.2.bid∉E.privateBids}

lemma measurableSet_event : MeasurableSet (event E) :=
  (measurableSet_lt measurable_const ((measurable_bid 2).comp measurable_snd)).inter
    ((((measurable_bid 2).comp measurable_snd) E.measurableSet_privateBids).compl)

lemma coarse_common_event : E.coarseTag ⁻¹' {(1:Fin 4)}=event E×ˢuniv := by
  ext x
  have hu : (Hybrid.upperRow x.2).1≠(1:Fin 4) := by
    unfold Hybrid.upperRow
    split <;> norm_num [Fin.ext_iff]
  by_cases hl : x.1.2.bid≤ E.d
  · simp [Observable.Regions.coarseTag,Observable.Regions.collapse,hl,event,not_lt.mpr hl]
  · by_cases hp : x.1.2.bid∈E.privateBids <;>
      simp [Observable.Regions.coarseTag,Observable.Regions.collapse,hl,hp,event,lt_of_not_ge hl,hu]

def commonDecode (x : ℝ×JointAction 2) : Icc (1:ℝ) E.U :=
  OriginalValues.clipToBand 1 E.U E.one_le_U x.2.bid

lemma measurable_commonDecode : Measurable (commonDecode E) :=
  (OriginalValues.measurable_clipToBand 1 E.U E.one_le_U).comp
    ((measurable_bid 2).comp measurable_snd)

include E in
lemma bandJoint_common {vL vU : ℝ} (μ : Measure (Icc vL vU)) [IsProbabilityMeasure μ]
    (πA : Law (A:=Icc (1:ℝ) E.U) μ) :
    (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl μ πA : Measure _).map (commonDecode E)=
      (bidMarginal πA.1 : Measure (Icc (1:ℝ) E.U)) := by
  have hf : Measurable (fun x : Icc vL vU×Icc (1:ℝ) E.U =>
      ((x.1:ℝ),bandAction (by norm_num : (0:ℝ)≤1) 2 le_rfl x.2)) :=
    measurable_fst.subtype_val.prodMk
      ((measurable_bandAction (by norm_num : (0:ℝ)≤1) 2 le_rfl).comp measurable_snd)
  change ((πA.1 : Measure (Icc vL vU × Icc (1:ℝ) E.U)).map _).map (commonDecode E)=(πA.1 : Measure (Icc vL vU × Icc (1:ℝ) E.U)).map Prod.snd
  erw [Measure.map_map (measurable_commonDecode E) hf]
  congr 1
  funext x
  apply Subtype.ext
  exact OriginalValues.clipToBand_eq 1 E.U E.one_le_U x.2.2

variable (P : ValueParameters) (hd : E.d=P.d0) (t : ℝ) (ht : P.M≤ t)
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
local notation "PA" => bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl
  (P.originalMovingActiveLaw t ht) πA

include hd hfloor in
theorem original_common_restriction :
    (J : Measure _).restrict (event E)=ENNReal.ofReal (activeMass P.theta-z) • (PA : Measure _) := by
  have hL : ∀ᵐ x ∂(lowJoint P.originalLowLaw πL : Measure (ℝ×JointAction 2)),x∉event E := by
    apply (ae_map_iff (measurable_fst.subtype_val.prodMk
      ((measurable_lowBroadcast P.d0).comp measurable_snd)).aemeasurable
      (measurableSet_event E).compl).mpr
    exact ae_of_all _ fun x => by
      intro hx
      have hb : (x.2:ℝ)≤ E.d := by rw [hd];exact x.2.2.2
      exact not_lt_of_ge hb hx.1
  have hP : ∀ᵐ x ∂(bandJoint hR 1 (by norm_num) P.originalPartialLaw πP : Measure _),x∉event E :=
    (bandJoint_support hR 1 (by norm_num) P.originalPartialLaw πP).mono
      (fun _ hx hp => hp.2 (Or.inl hx.2.1))
  have hA : ∀ᵐ x ∂(PA : Measure _),x∈event E :=
    (bandJoint_support (by norm_num : (0:ℝ)≤1) 2 le_rfl
      (P.originalMovingActiveLaw t ht) πA).mono (fun x hx =>
        ⟨E.d_lt_one.trans_le hx.2.1.1,by
          rintro (hp | hp)
          · linarith [hp.2,hx.2.1.1,E.Rp_lt_one]
          · have hp' : E.H≤x.2.bid := hp
            linarith [hp',hx.2.1.2,E.U_lt_H]⟩)
  let FH : ProbabilityMeasure ℝ := ⟨P.originalMovingUpperLaw t,P.originalMovingUpperLaw_probability t⟩
  have hH : ∀ᵐ x ∂(upperJoint FH upperBid hupperBid : Measure _),x∉event E :=
    (upperJoint_support FH upperBid hupperBid E.H
      ((P.originalMovingUpperLaw_support t).mono (fun v hv => hfloor v hv))).mono
        (fun _ hx he => he.2 (Or.inr hx.1))
  have hzL : (lowJoint P.originalLowLaw πL : Measure _).restrict (event E)=0 := by
    apply Measure.restrict_eq_zero.mpr
    exact measure_eq_zero_iff_ae_notMem.mpr hL
  have hzP : (bandJoint hR 1 (by norm_num) P.originalPartialLaw πP : Measure _).restrict (event E)=0 := by
    apply Measure.restrict_eq_zero.mpr
    exact measure_eq_zero_iff_ae_notMem.mpr hP
  have hzH : (upperJoint FH upperBid hupperBid : Measure _).restrict (event E)=0 := by
    apply Measure.restrict_eq_zero.mpr
    exact measure_eq_zero_iff_ae_notMem.mpr hH
  dsimp only [FH] at hzH
  change (fourJoint _ _ _ _ _ _ _ _).restrict _=_
  simp only [fourJoint,Measure.restrict_add,Measure.restrict_smul,hzL,hzP,hzH,
    Measure.restrict_eq_self_of_ae_mem hA,smul_zero,zero_add,add_zero]

include hd hfloor in
theorem original_common_mass : (J : Measure _).real (event E)=activeMass P.theta-z := by
  have h := congrArg (fun μ : Measure (ℝ×JointAction 2) => μ univ)
    (original_common_restriction E P hd t ht πL πP πA upperBid hupperBid hfloor)
  simp only [Measure.restrict_apply_univ,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] at h
  rw [measureReal_def,h,ENNReal.toReal_ofReal (P.movingActiveMass_positive t ht).le]

include hd hfloor in
theorem original_common_conditional : cond (J : Measure _) (event E)=(PA : Measure _) := by
  have hp := P.movingActiveMass_positive t ht
  apply ActiveJointMerge.measure_smul_cancel hp
  have hm : ENNReal.ofReal (activeMass P.theta-z)=(J : Measure _) (event E) := by
    rw [←original_common_mass E P hd t ht πL πP πA upperBid hupperBid hfloor,ofReal_measureReal]
  rw [hm,measure_smul_cond,original_common_restriction E P hd t ht πL πP πA
    upperBid hupperBid hfloor,hm]

include hd hfloor in
theorem native_original_common_bid {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (hjoint : Γ.F ⊗ₘ Γ.σ=(J : Measure _)) :
    (cond (userLaw Γ) (E.coarseTag ⁻¹' {(1:Fin 4)})).map
      (fun x : UserDraw 2 => commonDecode E x.1)=(bidMarginal πA.1 : Measure (Icc (1:ℝ) E.U)) := by
  rw [coarse_common_event]
  change (cond ((Γ.F ⊗ₘ Γ.σ).prod (permLaw 2)) _).map _=_
  rw [hjoint]
  have hp : 0<(J : Measure _).real (event E) := by
    rw [original_common_mass E P hd t ht πL πP πA upperBid hupperBid hfloor]
    exact P.movingActiveMass_positive t ht
  rw [conditioned_product_projection _ _ (event E) univ (measurableSet_event E)
    MeasurableSet.univ hp (by simp) (commonDecode E) (measurable_commonDecode E),
    original_common_conditional E P hd t ht πL πP πA upperBid hupperBid hfloor,
    bandJoint_common E (P.originalMovingActiveLaw t ht) πA]

end FCAppendix.Affine.Tail04.OriginalCommonLaw
