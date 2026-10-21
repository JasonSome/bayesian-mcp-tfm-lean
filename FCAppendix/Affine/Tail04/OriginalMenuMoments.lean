import FCAppendix.Affine.Tail04.IidActualBalancedCount
import FCAppendix.Affine.Tail04.NativeCountGuards
import FCAppendix.Affine.Tail04.ActiveJointMerge
import FCAppendix.Affine.Tail04.TypicalCountContinuity
import FCAppendix.Affine.Hybrid.FavoredNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical
open OriginalValues OriginalPopulation Existence.Distributional
open Affine.Hybrid Affine.LowBody

local instance {X : Type*} [MeasurableSpace X] (r : ℝ) (μ : Measure X) [IsFiniteMeasure μ] :
    IsFiniteMeasure (ENNReal.ofReal r • μ) := μ.smul_finite ENNReal.ofReal_ne_top

def categoryFlag (E : Observable.Regions) (k : Fin 4) (x : UserDraw 2) : Bool :=
  if E.coarseTag x=k then true else false

theorem measurable_categoryFlag (E : Observable.Regions) (k : Fin 4) :
    Measurable (categoryFlag E k) :=
  Measurable.ite (measurableSet_eq_fun E.measurable_coarseTag measurable_const)
    measurable_const measurable_const

theorem categoryFlag_indicator (E : Observable.Regions) (k : Fin 4) (x : UserDraw 2) :
    indicator (categoryFlag E k) x=(if E.coarseTag x=k then (1:ℝ) else 0) := by
  by_cases h : E.coarseTag x=k <;> simp [indicator,categoryFlag,h]

section CategoryMeans
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions)
    (s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (hrow : (userLaw Γ).map (E.nativeRow Γ)=rivalLaw s a h G)

include hs ha hh hsum G hrow in
theorem original_category_mean (k : Fin 4) :
    (∫ x,indicator (categoryFlag E k) x ∂userLaw Γ)=![s,a,h/2,h/2] k := by
  simp only [categoryFlag_indicator]
  change (∫ x, (fun q : Fin 4 => if q=k then (1:ℝ) else 0) (E.coarseTag x) ∂userLaw Γ) = _
  rw [←FiniteLaw.expect_ofMeasure (userLaw Γ) E.coarseTag E.measurable_coarseTag
      (fun q : Fin 4 => if q=k then (1:ℝ) else 0),
    NativeCountGuards.one_native_category_law Γ E s a h hs ha hh hsum G hrow,
    FiniteLaw.expect_singleton,categoryLaw_mass]

include s a h hs ha hh hsum G hrow in
theorem original_private_means_fair :
    (∫ x,indicator (categoryFlag E 2) x ∂userLaw Γ)=
      (∫ x,indicator (categoryFlag E 3) x ∂userLaw Γ) := by
  rw [original_category_mean Γ E s a h hs ha hh hsum G hrow,
    original_category_mean Γ E s a h hs ha hh hsum G hrow]
  rfl

end CategoryMeans

def sourceProbability (e0 B b : ℝ) : unitInterval :=
  ⟨probabilityClip (mixedFlagProbability e0 B b),probabilityClip_bounds _⟩

theorem sourceProbability_val (e0 B b : ℝ) :
    (sourceProbability e0 B b:ℝ)=sourceFlagProb e0 B (fun _ : Unit => b) () := rfl

theorem measurable_sourceProbability (e0 B : ℝ) : Measurable (sourceProbability e0 B) := by
  exact (continuous_probabilityClip.comp (continuous_mixedFlagProbability e0 B)).measurable.subtype_mk

def sourceReciprocalWeight (e0 B b : ℝ) : ℝ :=
  (sourceProbability e0 B b:ℝ)/max 1 b

theorem sourceReciprocalWeight_bounds (e0 B b : ℝ) :
    sourceReciprocalWeight e0 B b∈Icc (0:ℝ) 1 := by
  have hd : 0< max (1:ℝ) b := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact ⟨div_nonneg (sourceProbability e0 B b).property.1 hd.le,
    (div_le_one hd).mpr ((sourceProbability e0 B b).property.2.trans (le_max_left _ _))⟩

theorem measurable_sourceReciprocalWeight (e0 B : ℝ) :
    Measurable (sourceReciprocalWeight e0 B) :=
  (measurable_sourceProbability e0 B).subtype_val.div (measurable_const.max measurable_id)

def bulkReciprocalConstant (e0 B bStar : ℝ) : ℝ :=
  e0*((B-bStar)/(B-1))^2/bStar

theorem bulkReciprocalConstant_pos {e0 B bStar : ℝ}
    (he : 0< e0) (hStar : 1≤ bStar) (hgap : bStar< B) :
    0< bulkReciprocalConstant e0 B bStar := by
  have hB : 0< B-1 := by linarith
  have hStar0 : 0< bStar := lt_of_lt_of_le (by norm_num) hStar
  unfold bulkReciprocalConstant
  exact div_pos (mul_pos he (sq_pos_of_pos (div_pos (sub_pos.mpr hgap) hB))) hStar0

theorem sourceReciprocalWeight_lower {e0 B bStar b : ℝ}
    (he : 0≤ e0) (he1 : e0≤1) (hStar : 1≤ bStar) (hgap : bStar< B)
    (hb : b∈Icc 1 bStar) :
    bulkReciprocalConstant e0 B bStar≤ sourceReciprocalWeight e0 B b := by
  have hb0 : 0< b := lt_of_lt_of_le (by norm_num) hb.1
  have hStar0 : 0< bStar := hb0.trans_le hb.2
  have hB : 1< B := hStar.trans_lt hgap
  have hD : 0< B-1 := sub_pos.mpr hB
  have hratio : (B-bStar)/(B-1)≤(B-b)/(B-1) :=
    div_le_div_of_nonneg_right (by linarith [hb.2]) hD.le
  have hratio0 : 0≤(B-bStar)/(B-1) := div_nonneg (sub_pos.mpr hgap).le hD.le
  have hsq := mul_le_mul hratio hratio hratio0 (hratio0.trans hratio)
  have hnum : e0*((B-bStar)/(B-1))^2≤ mixedFlagProbability e0 B b := by
    simpa only [pow_two,mixedFlagProbability] using mul_le_mul_of_nonneg_left hsq he
  have hprob : (sourceProbability e0 B b:ℝ)=mixedFlagProbability e0 B b :=
    probabilityClip_eq ⟨mixedFlagProbability_nonneg he,
      mixedFlagProbability_le_one he he1 hB ⟨hb.1,hb.2.trans hgap.le⟩⟩
  rw [sourceReciprocalWeight,hprob,max_eq_right hb.1]
  exact (div_le_div_of_nonneg_left (by positivity) hb0 hb.2).trans
    (div_le_div_of_nonneg_right hnum hb0.le)

theorem sourceReciprocalWeight_eq {e0 B b : ℝ}
    (he : 0≤ e0) (he1 : e0≤1) (hB : 1< B) (hb : b∈Icc 1 B) :
    sourceReciprocalWeight e0 B b=bulkReciprocalConstant e0 B b := by
  have hp : (sourceProbability e0 B b:ℝ)=mixedFlagProbability e0 B b :=
    probabilityClip_eq ⟨mixedFlagProbability_nonneg he,
      mixedFlagProbability_le_one he he1 hB hb⟩
  rw [sourceReciprocalWeight,hp,max_eq_right hb.1]
  rfl

theorem bulkReciprocalConstant_antitone {e0 B x y : ℝ}
    (he : 0≤ e0) (he1 : e0≤1) (hx : 1≤ x) (hxy : x≤ y) (hyB : y< B) :
    bulkReciprocalConstant e0 B y≤ bulkReciprocalConstant e0 B x := by
  rw [←sourceReciprocalWeight_eq he he1 ((hx.trans hxy).trans_lt hyB) ⟨hx,hxy.trans hyB.le⟩]
  exact sourceReciprocalWeight_lower he he1 (hx.trans hxy) hyB ⟨hx,hxy⟩

def originalReciprocalWeight (E : Observable.Regions) (e0 B : ℝ) (x : UserDraw 2) : ℝ :=
  if E.coarseTag x=1 then sourceReciprocalWeight e0 B x.1.2.bid else 0

theorem originalReciprocalWeight_bounds (E : Observable.Regions) (e0 B : ℝ)
    (x : UserDraw 2) : originalReciprocalWeight E e0 B x∈Icc (0:ℝ) 1 := by
  unfold originalReciprocalWeight
  split_ifs
  · exact sourceReciprocalWeight_bounds e0 B _
  · norm_num

theorem measurable_originalReciprocalWeight (E : Observable.Regions) (e0 B : ℝ) :
    Measurable (originalReciprocalWeight E e0 B) :=
  Measurable.ite (measurableSet_eq_fun E.measurable_coarseTag measurable_const)
    ((measurable_sourceReciprocalWeight e0 B).comp
      ((measurable_bid 2).comp measurable_fst.snd)) measurable_const

theorem integrable_originalReciprocalWeight (E : Observable.Regions) (e0 B : ℝ)
    (μ : Measure (UserDraw 2)) [IsFiniteMeasure μ] :
    Integrable (originalReciprocalWeight E e0 B) μ := by
  apply Integrable.of_bound (measurable_originalReciprocalWeight E e0 B).aestronglyMeasurable 1
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (originalReciprocalWeight_bounds E e0 B x).1]
    exact (originalReciprocalWeight_bounds E e0 B x).2)

theorem originalReciprocalWeight_eq_marked (E : Observable.Regions) (e0 B : ℝ) (x : UserDraw 2) :
    originalReciprocalWeight E e0 B x=
      (sourceProbability e0 B x.1.2.bid:ℝ)*
        reciprocalWeight (categoryFlag E 1) (fun y : UserDraw 2 => y.1.2.bid) x := by
  by_cases h : E.coarseTag x=1 <;>
    simp [originalReciprocalWeight,reciprocalWeight,categoryFlag,h,sourceReciprocalWeight,div_eq_mul_inv]

theorem coarseTag_of_active_box (E : Observable.Regions) (x : UserDraw 2)
    (hb : x.1.2.bid∈Icc 1 E.U) : E.coarseTag x=1 := by
  have hd : ¬x.1.2.bid≤ E.d := not_le.mpr (E.d_lt_one.trans_le hb.1)
  have hp : x.1.2.bid∉E.privateBids := by
    rintro (hp|hp)
    · exact (not_le.mpr (E.Rp_lt_one.trans_le hb.1)) hp.2
    · exact (not_le.mpr E.U_lt_H) (hp.trans hb.2)
  simp [Observable.Regions.coarseTag,Observable.Regions.collapse,hd,hp]

section BulkJoint
variable (P : ValueParameters) (E : Observable.Regions) (u e0 B : ℝ)
  (h1u : 1≤1+u) (huE : 1+u≤ E.U) (huB : 1+u< B)
  (he0 : 0≤ e0) (he1 : e0≤1)
  (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)

include h1u huE huB he0 he1 in
theorem original_bulk_reciprocal_lower :
    bulkReciprocalConstant e0 B (1+u)≤
      ∫ x,originalReciprocalWeight E e0 B x ∂
        ((bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw πB :
          Measure (ℝ×JointAction 2)).prod (permLaw 2)) := by
  have hBids := (measurePreserving_fst
    (μ := (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw πB :
      Measure (ℝ×JointAction 2))) (ν := permLaw 2)).quasiMeasurePreserving.ae
      (bandJoint_support (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw πB)
  have hp : ∀ᵐ x ∂((bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw πB :
      Measure (ℝ×JointAction 2)).prod (permLaw 2)),
      bulkReciprocalConstant e0 B (1+u)≤ originalReciprocalWeight E e0 B x := by
    filter_upwards [hBids] with x hx
    rw [originalReciprocalWeight,if_pos (coarseTag_of_active_box E x ⟨hx.2.1.1,hx.2.1.2.trans huE⟩)]
    exact sourceReciprocalWeight_lower he0 he1 h1u huB hx.2.1
  simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono_ae (integrable_const (bulkReciprocalConstant e0 B (1+u)))
      (integrable_originalReciprocalWeight E e0 B _) hp

end BulkJoint

section NativeMixture
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions)
  (t : ℝ) (ht : P.M< t) (u e0 B : ℝ)
  (h1u : 1≤1+u) (huE : 1+u≤ E.U) (huB : 1+u< B) (he0 : 0< e0) (he1 : e0≤1)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)
  (πT : Law (A:=Icc (1:ℝ) E.U) (P.originalTruncatedTailLaw t ht))
  (upperBid : ℝ→ℝ) (hupper : Measurable upperBid)

local notation "hR" => E.d_nonneg.trans E.d_lt_R.le
local notation "J" => originalJoint P t ht.le E.R E.Rp E.U hR πL πP
  (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper
local notation "PB" => bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw πB
local notation "PT" => bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl (P.originalTruncatedTailLaw t ht) πT
local notation "PL" => lowJoint P.originalLowLaw πL
local notation "PP" => bandJoint hR 1 (by norm_num) P.originalPartialLaw πP
local notation "PH" => upperJoint (Subtype.mk (P.originalMovingUpperLaw t)
  (P.originalMovingUpperLaw_probability t) : ProbabilityMeasure ℝ) upperBid hupper

theorem original_joint_bulk_split :
    (J : Measure (ℝ×JointAction 2))=
      ENNReal.ofReal P.bulkWeight • (PB : Measure (ℝ×JointAction 2))+
      (ENNReal.ofReal (lowMass P.theta) • (PL : Measure (ℝ×JointAction 2))+
        ENNReal.ofReal partialMass • (PP : Measure (ℝ×JointAction 2))+
        ENNReal.ofReal (P.truncatedTailWeight t) • (PT : Measure (ℝ×JointAction 2))+
        ENNReal.ofReal (activeMass P.theta*P.zeta*powerTail P.M 10 t) •
          (PH : Measure (ℝ×JointAction 2))) := by
  change fourJoint _ _ _ _ PL PP _ PH=_
  unfold fourJoint
  rw [ActiveJointMerge.weighted_bandJoint_merged]
  simp only [mul_assoc,mul_comm]
  simp only [add_assoc,add_left_comm,add_comm]

include h1u huB he0 he1 in
theorem native_original_reciprocal_lower
    (hjoint : Γ.F⊗ₘΓ.σ=(J : Measure (ℝ×JointAction 2))) :
    0< P.bulkWeight*bulkReciprocalConstant e0 B (1+u) ∧
    P.bulkWeight*bulkReciprocalConstant e0 B (1+u)≤
      ∫ x,(sourceProbability e0 B x.1.2.bid:ℝ)*
        reciprocalWeight (categoryFlag E 1) (fun y : UserDraw 2 => y.1.2.bid) x ∂userLaw Γ := by
  refine ⟨mul_pos P.bulkWeight_pos (bulkReciprocalConstant_pos he0 h1u huB),?_⟩
  simp_rw [←originalReciprocalWeight_eq_marked]
  let rest : Measure (ℝ×JointAction 2) :=
    ENNReal.ofReal (lowMass P.theta) • (PL : Measure (ℝ×JointAction 2))+
      ENNReal.ofReal partialMass • (PP : Measure (ℝ×JointAction 2))+
      ENNReal.ofReal (P.truncatedTailWeight t) • (PT : Measure (ℝ×JointAction 2))+
      ENNReal.ofReal (activeMass P.theta*P.zeta*powerTail P.M 10 t) •
        (PH : Measure (ℝ×JointAction 2))
  have hsplit : Γ.F⊗ₘΓ.σ=ENNReal.ofReal P.bulkWeight • (PB : Measure (ℝ×JointAction 2))+rest :=
    hjoint.trans (original_joint_bulk_split P E t ht u huE πL πP πB πT upperBid hupper)
  letI : IsFiniteMeasure rest := by dsimp [rest];infer_instance
  rw [userLaw,hsplit,Measure.add_prod,Measure.prod_smul_left]
  have hi0 : Integrable (fun x : UserDraw 2 => originalReciprocalWeight E e0 B x)
      (ENNReal.ofReal P.bulkWeight • (PB : Measure (ℝ×JointAction 2)).prod (permLaw 2)) :=
    integrable_originalReciprocalWeight E e0 B _
  have hi1 : Integrable (fun x : UserDraw 2 => originalReciprocalWeight E e0 B x)
      (rest.prod (permLaw 2)) := integrable_originalReciprocalWeight E e0 B _
  rw [integral_add_measure hi0 hi1,integral_smul_measure,ENNReal.toReal_ofReal P.bulkWeight_pos.le,smul_eq_mul]
  have hbulk := original_bulk_reciprocal_lower P E u e0 B h1u huE huB he0.le he1 πB
  have hrest : 0≤∫ x,originalReciprocalWeight E e0 B x ∂rest.prod (permLaw 2) :=
    integral_nonneg (fun x => (originalReciprocalWeight_bounds E e0 B x).1)
  exact (mul_le_mul_of_nonneg_left hbulk P.bulkWeight_pos.le).trans (by linarith)

include h1u he0 he1 in
theorem native_original_reciprocal_uniform (bStar : ℝ)
    (hStar : 1+u≤ bStar) (hStarB : bStar< B)
    (hjoint : Γ.F⊗ₘΓ.σ=(J : Measure (ℝ×JointAction 2))) :
    0< P.bulkWeight*bulkReciprocalConstant e0 B bStar ∧
    P.bulkWeight*bulkReciprocalConstant e0 B bStar≤
      ∫ x,(sourceProbability e0 B x.1.2.bid:ℝ)*
        reciprocalWeight (categoryFlag E 1) (fun y : UserDraw 2 => y.1.2.bid) x ∂userLaw Γ := by
  have h := native_original_reciprocal_lower Γ P E t ht u e0 B h1u huE
    (hStar.trans_lt hStarB) he0 he1 πL πP πB πT upperBid hupper hjoint
  exact ⟨mul_pos P.bulkWeight_pos
      (bulkReciprocalConstant_pos he0 (h1u.trans hStar) hStarB),
    (mul_le_mul_of_nonneg_left
      (bulkReciprocalConstant_antitone he0.le he1 h1u hStar hStarB) P.bulkWeight_pos.le).trans h.2⟩

end NativeMixture

def noisyBulkWidth (u eps : ℝ) : ℝ := (1+u)*(1+eps)-1

theorem noisyBulkWidth_nonneg {u eps : ℝ} (hu : 0≤ u) (heps : 0≤ eps) :
    0≤ noisyBulkWidth u eps := by
  unfold noisyBulkWidth
  nlinarith [mul_nonneg hu heps]

def originalNoisyBulkLaw (P : ValueParameters) (u eps : ℝ) (heps : 0≤ eps)
    (π : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw) :
    Law (A:=Icc (1:ℝ) (1+noisyBulkWidth u eps)) P.originalBulkLaw := by
  rw [show 1+noisyBulkWidth u eps=(1+u)*(1+eps) by unfold noisyBulkWidth;ring]
  exact Hybrid.activeNoisyLaw (by norm_num : (0:ℝ)<1) heps P.originalBulkLaw π

theorem noisyBulk_cap_le_budget {u eps budget : ℝ}
    (hu : 0≤ u) (he : eps≤ budget) :
    1+noisyBulkWidth u eps≤(1+u)*(1+budget) := by
  unfold noisyBulkWidth
  have h := mul_le_mul_of_nonneg_left (add_le_add_left he 1) (by linarith : 0≤1+u)
  linarith

theorem source_numerator_accept (P : ValueParameters) (ξ mbar hm : ℝ) :
    (1-ξ/2)*mbar-ξ*(99/200)+(ξ/2)*(activeMass P.theta-hm)+
      ξ*((partialMass+hm)/2)=
    (1-ξ/2)*mbar-(ξ/2)*delta P.theta := by
  unfold activeMass partialMass
  ring

theorem source_numerator_reject (P : ValueParameters) (ξ mbar hm : ℝ) (hhm : 0≤ hm) :
    (1-ξ/2)*mbar-ξ*(99/200)+(ξ/2)*(activeMass P.theta-hm)+
      ξ*(hm/(partialMass+hm))*((partialMass+hm)/2)=
    (1-ξ/2)*mbar-(ξ/2)*(partialMass+delta P.theta) := by
  have hh : partialMass+hm≠0 := by norm_num [partialMass];linarith
  have he : (hm/(partialMass+hm))*((partialMass+hm)/2)=hm/2 := by
    field_simp [hh]
  rw [mul_assoc,he]
  unfold activeMass partialMass
  ring

theorem normalized_source_multiplier (a hm ξ em reciprocal deficit : ℝ)
    (ha : a-hm≠0) :
    ((1-ξ/2)*((a-hm)*em)-(ξ/2)*deficit)/((a-hm)*reciprocal)=
      ((1-ξ/2)*em-(ξ/2)*(deficit/(a-hm)))/reciprocal := by
  by_cases hr : reciprocal=0
  · simp [hr]
  · field_simp [ha,hr]

end FCAppendix.Affine.Tail04.MenuError
