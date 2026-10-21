import FCAppendix.Affine.Tail04.NativeNoisySource
import FCAppendix.Affine.Tail04.OriginalFiniteFibers

noncomputable section
namespace FCAppendix.Affine.Tail04.LatentNoisyPopulation
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid Existence.Distributional OriginalValues OriginalPopulation
open NativeNoisySource SourceTailNoisyFixedPoint OriginalFiniteFibers
open scoped BigOperators

section Implementation

def noisyAction (eps : ℝ) (heps : 0≤ eps) (a : JointAction 2) (u : unitInterval) : JointAction 2 :=
  ⟨a.bid*(1+eps*(u:ℝ)),mul_nonneg a.bid_nonneg (by linarith [mul_nonneg heps u.2.1]),
    a.routeCount,a.routeCount_le⟩

lemma measurable_noisyAction (eps : ℝ) (heps : 0≤ eps) :
    Measurable (fun p : JointAction 2×unitInterval => noisyAction eps heps p.1 p.2) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  exact (((measurable_bid 2).comp measurable_fst).mul
    (measurable_const.add (measurable_const.mul measurable_snd.subtype_val))).prodMk
      ((measurable_routeCount 2).comp measurable_fst) |>.comap_le

def noisyJoint (eps : ℝ) (heps : 0≤ eps) (z : (ℝ×JointAction 2)×unitInterval) : ℝ×JointAction 2 :=
  (z.1.1,noisyAction eps heps z.1.2 z.2)

lemma measurable_noisyJoint (eps : ℝ) (heps : 0≤ eps) : Measurable (noisyJoint eps heps) :=
  measurable_fst.fst.prodMk ((measurable_noisyAction eps heps).comp
    (measurable_fst.snd.prodMk measurable_snd))

theorem bandJoint_noisy {vlo vhi L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps)
    (k : ℕ) (hk : k≤2) (μ : Measure (Icc vlo vhi)) [IsProbabilityMeasure μ]
    (π : Law (A:=Icc L U) μ) :
    ((bandJoint hL.le k hk μ π : Measure _).prod (volume : Measure unitInterval)).map
      (noisyJoint eps heps)=
      (bandJoint hL.le k hk μ (activeNoisyLaw hL heps μ π) : Measure _) := by
  let f : Icc vlo vhi×Icc L U → ℝ×JointAction 2 := fun x => ((x.1:ℝ),bandAction hL.le k hk x.2)
  have hf : Measurable f := measurable_fst.subtype_val.prodMk
    ((measurable_bandAction hL.le k hk).comp measurable_snd)
  let g : (Icc vlo vhi×Icc L U)×unitInterval → Icc vlo vhi×Icc L (U*(1+eps)) :=
    fun x => (x.1.1,activeNoisyBid hL heps x)
  have hg : Measurable g := measurable_fst.fst.prodMk (continuous_activeNoisyBid hL heps).measurable
  let f' : Icc vlo vhi×Icc L (U*(1+eps)) → ℝ×JointAction 2 :=
    fun x => ((x.1:ℝ),bandAction hL.le k hk x.2)
  have hf' : Measurable f' := measurable_fst.subtype_val.prodMk
    ((measurable_bandAction hL.le k hk).comp measurable_snd)
  change (((π.1 : Measure _).map f).prod volume).map (noisyJoint eps heps)=
    (((π.1 : Measure _).prod volume).map g).map f'
  rw [show (((π.1 : Measure _).map f).prod volume)=
      ((π.1 : Measure _).prod volume).map (Prod.map f id) by
        simpa only [Measure.map_id] using Measure.map_prod_map _ _ hf measurable_id]
  rw [Measure.map_map (measurable_noisyJoint eps heps) (hf.prodMap measurable_id),
    Measure.map_map hf' hg]
  congr 1

private lemma bandJoint_cast_upper {vlo vhi L U V : ℝ} (hL : 0 ≤ L)
    (k : ℕ) (hk : k ≤ 2) (μ : Measure (Icc vlo vhi)) [IsProbabilityMeasure μ]
    (h : U = V) (π : Law (A:=Icc L V) μ) :
    bandJoint hL k hk μ (show Law (A:=Icc L U) μ from by rw [h]; exact π) =
      bandJoint hL k hk μ π := by
  cases h
  rfl

end Implementation

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)

def species : FiniteLaw (Fin 5) where
  mass := ![lowMass P.theta,partialMass,P.bulkWeight,P.truncatedTailWeight t,tailMass P t]
  nonneg := by
    intro i
    fin_cases i
    · exact P.low_mass_pos.le
    · norm_num [partialMass]
    · exact P.bulkWeight_pos.le
    · exact (P.truncatedTailWeight_pos t ht).le
    · exact SourceTailNoisyFixedPoint.tailMass_nonneg P t ht.le
  total := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Fin.isValue,add_zero]
    have h := P.component_weight_sum t
    unfold tailMass
    linarith [mass_sum P.theta]

def baseComponent : Fin 5 → ProbabilityMeasure (ℝ×JointAction 2) :=
  ![lowJoint P.originalLowLaw πL,
    bandJoint D.hR.le 1 (by norm_num) P.originalPartialLaw (partialBase D P t ht π),
    bandJoint (by norm_num) 2 le_rfl P.originalBulkLaw (bulkBase D P t ht π),
    bandJoint (by norm_num) 2 le_rfl (P.originalTruncatedTailLaw t ht) (tailBase D P t ht π),
    upperJoint ⟨P.originalMovingUpperLaw t,P.originalMovingUpperLaw_probability t⟩ upperBid hupperBid]

def physicalComponent : Fin 5 → ProbabilityMeasure (ℝ×JointAction 2) :=
  ![lowJoint P.originalLowLaw πL,
    bandJoint D.hR.le 1 (by norm_num) P.originalPartialLaw (partialPhysical D P t ht π),
    bandJoint (by norm_num) 2 le_rfl P.originalBulkLaw (bulkPhysical D P t ht π),
    bandJoint (by norm_num) 2 le_rfl (P.originalTruncatedTailLaw t ht) (tailPhysical D P t ht π),
    upperJoint ⟨P.originalMovingUpperLaw t,P.originalMovingUpperLaw_probability t⟩ upperBid hupperBid]

abbrev Tagged := Fin 5×(ℝ×JointAction 2)
abbrev Draw := (Tagged×unitInterval)×Equiv.Perm (Fin 2)

def taggedComponent (r : Fin 5) : ProbabilityMeasure Tagged :=
  (baseComponent D P t ht πL π upperBid hupperBid r).map
    (show Measurable (fun x : ℝ×JointAction 2 => (r,x)) from
      measurable_const.prodMk measurable_id).aemeasurable

def baseLaw : ProbabilityMeasure Tagged := by
  refine ⟨∑ r,ENNReal.ofReal ((species P t ht).mass r) •
    (taggedComponent D P t ht πL π upperBid hupperBid r : Measure Tagged),?_⟩
  constructor
  simp only [measure_sum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun r _ => (species P t ht).nonneg r),
    (species P t ht).total,ENNReal.ofReal_one]

def drawLaw : Measure Draw :=
  ((baseLaw D P t ht πL π upperBid hupperBid : Measure _).prod
    (volume : Measure unitInterval)).prod (permLaw 2)

instance drawLaw_probability : IsProbabilityMeasure (drawLaw D P t ht πL π upperBid hupperBid) := by
  unfold drawLaw
  infer_instance

def implementJoint (D : FiniteTailNoisyGame.Data) (z : Tagged×unitInterval) : ℝ×JointAction 2 :=
  if z.1.1=0 ∨ z.1.1=4 then z.1.2 else noisyJoint D.eps D.heps.le (z.1.2,z.2)

lemma measurable_implementJoint : Measurable (implementJoint D) := by
  apply Measurable.ite
  · exact (measurableSet_eq_fun measurable_fst.fst measurable_const).union
      (measurableSet_eq_fun measurable_fst.fst measurable_const)
  · exact measurable_fst.snd
  · exact (measurable_noisyJoint D.eps D.heps.le).comp (measurable_fst.snd.prodMk measurable_snd)

def realize (D : FiniteTailNoisyGame.Data) (z : Draw) : UserDraw 2 :=
  (implementJoint D z.1,z.2)

lemma measurable_realize : Measurable (realize D) :=
  (measurable_implementJoint D).prodMap measurable_id

theorem component_implementation (r : Fin 5) :
    ((taggedComponent D P t ht πL π upperBid hupperBid r : Measure Tagged).prod volume).map
      (implementJoint D)=(physicalComponent D P t ht πL π upperBid hupperBid r : Measure _) := by
  let f : ℝ×JointAction 2 → Tagged := fun x => (r,x)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  change (((baseComponent D P t ht πL π upperBid hupperBid r : Measure _).map f).prod volume).map
    (implementJoint D)=_
  rw [show (((baseComponent D P t ht πL π upperBid hupperBid r : Measure _).map f).prod volume)=
      ((baseComponent D P t ht πL π upperBid hupperBid r : Measure _).prod volume).map (Prod.map f id) by
        simpa only [Measure.map_id] using Measure.map_prod_map _ _ hf measurable_id]
  rw [Measure.map_map (measurable_implementJoint D) (hf.prodMap measurable_id)]
  fin_cases r
  · change Measure.map Prod.fst ((lowJoint P.originalLowLaw πL : Measure (ℝ×JointAction 2)).prod
      (volume : Measure unitInterval)) = _
    exact (measurePreserving_fst
      (μ:=(lowJoint P.originalLowLaw πL : Measure (ℝ×JointAction 2)))
      (ν:=(volume : Measure unitInterval))).map_eq
  · change Measure.map (noisyJoint D.eps D.heps.le)
      ((bandJoint D.hR.le 1 (by norm_num) P.originalPartialLaw (partialBase D P t ht π)
        : Measure (ℝ×JointAction 2)).prod volume) = _
    convert! bandJoint_noisy D.hR D.heps.le 1 (by norm_num) P.originalPartialLaw
      (partialBase D P t ht π) using 1
  · change Measure.map (noisyJoint D.eps D.heps.le)
      ((bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw (bulkBase D P t ht π)
        : Measure (ℝ×JointAction 2)).prod volume) = _
    rw [bandJoint_noisy]
    convert! congrArg (fun q : ProbabilityMeasure (ℝ×JointAction 2) =>
      (q : Measure (ℝ×JointAction 2)))
      (bandJoint_cast_upper (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw
        (one_add_bulkPhysicalWidth D)
        (activeNoisyLaw (by norm_num : (0:ℝ)<1) D.heps.le P.originalBulkLaw (π 0))).symm using 1
  · change Measure.map (noisyJoint D.eps D.heps.le)
      ((bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl (P.originalTruncatedTailLaw t ht)
        (tailBase D P t ht π) : Measure (ℝ×JointAction 2)).prod volume) = _
    convert! bandJoint_noisy (by norm_num : (0:ℝ)<1) D.heps.le 2 le_rfl
      (P.originalTruncatedTailLaw t ht) (tailBase D P t ht π) using 1
  · change Measure.map Prod.fst ((upperJoint
      ⟨P.originalMovingUpperLaw t,P.originalMovingUpperLaw_probability t⟩ upperBid hupperBid
        : Measure (ℝ×JointAction 2)).prod (volume : Measure unitInterval)) = _
    exact (measurePreserving_fst (μ:=(upperJoint
      ⟨P.originalMovingUpperLaw t,P.originalMovingUpperLaw_probability t⟩ upperBid hupperBid
        : Measure (ℝ×JointAction 2))) (ν:=(volume : Measure unitInterval))).map_eq

theorem physical_components_joint :
    (∑ r,ENNReal.ofReal ((species P t ht).mass r) •
      (physicalComponent D P t ht πL π upperBid hupperBid r : Measure _))=
      (NativeNoisySource.joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)) := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,species,physicalComponent,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  have h := joint_active_components D P t ht π
  change _=fourJoint _ _ _ _ _ _ _ _
  rw [fourJoint,h]
  abel

theorem implement_joint_law :
    ((baseLaw D P t ht πL π upperBid hupperBid : Measure _).prod volume).map
      (implementJoint D)=(NativeNoisySource.joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)) := by
  change ((∑ r,ENNReal.ofReal ((species P t ht).mass r) •
    (taggedComponent D P t ht πL π upperBid hupperBid r : Measure Tagged)).prod volume).map _=_
  rw [OriginalFiniteFibers.prod_finsetSum,
    OriginalFiniteFibers.map_finsetSum _ _ _ (measurable_implementJoint D)]
  simp only [Measure.prod_smul_left,Measure.map_smul,component_implementation]
  exact physical_components_joint D P t ht πL π upperBid hupperBid

variable (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v → H≤ upperBid v)
  (m : ℕ) (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((m:ℝ)*(tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Γ" => NativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare

theorem realize_original_user :
    (drawLaw D P t ht πL π upperBid hupperBid).map (realize D)=userLaw Γ := by
  change (((baseLaw D P t ht πL π upperBid hupperBid : Measure Tagged).prod
    (volume : Measure unitInterval)).prod (permLaw 2)).map (Prod.map (implementJoint D) id)=_
  rw [←Measure.map_prod_map _ _ (measurable_implementJoint D) measurable_id,
    Measure.map_id,implement_joint_law,game_original_user]

theorem realize_original_iid :
    (Measure.pi (fun _ : Fin m => drawLaw D P t ht πL π upperBid hupperBid)).map
      (fun x => fun i => realize D (x i))=userProfileLaw Γ := by
  rw [Measure.pi_map_pi (fun _ => (measurable_realize D).aemeasurable)]
  unfold userProfileLaw
  congr 1
  funext i
  exact realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor m hrare

end FCAppendix.Affine.Tail04.LatentNoisyPopulation
