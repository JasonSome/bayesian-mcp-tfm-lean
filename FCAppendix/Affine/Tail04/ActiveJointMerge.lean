import FCAppendix.Affine.Tail04.OriginalActiveComponents
import FCAppendix.Affine.Tail04.OriginalPopulation

noncomputable section
namespace FCAppendix.Affine.Tail04.ActiveJointMerge
open MeasureTheory ProbabilityTheory Set
open Existence.Distributional OriginalValues OriginalPopulation

section Two
variable {X : Type*} [MeasurableSpace X]

def normalizedTwo (x y : ℝ) (hx : 0≤ x) (hy : 0≤ y) (hs : 0< x+y)
    (μ ν : ProbabilityMeasure X) : ProbabilityMeasure X := by
  refine ⟨ENNReal.ofReal (x/(x+y)) • (μ : Measure X)+
    ENNReal.ofReal (y/(x+y)) • (ν : Measure X),?_⟩
  constructor
  simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add (div_nonneg hx hs.le) (div_nonneg hy hs.le)]
  rw [←add_div,div_self hs.ne',ENNReal.ofReal_one]

lemma normalizedTwo_weighted (x y : ℝ) (hx : 0≤ x) (hy : 0≤ y) (hs : 0< x+y)
    (μ ν : ProbabilityMeasure X) :
    ENNReal.ofReal (x+y) • (normalizedTwo x y hx hy hs μ ν : Measure X)=
      ENNReal.ofReal x • (μ : Measure X)+ENNReal.ofReal y • (ν : Measure X) := by
  change ENNReal.ofReal (x+y) • (_+_)=_
  rw [smul_add,smul_smul,smul_smul,←ENNReal.ofReal_mul hs.le,←ENNReal.ofReal_mul hs.le]
  congr 2 <;> field_simp

lemma measure_smul_cancel {a : ℝ} (ha : 0< a) {μ ν : Measure X}
    (h : ENNReal.ofReal a • μ=ENNReal.ofReal a • ν) : μ=ν := by
  have hz : ENNReal.ofReal a≠0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have h' := congrArg (fun η : Measure X => (ENNReal.ofReal a)⁻¹ • η) h
  simpa only [smul_smul,ENNReal.inv_mul_cancel hz ENNReal.ofReal_ne_top,one_smul] using h'
end Two

def extendBand {l u l' u' : ℝ} (hl : l'≤ l) (hu : u≤ u') (x : Icc l u) : Icc l' u' :=
  ⟨x.1,hl.trans x.2.1,x.2.2.trans hu⟩

lemma continuous_extendBand {l u l' u' : ℝ} (hl : l'≤ l) (hu : u≤ u') :
    Continuous (extendBand hl hu : Icc l u → Icc l' u') :=
  continuous_subtype_val.subtype_mk _

lemma measure_eq_of_real_map {l u : ℝ} (hlu : l≤ u)
    (μ ν : Measure (Icc l u)) (h : μ.map Subtype.val=ν.map Subtype.val) : μ=ν := by
  have hinv (η : Measure (Icc l u)) :
      (η.map Subtype.val).map (clipToBand l u hlu)=η := by
    rw [Measure.map_map (measurable_clipToBand l u hlu) measurable_subtype_coe]
    have hf : (clipToBand l u hlu) ∘ (Subtype.val : Icc l u → ℝ)=id := by
      funext x
      apply Subtype.ext
      exact clipToBand_eq l u hlu x.2
    rw [hf,Measure.map_id]
  rw [←hinv μ,h,hinv ν]

variable (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (u U : ℝ) (huU : 1+u≤ U)

local instance movingActive_probability (hle : P.M ≤ t) :
    IsProbabilityMeasure (P.originalMovingActiveLaw t hle) :=
  P.originalMovingActiveLaw_probability t hle

variable (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)
  (πT : Law (A:=Icc (1:ℝ) U) (P.originalTruncatedTailLaw t ht))

def bulkEmbedding :
    (Icc (P.vA-P.w) (P.vA+P.w) × Icc (1:ℝ) (1+u)) →
      Icc (P.vA-P.w) t × Icc (1:ℝ) U :=
  fun x => (extendBand le_rfl (P.active_tail_gap.le.trans ht.le) x.1,
    extendBand le_rfl huU x.2)

def tailEmbedding : (Icc P.M t × Icc (1:ℝ) U) → Icc (P.vA-P.w) t × Icc (1:ℝ) U :=
  fun x => (extendBand (by linarith [P.active_tail_gap,P.w_pos]) le_rfl x.1,x.2)

lemma continuous_bulkEmbedding : Continuous (bulkEmbedding P t ht u U huU) :=
  ((continuous_extendBand _ _).comp continuous_fst).prodMk
    ((continuous_extendBand _ _).comp continuous_snd)
lemma continuous_tailEmbedding : Continuous (tailEmbedding P t U) :=
  ((continuous_extendBand _ _).comp continuous_fst).prodMk continuous_snd

def bulkJoint : ProbabilityMeasure (Icc (P.vA-P.w) t × Icc (1:ℝ) U) :=
  πB.1.map (continuous_bulkEmbedding P t ht u U huU).measurable.aemeasurable

def tailJoint : ProbabilityMeasure (Icc (P.vA-P.w) t × Icc (1:ℝ) U) :=
  πT.1.map (continuous_tailEmbedding P t U).measurable.aemeasurable

def mergedActiveJoint : ProbabilityMeasure (Icc (P.vA-P.w) t × Icc (1:ℝ) U) :=
  normalizedTwo P.bulkWeight (P.truncatedTailWeight t) P.bulkWeight_pos.le
    (P.truncatedTailWeight_pos t ht).le (add_pos P.bulkWeight_pos (P.truncatedTailWeight_pos t ht))
    (bulkJoint P t ht u U huU πB) (tailJoint P t ht U πT)

lemma bulkJoint_real_value :
    (bulkJoint P t ht u U huU πB : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U)).map (fun x => (x.1 : ℝ))=
      P.originalBulkLaw.map Subtype.val := by
  change ((πB.1 : Measure (Icc (P.vA-P.w) (P.vA+P.w) × Icc (1:ℝ) (1+u))).map (bulkEmbedding P t ht u U huU)).map
    (fun x => (x.1 : ℝ))=_
  rw [Measure.map_map measurable_fst.subtype_val
    (continuous_bulkEmbedding P t ht u U huU).measurable]
  change (πB.1 : Measure (Icc (P.vA-P.w) (P.vA+P.w) × Icc (1:ℝ) (1+u))).map (fun x => (x.1 : ℝ))=_
  calc
    _ = ((πB.1 : Measure (Icc (P.vA-P.w) (P.vA+P.w) × Icc (1:ℝ) (1+u))).map Prod.fst).map Subtype.val :=
      (Measure.map_map measurable_subtype_coe measurable_fst).symm
    _ = _ := by rw [πB.2]

lemma tailJoint_real_value :
    (tailJoint P t ht U πT : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U)).map (fun x => (x.1 : ℝ))=
      (P.originalTruncatedTailLaw t ht).map Subtype.val := by
  change ((πT.1 : Measure (Icc P.M t × Icc (1:ℝ) U)).map (tailEmbedding P t U)).map (fun x => (x.1 : ℝ))=_
  rw [Measure.map_map measurable_fst.subtype_val
    (continuous_tailEmbedding P t U).measurable]
  change (πT.1 : Measure (Icc P.M t × Icc (1:ℝ) U)).map (fun x => (x.1 : ℝ))=_
  calc
    _ = ((πT.1 : Measure (Icc P.M t × Icc (1:ℝ) U)).map Prod.fst).map Subtype.val :=
      (Measure.map_map measurable_subtype_coe measurable_fst).symm
    _ = _ := by rw [πT.2]

lemma mergedActiveJoint_real_value :
    (mergedActiveJoint P t ht u U huU πB πT : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U)).map (fun x => (x.1 : ℝ))=
      (P.originalMovingActiveLaw t ht.le).map Subtype.val := by
  apply measure_smul_cancel (add_pos P.bulkWeight_pos (P.truncatedTailWeight_pos t ht))
  rw [←Measure.map_smul]
  rw [show ENNReal.ofReal (P.bulkWeight+P.truncatedTailWeight t) •
      (mergedActiveJoint P t ht u U huU πB πT : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U))=
      ENNReal.ofReal P.bulkWeight • (bulkJoint P t ht u U huU πB : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U))+
        ENNReal.ofReal (P.truncatedTailWeight t) • (tailJoint P t ht U πT : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U)) from
    normalizedTwo_weighted _ _ _ _ _ _ _]
  rw [Measure.map_add _ _ measurable_fst.subtype_val,Measure.map_smul,Measure.map_smul,
    bulkJoint_real_value,tailJoint_real_value,P.component_weight_sum]
  exact P.weighted_active_components t ht

def mergedActiveLaw : Law (A:=Icc (1:ℝ) U) (P.originalMovingActiveLaw t ht.le) := by
  refine ⟨mergedActiveJoint P t ht u U huU πB πT,?_⟩
  apply measure_eq_of_real_map (by linarith [P.active_tail_gap,P.w_pos])
  rw [Measure.map_map measurable_subtype_coe measurable_fst]
  exact mergedActiveJoint_real_value P t ht u U huU πB πT

theorem weighted_bandJoint_merged :
    ENNReal.ofReal (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t) •
      (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl (P.originalMovingActiveLaw t ht.le)
        (mergedActiveLaw P t ht u U huU πB πT) : Measure (ℝ × Game.JointAction 2)) =
      ENNReal.ofReal P.bulkWeight •
        (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw πB : Measure (ℝ × Game.JointAction 2)) +
      ENNReal.ofReal (P.truncatedTailWeight t) •
        (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl (P.originalTruncatedTailLaw t ht) πT : Measure (ℝ × Game.JointAction 2)) := by
  let f : Icc (P.vA-P.w) t × Icc (1:ℝ) U → ℝ×Game.JointAction 2 :=
    fun x => ((x.1:ℝ),bandAction (by norm_num : (0:ℝ)≤1) 2 le_rfl x.2)
  have hf : Measurable f := measurable_fst.subtype_val.prodMk
    ((measurable_bandAction (by norm_num : (0:ℝ)≤1) 2 le_rfl).comp measurable_snd)
  change ENNReal.ofReal _ • (mergedActiveJoint P t ht u U huU πB πT : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U)).map f=_
  rw [←Measure.map_smul,←P.component_weight_sum]
  rw [show ENNReal.ofReal (P.bulkWeight+P.truncatedTailWeight t) •
      (mergedActiveJoint P t ht u U huU πB πT : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U))=
      ENNReal.ofReal P.bulkWeight • (bulkJoint P t ht u U huU πB : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U))+
      ENNReal.ofReal (P.truncatedTailWeight t) • (tailJoint P t ht U πT : Measure (Icc (P.vA-P.w) t × Icc (1:ℝ) U)) from
    normalizedTwo_weighted _ _ _ _ _ _ _]
  rw [Measure.map_add _ _ hf,Measure.map_smul,Measure.map_smul]
  congr 1
  · congr 1
    change ((πB.1 : Measure (Icc (P.vA-P.w) (P.vA+P.w) × Icc (1:ℝ) (1+u))).map (bulkEmbedding P t ht u U huU)).map f=_
    rw [Measure.map_map hf (continuous_bulkEmbedding P t ht u U huU).measurable]
    rfl
  · congr 1
    change ((πT.1 : Measure (Icc P.M t × Icc (1:ℝ) U)).map (tailEmbedding P t U)).map f=_
    rw [Measure.map_map hf (continuous_tailEmbedding P t U).measurable]
    rfl

end FCAppendix.Affine.Tail04.ActiveJointMerge
