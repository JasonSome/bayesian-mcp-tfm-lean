import FCAppendix.Affine.UniformFinite.Early.Restricted
import FCAppendix.Affine.UniformFinite.ConditionalCounts
import FCAppendix.Affine.Hybrid.PopulationRows

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open scoped BigOperators

namespace OriginalPopulation

def uniformValue : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
instance uniformValue_probability : IsProbabilityMeasure uniformValue := by
  constructor
  simp [uniformValue]

def upperValue (i : Row) : Measure ℝ :=
  ENNReal.ofReal (1/(1-Uniform05.t i)) • volume.restrict (Ioc (Uniform05.t i) 1)

instance upperValue_probability (i : Row) : IsProbabilityMeasure (upperValue i) := by
  have ht:=Uniform05.t_lt_one i
  constructor
  simp only [upperValue,Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Ioc,smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity : 0≤1/(1-Uniform05.t i))]
  simp [(sub_pos.mpr ht).ne']

theorem uniform_split (i : Row) :
    uniformValue=ENNReal.ofReal (Uniform05.t i) • Uniform05.lowerValueMeasure i+
      ENNReal.ofReal (1-Uniform05.t i) • upperValue i := by
  have ht:=Uniform05.t_pos i
  have ht1:=Uniform05.t_lt_one i
  have hlow : ENNReal.ofReal (Uniform05.t i)*ENNReal.ofReal (1/Uniform05.t i)=1 := by
    rw [← ENNReal.ofReal_mul ht.le]
    simp [ht.ne']
  have hu : ENNReal.ofReal (1-Uniform05.t i)*ENNReal.ofReal (1/(1-Uniform05.t i))=1 := by
    rw [← ENNReal.ofReal_mul (sub_pos.mpr ht1).le]
    simp [(sub_pos.mpr ht1).ne']
  rw [Uniform05.lowerValueMeasure,upperValue,smul_smul,smul_smul,hlow,hu,one_smul,one_smul]
  have hd : Disjoint (Icc (0:ℝ) (Uniform05.t i)) (Ioc (Uniform05.t i) 1) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    exact not_lt_of_ge hv.2 hw.1
  have he : Icc (0:ℝ) (Uniform05.t i) ∪ Ioc (Uniform05.t i) 1=Icc (0:ℝ) 1 := by
    ext v
    simp only [mem_union,mem_Icc,mem_Ioc]
    constructor
    · rintro (⟨hv,hvt⟩|⟨hvt,hv⟩)
      · exact ⟨hv,hvt.trans ht1.le⟩
      · exact ⟨ht.le.trans hvt.le,hv⟩
    · intro hv
      by_cases hvt : v≤ Uniform05.t i
      · exact Or.inl ⟨hv.1,hvt⟩
      · exact Or.inr ⟨lt_of_not_ge hvt,hv.2⟩
  rw [← Measure.restrict_union hd measurableSet_Ioc,he]
  rfl

structure UpperPriorityLaw (i : Row) (R : ℝ) where
  sigma : Kernel ℝ (JointAction 2)
  markov : IsMarkovKernel sigma
  priority : ∀ᵐv∂upperValue i,∀ᵐa∂sigma v,R≤ a.bid ∧ a.routeCount=1

instance upper_markov {i : Row} {R : ℝ} (H : UpperPriorityLaw i R) : IsMarkovKernel H.sigma := H.markov

def constantUpper (i : Row) (R : ℝ) (hR : Uniform05.cap i< R) : UpperPriorityLaw i R where
  sigma := Kernel.deterministic (fun _ : ℝ=>(⟨R,(Uniform05.cap_pos i).le.trans hR.le,1,by decide⟩ : JointAction 2))
    measurable_const
  markov := inferInstance
  priority := ae_of_all _ (fun _=> by simp [Kernel.deterministic_apply])

def lowerAction (i : Row) (p : Value i×unitInterval) : JointAction 2 := Hybrid.lowBroadcast (baseBid i p)

theorem measurable_lowerAction (i : Row) : Measurable (lowerAction i) :=
  (Hybrid.measurable_lowBroadcast (Uniform05.cap i)).comp (continuous_baseBid i).measurable

def lowerKernel (i : Row) (sigma : Kernel (Value i) unitInterval) [IsSFiniteKernel sigma] : Kernel (Value i) (JointAction 2) where
  toFun v := (sigma v).map (fun q=> lowerAction i (v,q))
  measurable' := by
    apply Measure.measurable_of_measurable_coe _
    intro S hS
    have hsection (v : Value i) : Measurable (fun q=> lowerAction i (v,q)) :=
      (measurable_lowerAction i).comp (measurable_const.prodMk measurable_id)
    simp_rw [Measure.map_apply (hsection _) hS]
    exact Kernel.measurable_kernel_prodMk_left (hS.preimage (measurable_lowerAction i))

instance lowerKernel_markov (i : Row) (sigma : Kernel (Value i) unitInterval) [IsMarkovKernel sigma] :
    IsMarkovKernel (lowerKernel i sigma) := by
  constructor
  intro v
  exact Measure.isProbabilityMeasure_map
    ((measurable_lowerAction i).comp (measurable_const.prodMk measurable_id)).aemeasurable

def clampValue (i : Row) (v : ℝ) : Value i :=
  ⟨min (Uniform05.t i) (max 0 v),le_min (Uniform05.t_pos i).le (le_max_left _ _),min_le_left _ _⟩

theorem continuous_clampValue (i : Row) : Continuous (clampValue i) :=
  (continuous_const.min (continuous_const.max continuous_id)).subtype_mk _

theorem clampValue_coe (i : Row) (v : Value i) : clampValue i v=v := by
  apply Subtype.ext
  simp [clampValue,max_eq_right v.property.1,min_eq_right v.property.2]

def lowerRealKernel {i : Row} {M : ℕ} (E : ExactRestrictedLaw i M) : Kernel ℝ (JointAction 2) :=
  (lowerKernel i E.sigma).comap (clampValue i) (continuous_clampValue i).measurable

instance lowerRealKernel_markov {i : Row} {M : ℕ} (E : ExactRestrictedLaw i M) :
    IsMarkovKernel (lowerRealKernel E) := by unfold lowerRealKernel; infer_instance

def fullKernel {i : Row} {M : ℕ} {R : ℝ} (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) :
    Kernel ℝ (JointAction 2) :=
  Kernel.piecewise (s:=Icc (0:ℝ) (Uniform05.t i)) measurableSet_Icc (lowerRealKernel E) H.sigma

instance fullKernel_markov {i : Row} {M : ℕ} {R : ℝ}
    (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) : IsMarkovKernel (fullKernel E H) := by
  unfold fullKernel
  infer_instance

theorem fullKernel_at_lower {i : Row} {M : ℕ} {R : ℝ}
    (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) (v : Value i) :
    fullKernel E H v=(E.sigma v).map (fun q=> lowerAction i (v,q)) := by
  simp only [fullKernel,Kernel.piecewise_apply,if_pos v.property,lowerRealKernel,
    Kernel.comap_apply,clampValue_coe,lowerKernel]
  rfl

def lowerJoint {i : Row} {M : ℕ} (E : ExactRestrictedLaw i M) : ProbabilityMeasure (ℝ×JointAction 2) :=
  E.pi.1.map ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_lowerAction i)).aemeasurable

def upperJoint {i : Row} {R : ℝ} (H : UpperPriorityLaw i R) : ProbabilityMeasure (ℝ×JointAction 2) :=
  ⟨upperValue i⊗ₘH.sigma,inferInstance⟩

def fullLaw {i : Row} {M : ℕ} {R : ℝ} (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) :
    ProbabilityMeasure (ℝ×JointAction 2) := ⟨uniformValue⊗ₘfullKernel E H,inferInstance⟩

theorem fullLaw_value {i : Row} {M : ℕ} {R : ℝ}
    (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) :
    (fullLaw E H : Measure (ℝ×JointAction 2)).map Prod.fst=uniformValue := by
  change (uniformValue⊗ₘfullKernel E H).fst=uniformValue
  exact Measure.fst_compProd uniformValue (fullKernel E H)

theorem fullLaw_mixture {i : Row} {M : ℕ} {R : ℝ}
    (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) :
    (fullLaw E H : Measure (ℝ×JointAction 2))=
      ENNReal.ofReal (Uniform05.t i) • (lowerJoint E : Measure (ℝ×JointAction 2))+
      ENNReal.ofReal (1-Uniform05.t i) • (upperJoint H : Measure (ℝ×JointAction 2)) := by
  ext S hS
  have hfull : Measurable (fun v=> fullKernel E H v (Prod.mk v ⁻¹' S)) :=
    Kernel.measurable_kernel_prodMk_left hS
  change (uniformValue⊗ₘfullKernel E H) S=_
  rw [Measure.compProd_apply hS,uniform_split i,lintegral_add_measure,
    lintegral_smul_measure,lintegral_smul_measure,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  congr 1
  · congr 1
    rw [← lowerMeasure_real i,lintegral_map hfull (measurable_subtype_coe)]
    simp_rw [fullKernel_at_lower]
    have hlow : Measurable (fun p : Value i×unitInterval=>((p.1:ℝ),lowerAction i p)) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_lowerAction i)
    have hlow_map : (lowerJoint E : Measure (ℝ×JointAction 2))=
        (E.pi.1 : Measure (Value i×unitInterval)).map (fun p=> ((p.1:ℝ),lowerAction i p)) := rfl
    have hdis : lowerMeasure i⊗ₘE.sigma=(E.pi.1 : Measure (Value i×unitInterval)) := E.disintegration
    rw [hlow_map,Measure.map_apply hlow hS,← hdis,
      Measure.compProd_apply (hS.preimage hlow)]
    apply lintegral_congr
    intro v
    have hv : Measurable (fun q : unitInterval=>lowerAction i (v,q)) :=
      (measurable_lowerAction i).comp ((measurable_const (a:=v)).prodMk measurable_id)
    rw [Measure.map_apply hv
      (hS.preimage measurable_prodMk_left)]
    rfl
  · congr 1
    have hu_map : (upperJoint H : Measure (ℝ×JointAction 2))=upperValue i⊗ₘH.sigma := rfl
    rw [hu_map,Measure.compProd_apply hS]
    apply lintegral_congr_ae
    have hu : ∀ᵐv∂upperValue i,v∈Ioc (Uniform05.t i) 1 :=
      Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
    filter_upwards [hu] with v hv
    have hn : v∉Icc (0:ℝ) (Uniform05.t i):=fun h=> not_lt_of_ge h.2 hv.1
    simp only [fullKernel,Kernel.piecewise_apply,if_neg hn]

theorem lowerJoint_shape {i : Row} {M : ℕ} (E : ExactRestrictedLaw i M) :
    ∀ᵐx∂(lowerJoint E : Measure (ℝ×JointAction 2)),
      x.2.bid≤ Uniform05.cap i ∧ x.2.routeCount=2 := by
  apply (ae_map_iff
    ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_lowerAction i)).aemeasurable
    ((measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))).mpr
  exact ae_of_all _ (fun p=>⟨(baseBid i p).property.2,rfl⟩)

theorem upperJoint_shape {i : Row} {R : ℝ} (H : UpperPriorityLaw i R) :
    ∀ᵐx∂(upperJoint H : Measure (ℝ×JointAction 2)),R≤ x.2.bid ∧ x.2.routeCount=1 := by
  apply (Measure.ae_compProd_iff
    ((measurableSet_le measurable_const ((measurable_bid 2).comp measurable_snd)).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))).mpr
  exact H.priority

theorem fullLaw_shape {i : Row} {M : ℕ} {R : ℝ}
    (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) (hR : Uniform05.cap i< R) :
    ∀ᵐx∂(fullLaw E H : Measure (ℝ×JointAction 2)),Hybrid.PopulationGame.actionShape (Uniform05.cap i) x.2 := by
  rw [fullLaw_mixture]
  apply ae_add_measure_iff.mpr
  exact ⟨Measure.ae_smul_measure ((lowerJoint_shape E).mono (fun _ h=> Or.inl h)) _,
    Measure.ae_smul_measure ((upperJoint_shape H).mono (fun _ h=> Or.inr ⟨hR.trans_le h.1,h.2⟩)) _⟩

def seedLaw {i : Row} {M : ℕ} (E : ExactRestrictedLaw i M) : Measure ℝ :=
  cond (E.realBid : Measure ℝ) (Iic (Uniform05.t i/2))

variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

def primitiveGame (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) :
    FiniteGame M 2 (Uniform07.capacity M) unitInterval :=
  { Hybrid.PopulationGame.game M (Uniform07.capacity M) (fullLaw E H)
      (Uniform05.eta i) (Uniform05.eta_range i).1.le (Uniform05.eta_range i).2 (Uniform05.cap i) with
    F:=uniformValue
    hF:=inferInstance
    σ:=fullKernel E H
    hσ:=inferInstance }

def game (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) :
    FiniteGame M 2 (Uniform07.capacity M) unitInterval :=
  NativeContext.nativeGame i E.law (seedLaw E) (primitiveGame E H)

theorem game_value (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) :
    (game E H).F=uniformValue := rfl

theorem game_joint (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) :
    (game E H).F⊗ₘ(game E H).σ=(fullLaw E H : Measure (ℝ×JointAction 2)) := rfl

theorem game_lower_kernel (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R) (v : Value i) :
    (game E H).σ v=(E.sigma v).map (fun q=> lowerAction i (v,q)) := fullKernel_at_lower E H v

theorem game_profile_support (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : Uniform05.cap i< R) :
    ∀ᵐd∂userProfileLaw (game E H),d∈Hybrid.classifiedProfiles M (Uniform05.cap i) := by
  have hj : ∀ᵐx∂(game E H).F⊗ₘ(game E H).σ,
      Hybrid.PopulationGame.actionShape (Uniform05.cap i) x.2 := fullLaw_shape E H hR
  have hu : ∀ᵐu∂userLaw (game E H),
      Hybrid.PopulationGame.actionShape (Uniform05.cap i) u.1.2 :=
    (measurePreserving_fst (μ:=(game E H).F⊗ₘ(game E H).σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hj
  exact ae_all_iff.mpr (fun a=>
    (measurePreserving_eval (fun _ : Fin M=> userLaw (game E H)) a).quasiMeasurePreserving.ae hu)

theorem game_proposer_optimal (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : Uniform05.cap i< R) :
    ∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal (Uniform07.capacity M)
        (beliefReceipts (game E H).A
          (posteriorCountBelief (game E H)
            (Hybrid.classifiedPosterior (game E H) (R:=R) (game_profile_support E H hR)) j L) L)
        ((game E H).policy j L s).val :=
  NativeContext.proposer_optimal i E.law (seedLaw E) (primitiveGame E H) rfl hR rfl
    (game_profile_support E H hR)

end OriginalPopulation
end FCAppendix.Affine.UniformFinite
