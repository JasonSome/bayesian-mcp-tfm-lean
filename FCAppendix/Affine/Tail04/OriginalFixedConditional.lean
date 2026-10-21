import FCAppendix.Affine.Tail04.OriginalFixedReplacement
import Mathlib.Probability.Kernel.Disintegration.Unique

noncomputable section
namespace FCAppendix.Affine.Tail04.ValueParameters
open OriginalValues
open MeasureTheory ProbabilityTheory Set Filter Game Bayes Classical
open Existence.RankEnvelope

variable (P : ValueParameters)

theorem originalFixedUpperJoint_graph (m : ℕ) (hm : 200≤ m)
    (R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w) :
    ∀ᵐ x ∂(P.originalFixedUpperJoint m hm R hR hRt : Measure (ℝ×JointAction 2)),
      P.vA-P.w≤ x.1 ∧ x.2=Hybrid.upperAction (P.originalFixedUpperBid m R) x.1 := by
  have hb := (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable
  have hf := measurable_id.prodMk (Hybrid.measurable_upperAction (P.originalFixedUpperBid m R) hb)
  have hgraph : MeasurableSet {x : ℝ×JointAction 2 | P.vA-P.w≤ x.1 ∧
      x.2=Hybrid.upperAction (P.originalFixedUpperBid m R) x.1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_eq_fun measurable_snd
        ((Hybrid.measurable_upperAction _ hb).comp measurable_fst))
  change ∀ᵐ x ∂(P.originalFixedUpperLaw : Measure ℝ).map
    (fun v => (v,Hybrid.upperAction (P.originalFixedUpperBid m R) v)), _
  apply (ae_map_iff hf.aemeasurable hgraph).mpr
  exact P.originalFixedUpperLaw_support.mono (fun v hv => ⟨hv,rfl⟩)

theorem fixUpperKernel_below (σ : Kernel ℝ (JointAction 2))
    (t : ℝ) (b : ℝ → ℝ) (hb : Measurable b) (v : ℝ) (hv : v< t) :
    fixUpperKernel σ t b hb v=σ v := by
  simp only [fixUpperKernel,Kernel.piecewise_apply,mem_Ici,if_neg (not_le.mpr hv)]

theorem originalFixed_borrowed_joint (m : ℕ) (hm : 200≤ m)
    (R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (σ0 : Kernel ℝ (JointAction 2)) [IsMarkovKernel σ0]
    (hKL : (P.originalLowLaw.map Subtype.val)⊗ₘσ0=(PL : Measure (ℝ×JointAction 2)))
    (hKA : (P.originalPartialLaw.map Subtype.val)⊗ₘσ0=(PA : Measure (ℝ×JointAction 2))) :
    (valueLaw P)⊗ₘfixUpperKernel σ0 (P.vA-P.w) (P.originalFixedUpperBid m R)
      (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable=
        Hybrid.populationJoint (lowMass P.theta) partialMass (activeMass P.theta) PL PA
          (P.originalFixedUpperJoint m hm R hR hRt) := by
  let τ := fixUpperKernel σ0 (P.vA-P.w) (P.originalFixedUpperBid m R)
    (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable
  have hFL : ∀ᵐ v ∂P.originalLowLaw.map Subtype.val, v≤ P.d0 := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Iic).mpr
    exact Eventually.of_forall (fun v => v.property.2)
  have hFA : ∀ᵐ v ∂P.originalPartialLaw.map Subtype.val, v≤2+P.w := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Iic).mpr
    exact Eventually.of_forall (fun v => v.property.2)
  have hτL : τ=ᵐ[P.originalLowLaw.map Subtype.val] σ0 := by
    filter_upwards [hFL] with v hv
    exact fixUpperKernel_below _ _ _ _ v
      (by linarith [P.low_partial_gap,P.partial_active_gap,P.w_pos])
  have hτA : τ=ᵐ[P.originalPartialLaw.map Subtype.val] σ0 := by
    filter_upwards [hFA] with v hv
    exact fixUpperKernel_below _ _ _ _ v (by linarith [P.partial_active_gap])
  have hτH : τ=ᵐ[(P.originalFixedUpperLaw : Measure ℝ)]
      Kernel.deterministic (Hybrid.upperAction (P.originalFixedUpperBid m R))
        (Hybrid.measurable_upperAction _ (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable) := by
    filter_upwards [P.originalFixedUpperLaw_support] with v hv
    exact fixUpperKernel_at_value _ _ _
      (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable v hv
  have hF : ENNReal.ofReal (lowMass P.theta) • P.originalLowLaw.map Subtype.val+
      ENNReal.ofReal partialMass • P.originalPartialLaw.map Subtype.val+
      ENNReal.ofReal (activeMass P.theta) • (P.originalFixedUpperLaw : Measure ℝ)=valueLaw P := by
    rw [P.weighted_originalLowLaw,P.weighted_originalPartialLaw,P.weighted_originalFixedUpperLaw]
    exact P.fixed_restriction_partition
  change (valueLaw P)⊗ₘτ=_
  rw [←hF,Measure.compProd_add_left,Measure.compProd_add_left]
  simp only [Measure.compProd_smul_left]
  rw [Measure.compProd_congr hτL,Measure.compProd_congr hτA,Measure.compProd_congr hτH,hKL,hKA,
    Measure.compProd_deterministic]
  rfl

section Native
variable {m : ℕ} (hm : 200≤ m)
  (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
  (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
  (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
  (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1)
  (PH0 : ProbabilityMeasure (ℝ×JointAction 2))

def originalFixedConditionalGame : FiniteGame m 2 (marketCapacity m) unitInterval :=
  ConditionalVersions.withStrategy (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) (fixUpperKernel (P.originalFixedReference C U R PL PA η hη0 hη1 PH0).σ (P.vA-P.w) (P.originalFixedUpperBid m R) (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable)

theorem originalFixedConditionalGame_low_kernel (v : ℝ) (hv : v< P.vA-P.w) :
    ((P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0)).σ v=((P.originalFixedReference C U R PL PA η hη0 hη1 PH0)).σ v := fixUpperKernel_below _ _ _
      (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable v hv

theorem originalFixedConditionalGame_upper_kernel (v : ℝ) (hv : P.vA-P.w≤ v) :
    ((P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0)).σ v=Measure.dirac (Hybrid.upperAction (P.originalFixedUpperBid m R) v) :=
  fixUpperKernel_at_value _ _ _
    (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable v hv

variable
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (hKL : (P.originalLowLaw.map Subtype.val)⊗ₘ(P.originalFixedReference C U R PL PA η hη0 hη1 PH0).σ=(PL : Measure (ℝ×JointAction 2)))
    (hKA : (P.originalPartialLaw.map Subtype.val)⊗ₘ(P.originalFixedReference C U R PL PA η hη0 hη1 PH0).σ=(PA : Measure (ℝ×JointAction 2)))

include hVL hVA in
theorem originalFixedConditionalGame_value : ((P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0)).F=valueLaw P :=
  P.originalFixedGame_valueLaw hm C U R hR hRt PL PA hVL hVA η hη0 hη1

include hVL hVA hKL hKA in
theorem originalFixedConditionalGame_joint :
    ((P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0)).F⊗ₘ(P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0).σ=Hybrid.populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
      PL PA (P.originalFixedUpperJoint m hm R hR hRt) := by
  change ((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)).F⊗ₘ(fixUpperKernel (P.originalFixedReference C U R PL PA η hη0 hη1 PH0).σ (P.vA-P.w) (P.originalFixedUpperBid m R) (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable)=_
  rw [P.originalFixedGame_valueLaw hm C U R hR hRt PL PA hVL hVA η hη0 hη1]
  exact P.originalFixed_borrowed_joint m hm R hR hRt PL PA ((P.originalFixedReference C U R PL PA η hη0 hη1 PH0)).σ hKL hKA

include hVL hVA hKL hKA in
theorem originalFixedConditionalGame_kernel_ae : (fixUpperKernel (P.originalFixedReference C U R PL PA η hη0 hη1 PH0).σ (P.vA-P.w) (P.originalFixedUpperBid m R) (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable)=ᵐ[((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)).F] ((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)).σ := by
  have hj : ((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)).F⊗ₘ(fixUpperKernel (P.originalFixedReference C U R PL PA η hη0 hη1 PH0).σ (P.vA-P.w) (P.originalFixedUpperBid m R) (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable)=((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)).F⊗ₘ(P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1).σ := by
    rw [P.originalFixedGame_joint]
    exact P.originalFixedConditionalGame_joint hm C U R hR hRt PL PA η hη0 hη1 PH0 hVL hVA hKL hKA
  letI : Nonempty (JointAction 2) := ⟨⟨0,le_rfl,0,by omega⟩⟩
  have hτ := eq_condKernel_of_measure_eq_compProd (ρ:=((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)).F⊗ₘ(P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1).σ) (fixUpperKernel (P.originalFixedReference C U R PL PA η hη0 hη1 PH0).σ (P.vA-P.w) (P.originalFixedUpperBid m R) (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable)
    (by rw [Measure.fst_compProd];exact hj.symm)
  have hae : (fixUpperKernel (P.originalFixedReference C U R PL PA η hη0 hη1 PH0).σ
      (P.vA-P.w) (P.originalFixedUpperBid m R)
      (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable) =ᵐ[
        (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1).F]
      ((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1).F ⊗ₘ
        (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1).σ).condKernel := by
    convert! hτ using 1
    rw [Measure.fst_compProd]
    rfl
  exact hae.trans (condKernel_compProd ((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)).F ((P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1)).σ)

include hVL hVA hKL hKA in
theorem originalFixedConditionalGame_problem (i : Fin m) : problem (P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0) i=problem (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) i := by
  apply ConditionalVersions.withStrategy_problem
  exact P.originalFixedConditionalGame_kernel_ae hm C U R hR hRt PL PA η hη0 hη1 PH0 hVL hVA hKL hKA

include hVL hVA hKL hKA in
theorem originalFixedConditionalGame_lower_count
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (i : Fin m) (act : JointAction 2) (ha : act.bid< R) :
    (problem (P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0) i).outcome act=(problem (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) i).outcome act := by
  rw [P.originalFixedConditionalGame_problem hm C U R hR hRt PL PA η hη0 hη1 PH0 hVL hVA hKL hKA i]
  exact P.originalFixedGame_lower_count hm C U R hR hRt PL PA η hη0 hη1 PH0 hH0 i act ha

include hVL hVA hKL hKA in
theorem originalFixedConditionalGame_lower_expect
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (v : ℝ) (hv : v< P.vA-P.w)
    (hσv : ∀ᵐ act ∂((P.originalFixedReference C U R PL PA η hη0 hη1 PH0)).σ v, act.bid< R) (f : Fin 3 → ℝ) :
    (conditionalTypeCountLaw (P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0) (by omega) v).expect f=
      (conditionalTypeCountLaw (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) (by omega) v).expect f := by
  rw [conditionalTypeCountLaw_expect,conditionalTypeCountLaw_expect,
    P.originalFixedConditionalGame_low_kernel hm C U R hR hRt PL PA η hη0 hη1 PH0 v hv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hσv] with act ha
  rw [P.originalFixedConditionalGame_lower_count hm C U R hR hRt PL PA η hη0 hη1 PH0
    hVL hVA hKL hKA hH0 i act ha]

include hVL hVA hKL hKA in
theorem originalFixedConditionalGame_lower_law
    (hH0 : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (v : ℝ) (hv : v< P.vA-P.w) (hσv : ∀ᵐ act ∂((P.originalFixedReference C U R PL PA η hη0 hη1 PH0)).σ v, act.bid< R) :
    conditionalTypeCountLaw (P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0) (by omega) v=conditionalTypeCountLaw (P.originalFixedReference C U R PL PA η hη0 hη1 PH0) (by omega) v := by
  apply FiniteLaw.ext
  intro r
  have he := P.originalFixedConditionalGame_lower_expect hm C U R hR hRt PL PA η hη0 hη1 PH0
    hVL hVA hKL hKA hH0 v hv hσv (fun z => if z=r then 1 else 0)
  simpa only [FiniteLaw.expect_singleton] using he

include hVL hVA hKL hKA in
theorem originalFixedConditionalGame_upper_expect
    (hUR : U< R)
    (hLcap : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hAcap : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (v : ℝ) (hv : P.vA-P.w≤ v) (f : Fin 3 → ℝ) :
    (conditionalTypeCountLaw (P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0) (by omega) v).expect f=
      (1-rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v)*f 0+
        rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v*f 1 := by
  rw [conditionalTypeCountLaw_expect,
    P.originalFixedConditionalGame_upper_kernel hm C U R hR hRt PL PA η hη0 hη1 PH0 v hv]
  have hc := capacity_bounds m hm
  have hterm (i : Fin m) : (∫ act,((problem (P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0) i).outcome act).expect f
      ∂Measure.dirac (Hybrid.upperAction (P.originalFixedUpperBid m R) v))=
      (1-rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v)*f 0+
        rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v*f 1 := by
    rw [integral_dirac,P.originalFixedConditionalGame_problem hm C U R hR hRt PL PA η hη0 hη1 PH0
      hVL hVA hKL hKA i]
    exact native_original_upper_count_expect (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) P.fixedUpperMeasure (by omega) hc.2.2.1 hc.2.2.2
      (P.fixedUpperMeasure_mass_small.trans (by norm_num)) (P.vA-P.w) R hR hRt
      P.fixedUpperMeasure_support
      (P.originalFixedGame_mean hm C U R hR hRt hUR PL PA hLcap hAcap η hη0 hη1) i v hv f
  simp_rw [hterm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
  field_simp

include hVL hVA hKL hKA in
theorem originalFixedConditionalGame_upper_law
    (hUR : U< R)
    (hLcap : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hAcap : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (v : ℝ) (hv : P.vA-P.w≤ v) :
    conditionalTypeCountLaw (P.originalFixedConditionalGame hm C U R hR hRt PL PA η hη0 hη1 PH0) (by omega) v=
      upperSingletonCount (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v)
        (rank_bounds P.fixedUpperMeasure (m-1) (marketCapacity m) (by norm_num)
          (P.fixedUpperMeasure_mass_small.trans (by norm_num)) v).1
        (rank_bounds P.fixedUpperMeasure (m-1) (marketCapacity m) (by norm_num)
          (P.fixedUpperMeasure_mass_small.trans (by norm_num)) v).2 := by
  apply FiniteLaw.ext
  intro r
  have he := P.originalFixedConditionalGame_upper_expect hm C U R hR hRt PL PA η hη0 hη1 PH0
    hVL hVA hKL hKA hUR hLcap hAcap v hv (fun z => if z=r then 1 else 0)
  rw [←upperSingletonCount_expect (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v)
    (rank_bounds P.fixedUpperMeasure (m-1) (marketCapacity m) (by norm_num)
      (P.fixedUpperMeasure_mass_small.trans (by norm_num)) v).1
    (rank_bounds P.fixedUpperMeasure (m-1) (marketCapacity m) (by norm_num)
      (P.fixedUpperMeasure_mass_small.trans (by norm_num)) v).2
    (fun z : Fin 3 => if z=r then 1 else 0)] at he
  simpa only [FiniteLaw.expect_singleton] using he

end Native
end FCAppendix.Affine.Tail04.ValueParameters
namespace FCAppendix.Affine.Tail04.OriginalValues
export FCAppendix.Affine.Tail04.ValueParameters (originalFixedUpperJoint_graph fixUpperKernel_below originalFixed_borrowed_joint originalFixedConditionalGame originalFixedConditionalGame_low_kernel originalFixedConditionalGame_upper_kernel originalFixedConditionalGame_value originalFixedConditionalGame_joint originalFixedConditionalGame_kernel_ae originalFixedConditionalGame_problem originalFixedConditionalGame_lower_count originalFixedConditionalGame_lower_expect originalFixedConditionalGame_lower_law originalFixedConditionalGame_upper_expect originalFixedConditionalGame_upper_law)
end FCAppendix.Affine.Tail04.OriginalValues
