import FCAppendix.Affine.Tail04.OriginalUpperSource
import FCAppendix.Affine.Tail04.UpperLawInvariance
import FCAppendix.Affine.Tail04.SourceValuePartition
import FCAppendix.Affine.Tail04.ConditionalVersions

noncomputable section
namespace FCAppendix.Affine.Tail04.ValueParameters
open OriginalValues
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical
open Existence.RankEnvelope

variable (P : ValueParameters)

def originalFixedUpperJoint (m : ℕ) (hm : 200≤ m)
    (R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w) :
    ProbabilityMeasure (ℝ×JointAction 2) :=
  Hybrid.upperJoint P.originalFixedUpperLaw (P.originalFixedUpperBid m R)
    (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable

theorem originalFixedUpperJoint_properties (m : ℕ) (hm : 200≤ m)
    (R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w) :
    (P.originalFixedUpperJoint m hm R hR hRt : Measure (ℝ×JointAction 2)).map Prod.fst=
      (P.originalFixedUpperLaw : Measure ℝ) ∧
    (P.originalFixedUpperJoint m hm R hR hRt : Measure (ℝ×JointAction 2)).map (fun x => x.2.bid)=
      (P.originalFixedUpperLaw : Measure ℝ).map (P.originalFixedUpperBid m R) ∧
    (∀ᵐ x ∂(P.originalFixedUpperJoint m hm R hR hRt : Measure (ℝ×JointAction 2)),
      R≤ x.2.bid ∧ x.2.routeCount=1) ∧
    (∀ y : ℝ, (P.originalFixedUpperJoint m hm R hR hRt : Measure (ℝ×JointAction 2))
      {x | x.2.bid=y}=0) := by
  obtain ⟨hb,PH,hPH,hvalue,hbid,hshape,hnull⟩ :=
    (P.exists_originalFixedUpperJoint m hm R hR hRt).2.2
  have he : PH=P.originalFixedUpperJoint m hm R hR hRt := by
    rw [hPH]
    rfl
  rw [he] at hvalue hbid hshape hnull
  exact ⟨hvalue,hbid,hshape,hnull⟩

def originalFixedGame {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    FiniteGame m 2 (marketCapacity m) unitInterval :=
  ClosedUpperPriority.populationGame C U R (lowMass P.theta) partialMass
    (activeMass P.theta) P.low_mass_pos.le (by norm_num [partialMass])
    P.active_mass_pos.le (mass_sum P.theta) PL PA
    (P.originalFixedUpperJoint m hm R hR hRt) η hη0 hη1

theorem originalFixedGame_joint {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    let G := P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1
    G.F⊗ₘG.σ=Hybrid.populationJoint (lowMass P.theta) partialMass
      (activeMass P.theta) PL PA (P.originalFixedUpperJoint m hm R hR hRt) := by
  exact ClosedUpperPriority.populationGame_joint_law C U R (lowMass P.theta) partialMass
    (activeMass P.theta) P.low_mass_pos.le (by norm_num [partialMass])
    P.active_mass_pos.le (mass_sum P.theta) PL PA
    (P.originalFixedUpperJoint m hm R hR hRt) η hη0 hη1

theorem originalFixedGame_valueLaw {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1).F=valueLaw P := by
  change (Hybrid.populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
    PL PA (P.originalFixedUpperJoint m hm R hR hRt)).map Prod.fst=valueLaw P
  rw [Hybrid.populationJoint,Measure.map_add _ _ measurable_fst,
    Measure.map_add _ _ measurable_fst]
  simp only [Measure.map_smul,hVL,hVA,(P.originalFixedUpperJoint_properties m hm R hR hRt).1]
  rw [P.weighted_originalLowLaw,P.weighted_originalPartialLaw,P.weighted_originalFixedUpperLaw]
  exact P.fixed_restriction_partition

theorem originalFixedGame_mean {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w) (hUR : U< R)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) (i : Fin m) (y : ℝ) (hy : R≤ y) :
    meanAcceptProb (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) i y=
      bidRank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.originalFixedUpperBid m R) y := by
  have hH := P.originalFixedUpperJoint_properties m hm R hR hRt
  have hh := ClosedUpperPriority.population_upper_mean_eq_bidRank C U R
    (lowMass P.theta) partialMass (activeMass P.theta) hR hUR P.low_mass_pos.le
    (by norm_num [partialMass]) P.active_mass_pos.le (mass_sum P.theta) PL PA
    (P.originalFixedUpperJoint m hm R hR hRt) P.originalFixedUpperLaw hL hA
    (hH.2.2.1.mono (fun _ h => h.2)) hH.2.2.2 (P.originalFixedUpperBid m R)
    hH.2.1 η hη0 hη1 (by have := (capacity_bounds m hm).2.2.2;omega) i y hy
  simpa only [P.weighted_originalFixedUpperLaw,originalFixedGame] using hh

private theorem probability_eq_dirac_of_ae {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (a : A)
    (h : ∀ᵐ x ∂μ, x=a) : μ=Measure.dirac a := by
  apply Measure.ext
  intro E hE
  by_cases ha : a∈E
  · have he : E=ᵐ[μ] univ := by
      filter_upwards [h] with x hx
      change (x ∈ E) = (x ∈ univ)
      simp only [hx,ha,mem_univ]
    rw [measure_congr he,measure_univ]
    simp [Measure.dirac_apply' a hE,ha]
  · have he : μ E=0 := measure_eq_zero_iff_ae_notMem.mpr
      (h.mono (fun x hx => by simpa only [hx] using ha))
    rw [he]
    simp [Measure.dirac_apply' a hE,ha]

def fixUpperKernel (σ : Kernel ℝ (JointAction 2)) (t : ℝ)
    (b : ℝ → ℝ) (hb : Measurable b) : Kernel ℝ (JointAction 2) :=
  Kernel.piecewise (measurableSet_Ici : MeasurableSet (Ici t))
    (Kernel.deterministic (Hybrid.upperAction b)
    (Hybrid.measurable_upperAction b hb)) σ

instance fixUpperKernel_markov (σ : Kernel ℝ (JointAction 2)) [IsMarkovKernel σ]
    (t : ℝ) (b : ℝ → ℝ) (hb : Measurable b) :
    IsMarkovKernel (fixUpperKernel σ t b hb) := by
  unfold fixUpperKernel
  infer_instance

theorem fixUpperKernel_at_value (σ : Kernel ℝ (JointAction 2))
    (t : ℝ) (b : ℝ → ℝ) (hb : Measurable b) (v : ℝ) (hv : t≤ v) :
    fixUpperKernel σ t b hb v=Measure.dirac (Hybrid.upperAction b v) := by
  simp only [fixUpperKernel,Kernel.piecewise_apply,mem_Ici,if_pos hv,Kernel.deterministic_apply]

theorem fixUpperKernel_ae (F : Measure ℝ) [IsProbabilityMeasure F]
    (σ : Kernel ℝ (JointAction 2)) [IsMarkovKernel σ]
    (t : ℝ) (b : ℝ → ℝ) (hb : Measurable b)
    (hpure : ∀ᵐ x ∂F⊗ₘσ, t≤ x.1 → x.2=Hybrid.upperAction b x.1) :
    fixUpperKernel σ t b hb =ᵐ[F] σ := by
  filter_upwards [Measure.ae_ae_of_ae_compProd hpure] with v hv
  by_cases htv : t≤ v
  · rw [fixUpperKernel_at_value σ t b hb v htv]
    exact (probability_eq_dirac_of_ae (σ v) (Hybrid.upperAction b v)
      (hv.mono (fun _ h => h htv))).symm
  · simp only [fixUpperKernel,Kernel.piecewise_apply,mem_Ici,if_neg htv]

theorem originalFixedGame_upper_pure {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    let G := P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1
    ∀ᵐ x ∂G.F⊗ₘG.σ, P.vA-P.w≤ x.1 → x.2=Hybrid.upperAction (P.originalFixedUpperBid m R) x.1 := by
  dsimp only
  rw [P.originalFixedGame_joint]
  have hlow : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.1≤ P.d0 := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Iic).mp
    rw [hVL]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Iic).mpr
    exact Eventually.of_forall (fun v => v.property.2)
  have hpartial : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.1≤2+P.w := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Iic).mp
    rw [hVA]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Iic).mpr
    exact Eventually.of_forall (fun v => v.property.2)
  have hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), P.vA-P.w≤ x.1 →
      x.2=Hybrid.upperAction (P.originalFixedUpperBid m R) x.1 := by
    filter_upwards [hlow] with x hx hupper
    exfalso
    linarith [P.low_partial_gap,P.partial_active_gap,P.w_pos]
  have hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), P.vA-P.w≤ x.1 →
      x.2=Hybrid.upperAction (P.originalFixedUpperBid m R) x.1 := by
    filter_upwards [hpartial] with x hx hupper
    exfalso
    linarith [P.partial_active_gap]
  have hb := (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable
  have hf := measurable_id.prodMk (Hybrid.measurable_upperAction (P.originalFixedUpperBid m R) hb)
  have hgraph : MeasurableSet {x : ℝ×JointAction 2 | P.vA-P.w≤ x.1 →
      x.2=Hybrid.upperAction (P.originalFixedUpperBid m R) x.1} := by
    have he := (measurableSet_le
      (measurable_const : Measurable (fun _ : ℝ×JointAction 2 => P.vA-P.w))
      (measurable_fst : Measurable (fun x : ℝ×JointAction 2 => x.1))).compl.union
        (measurableSet_eq_fun measurable_snd
          ((Hybrid.measurable_upperAction _ hb).comp measurable_fst))
    convert! he using 1
    ext x
    simp only [Set.mem_setOf_eq,imp_iff_not_or,Set.mem_union,Set.mem_compl_iff,Function.comp_def]
  have hH : ∀ᵐ x ∂(P.originalFixedUpperJoint m hm R hR hRt : Measure (ℝ×JointAction 2)),
      P.vA-P.w≤ x.1 → x.2=Hybrid.upperAction (P.originalFixedUpperBid m R) x.1 := by
    change ∀ᵐ x ∂(P.originalFixedUpperLaw : Measure ℝ).map
      (fun v => (v,Hybrid.upperAction (P.originalFixedUpperBid m R) v)), _
    apply (ae_map_iff hf.aemeasurable hgraph).mpr
    exact Eventually.of_forall (fun v _ => rfl)
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure hL _,Measure.ae_smul_measure hA _⟩,
      Measure.ae_smul_measure hH _⟩

def originalFixedVersionGame {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    FiniteGame m 2 (marketCapacity m) unitInterval :=
  let G := P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1
  ConditionalVersions.withStrategy G
    (fixUpperKernel G.σ (P.vA-P.w) (P.originalFixedUpperBid m R)
      (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable)

theorem originalFixedVersionGame_upper {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) (v : ℝ) (hv : P.vA-P.w≤ v) :
    (P.originalFixedVersionGame hm C U R hR hRt PL PA η hη0 hη1).σ v=
      Measure.dirac (Hybrid.upperAction (P.originalFixedUpperBid m R) v) :=
  fixUpperKernel_at_value _ _ _
    (P.exists_originalFixedUpperJoint m hm R hR hRt).1.measurable v hv

theorem originalFixedVersionGame_problem {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) (i : Fin m) :
    problem (P.originalFixedVersionGame hm C U R hR hRt PL PA η hη0 hη1) i=
      problem (P.originalFixedGame hm C U R hR hRt PL PA η hη0 hη1) i := by
  apply ConditionalVersions.withStrategy_problem
  exact fixUpperKernel_ae _ _ _ _ _
    (P.originalFixedGame_upper_pure hm C U R hR hRt PL PA hVL hVA η hη0 hη1)

theorem originalFixedVersionGame_joint {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    let G := P.originalFixedVersionGame hm C U R hR hRt PL PA η hη0 hη1
    G.F⊗ₘG.σ=Hybrid.populationJoint (lowMass P.theta) partialMass
      (activeMass P.theta) PL PA (P.originalFixedUpperJoint m hm R hR hRt) := by
  change (ConditionalVersions.withStrategy _ _).F ⊗ₘ
      (ConditionalVersions.withStrategy _ _).σ = _
  rw [ConditionalVersions.withStrategy_joint _ _
    (fixUpperKernel_ae _ _ _ _ _
      (P.originalFixedGame_upper_pure hm C U R hR hRt PL PA hVL hVA η hη0 hη1))]
  exact P.originalFixedGame_joint hm C U R hR hRt PL PA η hη0 hη1

theorem originalFixedVersionGame_valueLaw {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    (P.originalFixedVersionGame hm C U R hR hRt PL PA η hη0 hη1).F=valueLaw P :=
  P.originalFixedGame_valueLaw hm C U R hR hRt PL PA hVL hVA η hη0 hη1

theorem originalFixedVersionGame_count_expect {m : ℕ} (hm : 200≤ m)
    (C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w) (hUR : U< R)
    (PL PA : ProbabilityMeasure (ℝ×JointAction 2))
    (hVL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val)
    (hVA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val)
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) (v : ℝ) (hv : P.vA-P.w≤ v)
    (f : Fin 3 → ℝ) :
    (conditionalTypeCountLaw
      (P.originalFixedVersionGame hm C U R hR hRt PL PA η hη0 hη1) (by omega) v).expect f=
      (1-rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v)*f 0+
        rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v*f 1 := by
  rw [conditionalTypeCountLaw_expect,P.originalFixedVersionGame_upper hm C U R hR hRt PL PA η hη0 hη1 v hv]
  have hc := capacity_bounds m hm
  have hterm (i : Fin m) : (∫ act,
      ((problem (P.originalFixedVersionGame hm C U R hR hRt PL PA η hη0 hη1) i).outcome act).expect f
        ∂Measure.dirac (Hybrid.upperAction (P.originalFixedUpperBid m R) v))=
      (1-rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v)*f 0+
        rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v*f 1 := by
    rw [integral_dirac,P.originalFixedVersionGame_problem hm C U R hR hRt PL PA hVL hVA η hη0 hη1 i]
    exact native_original_upper_count_expect _ P.fixedUpperMeasure (by omega) hc.2.2.1 hc.2.2.2
      (P.fixedUpperMeasure_mass_small.trans (by norm_num)) (P.vA-P.w) R hR hRt
      P.fixedUpperMeasure_support (P.originalFixedGame_mean hm C U R hR hRt hUR PL PA hL hA η hη0 hη1)
      i v hv f
  simp_rw [hterm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
  field_simp

theorem originalFixedVersionGame_count_tendsto
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hN200 : ∀ k, 200≤ N k)
    (C : ∀ k, Hybrid.ContextPolicy (N k) (marketCapacity (N k)) unitInterval)
    (U R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w) (hUR : U< R)
    (PL PA : ℕ → ProbabilityMeasure (ℝ×JointAction 2))
    (hVL : ∀ k, (PL k : Measure (ℝ×JointAction 2)).map Prod.fst=
      P.originalLowLaw.map Subtype.val)
    (hVA : ∀ k, (PA k : Measure (ℝ×JointAction 2)).map Prod.fst=
      P.originalPartialLaw.map Subtype.val)
    (hL : ∀ k, ∀ᵐ x ∂(PL k : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hA : ∀ k, ∀ᵐ x ∂(PA k : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    ∀ v, P.vA-P.w≤ v → ∀ f : Fin 3 → ℝ,
      Tendsto (fun k => (conditionalTypeCountLaw
        (P.originalFixedVersionGame (hN200 k) (C k) U R hR hRt (PL k) (PA k)
          η hη0 hη1) (by have := hN200 k;omega) v).expect f) atTop (𝓝 (f 1)) := by
  intro v hv f
  have hq := (original_fixed_rank_tendsto_one P.fixedUpperMeasure
    P.fixedUpperMeasure_mass_small v).comp hN
  have he (k : ℕ) := P.originalFixedVersionGame_count_expect (hN200 k) (C k)
    U R hR hRt hUR (PL k) (PA k) (hVL k) (hVA k) (hL k) (hA k) η hη0 hη1 v hv f
  simp_rw [he]
  simpa only [sub_self,zero_mul,one_mul,zero_add,Function.comp_def] using
    (((tendsto_const_nhds (x := (1:ℝ))).sub hq).mul_const (f 0)).add (hq.mul_const (f 1))

end FCAppendix.Affine.Tail04.ValueParameters
namespace FCAppendix.Affine.Tail04.OriginalValues
export FCAppendix.Affine.Tail04.ValueParameters (originalFixedUpperJoint originalFixedUpperJoint_properties originalFixedGame originalFixedGame_joint originalFixedGame_valueLaw originalFixedGame_mean fixUpperKernel fixUpperKernel_at_value fixUpperKernel_ae originalFixedGame_upper_pure originalFixedVersionGame originalFixedVersionGame_upper originalFixedVersionGame_problem originalFixedVersionGame_joint originalFixedVersionGame_valueLaw originalFixedVersionGame_count_expect originalFixedVersionGame_count_tendsto)
end FCAppendix.Affine.Tail04.OriginalValues
