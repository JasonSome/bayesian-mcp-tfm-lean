import FCAppendix.Affine.Tail04.CompactSelector
import FCAppendix.Affine.Tail04.WeakProbability
import FCAppendix.Affine.Tail04.EqualPrivateContinuity
import FCAppendix.Affine.FiniteSelector
import FCAppendix.Proposer.MeasurableExactCapacity

set_option maxHeartbeats 500000
noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateMeasurable
open MeasureTheory ProbabilityTheory Set Classical TopologicalSpace
open scoped BigOperators
open EqualPrivateFrontier EqualPrivateContinuity

lemma pointwise_sampler_of_kernel {Z B : Type*} [MeasurableSpace Z]
    [MeasurableSpace B] [Nonempty B] [StandardBorelSpace B]
    (κ : Kernel Z B) [IsMarkovKernel κ] (P : Z → B → Prop)
    (hP : MeasurableSet {w : Z × B | P w.1 w.2})
    (fallback : Z → B) (hfallback : Measurable fallback)
    (hfallbackP : ∀ z, P z (fallback z))
    (hκ : ∀ z, ∀ᵐ a ∂κ z, P z a) :
    ∃ f : Z → unitInterval → B,
      Measurable (Function.uncurry f) ∧
      (∀ z, volume.map (f z) = κ z) ∧ ∀ z u, P z (f z u) := by
  obtain ⟨raw, hraw, hlaw⟩ := κ.exists_measurable_map_eq_unitInterval
  let f : Z → unitInterval → B := fun z u =>
    if P z (raw z u) then raw z u else fallback z
  have hgood : MeasurableSet {w : Z × unitInterval | P w.1 (raw w.1 w.2)} := by
    simpa only [Set.preimage, Set.mem_setOf_eq, Function.uncurry, Function.comp_def, id_eq] using hP.preimage (measurable_fst.prodMk hraw)
  have hf : Measurable (Function.uncurry f) :=
    Measurable.ite hgood hraw (hfallback.comp measurable_fst)
  refine ⟨f, hf, ?_, ?_⟩
  · intro z
    have hrawz : Measurable (raw z) := by
      simpa only [Function.uncurry, Function.comp_def, id_eq] using hraw.comp (measurable_const.prodMk measurable_id)
    have hbest := hκ z
    rw [← hlaw z] at hbest
    have hPz : MeasurableSet {a | P z a} := by
      simpa only [Set.preimage, Set.mem_setOf_eq, Function.uncurry, Function.comp_def, id_eq] using hP.preimage (measurable_const.prodMk measurable_id)
    have hgoodz : ∀ᵐ u ∂(volume : Measure unitInterval), P z (raw z u) :=
      (ae_map_iff hrawz.aemeasurable hPz).mp hbest
    have he : f z =ᵐ[(volume : Measure unitInterval)] raw z := by
      filter_upwards [hgoodz] with u hu
      simp only [f, if_pos hu]
    exact (Measure.map_congr he).trans (hlaw z)
  · intro z u
    dsimp only [f]
    split_ifs with hz
    · exact hz
    · exact hfallbackP z

variable {ι T A : Type*} [Fintype ι]
  [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T]
  [PolishSpace T] [BorelSpace T] [Nonempty T]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A]
  [MetrizableSpace A] [BorelSpace A] [Nonempty A] [StandardBorelSpace A] [Fintype A]

abbrev Parameters (ι T : Type*) [MeasurableSpace T] (lo hi : ℝ) :=
  (ι → Icc lo hi) × WeakProbability.Law T

def forget {lo hi : ℝ} (p : Parameters ι T lo hi) : Parameter ι T lo hi :=
  (p.1,p.2.val)

omit [Fintype ι] [CompactSpace T] [PolishSpace T] [Nonempty T] in
lemma continuous_forget {lo hi : ℝ} :
    Continuous (forget : Parameters ι T lo hi → Parameter ι T lo hi) :=
  continuous_fst.prodMk (WeakProbability.continuous_val.comp continuous_snd)

def bids {lo hi : ℝ} (p : Parameters ι T lo hi) : ι → ℝ := parameterBids (forget p)

omit [Fintype ι] [CompactSpace T] [PolishSpace T] [Nonempty T] in
lemma continuous_bids {lo hi : ℝ} :
    Continuous (bids : Parameters ι T lo hi → ι → ℝ) :=
  continuous_pi fun i => continuous_subtype_val.comp
    ((continuous_apply i).comp continuous_fst)

def planGraph (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ : ℝ)
    (lo hi : ℝ) : Set (Parameters ι T lo hi × WeakProbability.Law (T × A)) :=
  {z | firstMarginal z.2.val = z.1.2.val ∧ gap x r ξ (bids z.1,z.2.val)=0}

omit [StandardBorelSpace A] [Nonempty T] in
lemma isClosed_planGraph (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) : IsClosed (planGraph x r ξ lo hi) := by
  apply IsClosed.inter
  · exact isClosed_eq
      (continuous_firstMarginal.comp (WeakProbability.continuous_val.comp continuous_snd))
      (WeakProbability.continuous_val.comp (continuous_snd.comp continuous_fst))
  · exact isClosed_eq ((continuous_gap x r ξ).comp
      ((continuous_bids.comp continuous_fst).prodMk
        (WeakProbability.continuous_val.comp continuous_snd))) continuous_const

omit [Nonempty T] in
lemma planGraph_nonempty (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) (p : Parameters ι T lo hi) :
    ∃ π : WeakProbability.Law (T × A), (p,π) ∈ planGraph x r ξ lo hi := by
  refine ⟨⟨(chosenPlan x r ξ (forget p)).1⟩,?_,chosenPlan_gap x r ξ (forget p)⟩
  apply ProbabilityMeasure.toMeasure_injective
  exact (chosenPlan x r ξ (forget p)).2

theorem exists_measurable_planLaw (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) :
    ∃ π : Parameters ι T lo hi → WeakProbability.Law (T × A), Measurable π ∧
      ∀ p, firstMarginal (π p).val=p.2.val ∧ gap x r ξ (bids p,(π p).val)=0 :=
  CompactSelector.exists_measurable_selector (planGraph x r ξ lo hi)
    (isClosed_planGraph x r ξ lo hi) (planGraph_nonempty x r ξ lo hi)

def planLaw (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) : Parameters ι T lo hi → WeakProbability.Law (T × A) :=
  (exists_measurable_planLaw x r ξ lo hi).choose

lemma measurable_planLaw (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) : Measurable (planLaw x r ξ lo hi) :=
  (exists_measurable_planLaw x r ξ lo hi).choose_spec.1

lemma planLaw_spec (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) (p : Parameters ι T lo hi) :
    firstMarginal (planLaw x r ξ lo hi p).val=p.2.val ∧
      gap x r ξ (bids p,(planLaw x r ξ lo hi p).val)=0 :=
  (exists_measurable_planLaw x r ξ lo hi).choose_spec.2 p

def q (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) (p : Parameters ι T lo hi) : ι → ℝ :=
  ambientMarginal x (planLaw x r ξ lo hi p).val

lemma measurable_q (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    Measurable (q x r ξ lo hi) :=
  ((continuous_ambientMarginal x).comp WeakProbability.continuous_val).measurable.comp
    (measurable_planLaw x r ξ lo hi)

lemma q_eq_chosenMarginal (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) (hξ : 0 < ξ) (hlo : 0 < lo) (p : Parameters ι T lo hi) :
    q x r ξ lo hi p = chosenMarginal x r ξ (forget p) := by
  have hfst : ((planLaw x r ξ lo hi p).val : Measure (T × A)).map Prod.fst =
      WeakProbability.toMeasure p.2 :=
    congrArg (fun μ : ProbabilityMeasure T => (μ : Measure T))
      (planLaw_spec x r ξ lo hi p).1
  let π : Plan (A := A) (WeakProbability.toMeasure p.2) :=
    ⟨(planLaw x r ξ lo hi p).val,hfst⟩
  let τ := chosenPlan x r ξ (forget p)
  have hπ := integralOptimal_of_gap_eq_zero x r (bids p) ξ
    (WeakProbability.toMeasure p.2) π (planLaw_spec x r ξ lo hi p).2
  have hτ := integralOptimal_of_gap_eq_zero x r (bids p) ξ
    (WeakProbability.toMeasure p.2) τ (chosenPlan_gap x r ξ (forget p))
  exact marginal_unique (WeakProbability.toMeasure p.2) x r (bids p) ξ hξ
    (fun i => hlo.trans_le (p.1 i).2.1) π τ hπ hτ

theorem continuous_q (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) (hξ : 0 < ξ) (hlo : 0 < lo) :
    Continuous (q x r ξ lo hi) := by
  have he : q x r ξ lo hi = fun p => chosenMarginal x r ξ (forget p) :=
    funext (q_eq_chosenMarginal x r ξ lo hi hξ hlo)
  rw [he]
  exact (continuous_chosenMarginal x r ξ lo hi hξ hlo).comp continuous_forget

def localUtility (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) (z : Parameters ι T lo hi × T) (a : A) : ℝ :=
  score x r (bids z.1) (q x r ξ lo hi z.1) ξ (z.2,a)

lemma measurable_localUtility (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) :
    Measurable (fun z : (Parameters ι T lo hi × T) × A =>
      localUtility x r ξ lo hi z.1 z.2) := by
  unfold localUtility score
  simp only [ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    smul_eq_mul]
  have hp : Measurable (fun z : (Parameters ι T lo hi × T) × A => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hta : Measurable (fun z : (Parameters ι T lo hi × T) × A => (z.1.2,z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  apply (r.continuous.measurable.comp hta).add
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_pi_apply i).comp (continuous_bids.measurable.comp hp)).mul
    (measurable_const.sub (measurable_const.mul
      ((measurable_pi_apply i).comp ((measurable_q x r ξ lo hi).comp hp))))).mul
    ((x i).continuous.measurable.comp hta)

def Best (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (z : Parameters ι T lo hi × T) (a : A) : Prop :=
  ∀ a', localUtility x r ξ lo hi z a' ≤ localUtility x r ξ lo hi z a

lemma measurableSet_best (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    MeasurableSet {z : (Parameters ι T lo hi × T) × A | Best x r ξ lo hi z.1 z.2} := by
  simp only [Best,setOf_forall]
  exact MeasurableSet.iInter fun a' => measurableSet_le
    ((measurable_localUtility x r ξ lo hi).comp (measurable_fst.prodMk measurable_const))
    (measurable_localUtility x r ξ lo hi)

def fallback (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (z : Parameters ι T lo hi × T) : A := FiniteSelector.select (localUtility x r ξ lo hi z)

lemma fallback_best (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (z : Parameters ι T lo hi × T) : Best x r ξ lo hi z (fallback x r ξ lo hi z) :=
  FiniteSelector.select_max (localUtility x r ξ lo hi z)

lemma measurable_fallback (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    Measurable (fallback x r ξ lo hi) := by
  change Measurable (fun z : Parameters ι T lo hi × T =>
    FiniteSelector.select (localUtility x r ξ lo hi z))
  apply FiniteSelector.measurable_select
  intro a
  simpa only [Function.comp_def] using (measurable_localUtility x r ξ lo hi).comp
    (show Measurable (fun z : Parameters ι T lo hi × T => (z,a)) from
      measurable_id.prodMk measurable_const)

def jointKernel (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    Kernel (Parameters ι T lo hi) (T × A) :=
  WeakProbability.kernel (planLaw x r ξ lo hi) (measurable_planLaw x r ξ lo hi)

instance (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    IsMarkovKernel (jointKernel x r ξ lo hi) := by unfold jointKernel; infer_instance

lemma jointKernel_fst (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (p : Parameters ι T lo hi) :
    (jointKernel x r ξ lo hi).fst p = WeakProbability.toMeasure p.2 :=
  congrArg (fun μ : ProbabilityMeasure T => (μ : Measure T))
    (planLaw_spec x r ξ lo hi p).1

def rawKernel (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    Kernel (Parameters ι T lo hi × T) A := (jointKernel x r ξ lo hi).condKernel

instance (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    IsMarkovKernel (rawKernel x r ξ lo hi) := by unfold rawKernel; infer_instance

def fiber {P : Type*} [MeasurableSpace P] (κ : Kernel (P × T) A) (p : P) : Kernel T A :=
  κ.comap (fun t => (p,t)) measurable_prodMk_left

instance {P : Type*} [MeasurableSpace P] (κ : Kernel (P × T) A) [IsMarkovKernel κ]
    (p : P) : IsMarkovKernel (fiber κ p) := by unfold fiber; infer_instance

lemma rawKernel_disintegrates (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (p : Parameters ι T lo hi) :
    WeakProbability.toMeasure p.2 ⊗ₘ fiber (rawKernel x r ξ lo hi) p =
      WeakProbability.toMeasure (planLaw x r ξ lo hi p) := by
  apply Measure.ext
  intro S hS
  rw [Measure.compProd_apply hS]
  have hh := congrArg (fun κ : Kernel (Parameters ι T lo hi) (T × A) => κ p S)
    (Kernel.disintegrate (jointKernel x r ξ lo hi) (jointKernel x r ξ lo hi).condKernel)
  rw [Kernel.compProd_apply hS,jointKernel_fst] at hh
  exact hh

lemma rawKernel_ae_best (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (p : Parameters ι T lo hi) :
    ∀ᵐ t ∂WeakProbability.toMeasure p.2,
      ∀ᵐ a ∂rawKernel x r ξ lo hi (p,t), Best x r ξ lo hi (p,t) a := by
  have hfst : ((planLaw x r ξ lo hi p).val : Measure (T × A)).map Prod.fst =
      WeakProbability.toMeasure p.2 :=
    congrArg (fun μ : ProbabilityMeasure T => (μ : Measure T))
      (planLaw_spec x r ξ lo hi p).1
  let π : Plan (A := A) (WeakProbability.toMeasure p.2) :=
    ⟨(planLaw x r ξ lo hi p).val,hfst⟩
  have hopt := integralOptimal_of_gap_eq_zero x r (bids p) ξ
    (WeakProbability.toMeasure p.2) π (planLaw_spec x r ξ lo hi p).2
  have hall := Existence.Distributional.allAction_of_integralOptimal
    (WeakProbability.toMeasure p.2) π (score x r (bids p) (marginal x π) ξ)
    (score x r (bids p) (marginal x π) ξ).continuous hopt
  have hq : marginal x π = q x r ξ lo hi p := rfl
  rw [hq] at hall
  have hS : MeasurableSet {z : T × A | Best x r ξ lo hi (p,z.1) z.2} := by
    simpa only [Set.preimage, Set.mem_setOf_eq, Function.comp_def] using (measurableSet_best x r ξ lo hi).preimage
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hjoint : ∀ᵐ z ∂(WeakProbability.toMeasure p.2 ⊗ₘ fiber (rawKernel x r ξ lo hi) p),
      Best x r ξ lo hi (p,z.1) z.2 := by
    rw [rawKernel_disintegrates]
    simpa only [Best, localUtility, Existence.Distributional.AllActionOptimal,
      π, WeakProbability.toMeasure, Prod.mk.eta] using hall
  exact (Measure.ae_compProd_iff hS).mp hjoint

def goodSignals (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    Set (Parameters ι T lo hi × T) :=
  {z | rawKernel x r ξ lo hi z {a | ¬Best x r ξ lo hi z a}=0}

lemma measurableSet_goodSignals (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) : MeasurableSet (goodSignals x r ξ lo hi) :=
  measurableSet_eq_fun (Kernel.measurable_kernel_prodMk_left
    (measurableSet_best x r ξ lo hi).compl) measurable_const

lemma ae_goodSignals (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (p : Parameters ι T lo hi) :
    ∀ᵐ t ∂WeakProbability.toMeasure p.2, (p,t) ∈ goodSignals x r ξ lo hi :=
  (rawKernel_ae_best x r ξ lo hi p).mono fun _ h => ae_iff.mp h

def policyKernel (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    Kernel (Parameters ι T lo hi × T) A :=
  Kernel.piecewise (measurableSet_goodSignals x r ξ lo hi) (rawKernel x r ξ lo hi)
    (Kernel.deterministic (fallback x r ξ lo hi) (measurable_fallback x r ξ lo hi))

instance (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    IsMarkovKernel (policyKernel x r ξ lo hi) := by unfold policyKernel; infer_instance

lemma policyKernel_best (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (z : Parameters ι T lo hi × T) :
    ∀ᵐ a ∂policyKernel x r ξ lo hi z, Best x r ξ lo hi z a := by
  by_cases hz : z ∈ goodSignals x r ξ lo hi
  · simp only [policyKernel,Kernel.piecewise_apply,if_pos hz]
    exact ae_iff.mpr hz
  · simp only [policyKernel,Kernel.piecewise_apply,if_neg hz,Kernel.deterministic_apply]
    apply (ae_dirac_iff ((measurableSet_best x r ξ lo hi).preimage
      (measurable_const.prodMk measurable_id))).mpr
    exact fallback_best x r ξ lo hi z

lemma policyKernel_disintegrates (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (p : Parameters ι T lo hi) :
    WeakProbability.toMeasure p.2 ⊗ₘ fiber (policyKernel x r ξ lo hi) p =
      WeakProbability.toMeasure (planLaw x r ξ lo hi p) := by
  have he : fiber (policyKernel x r ξ lo hi) p =ᵐ[WeakProbability.toMeasure p.2]
      fiber (rawKernel x r ξ lo hi) p := by
    filter_upwards [ae_goodSignals x r ξ lo hi p] with t ht
    change policyKernel x r ξ lo hi (p,t)=rawKernel x r ξ lo hi (p,t)
    simp only [policyKernel,Kernel.piecewise_apply,if_pos ht]
  exact (Measure.compProd_congr he).trans (rawKernel_disintegrates x r ξ lo hi p)

theorem exists_pointwise_sampler (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ) :
    ∃ f : (Parameters ι T lo hi × T) → unitInterval → A,
      Measurable (Function.uncurry f) ∧
      (∀ z, volume.map (f z)=policyKernel x r ξ lo hi z) ∧
      ∀ z u, Best x r ξ lo hi z (f z u) := by
  exact pointwise_sampler_of_kernel (policyKernel x r ξ lo hi)
    (Best x r ξ lo hi) (measurableSet_best x r ξ lo hi)
    (fallback x r ξ lo hi) (measurable_fallback x r ξ lo hi)
    (fallback_best x r ξ lo hi) (policyKernel_best x r ξ lo hi)

theorem sampler_jointLaw (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ)) (ξ lo hi : ℝ)
    (f : (Parameters ι T lo hi × T) → unitInterval → A)
    (hf : Measurable (Function.uncurry f))
    (hlaw : ∀ z, volume.map (f z)=policyKernel x r ξ lo hi z)
    (p : Parameters ι T lo hi) :
    ((WeakProbability.toMeasure p.2).prod (volume : Measure unitInterval)).map
      (fun z : T × unitInterval => (z.1,f (p,z.1) z.2)) =
      WeakProbability.toMeasure (planLaw x r ξ lo hi p) := by
  have hs : Measurable (fun z : T × unitInterval => f (p,z.1) z.2) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun z : T × unitInterval => (z.1,f (p,z.1) z.2)) :=
    measurable_fst.prodMk hs
  rw [← policyKernel_disintegrates x r ξ lo hi p]
  ext S hS
  rw [Measure.map_apply hm hS,Measure.prod_apply (hS.preimage hm),
    Measure.compProd_apply hS]
  apply lintegral_congr
  intro t
  change volume {u | (t,f (p,t) u) ∈ S} =
    policyKernel x r ξ lo hi (p,t) {a | (t,a) ∈ S}
  rw [← hlaw (p,t)]
  exact (Measure.map_apply
    (show Measurable (f (p,t)) from hf.comp (measurable_const.prodMk measurable_id))
    (show MeasurableSet {a | (t,a) ∈ S} from hS.preimage measurable_prodMk_left)).symm

lemma planGraph_marginal (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) (hξ : 0 < ξ) (hlo : 0 < lo)
    (p : Parameters ι T lo hi) (π : WeakProbability.Law (T × A))
    (hπ : (p,π) ∈ planGraph x r ξ lo hi) :
    ambientMarginal x π.val = q x r ξ lo hi p := by
  have hfst : (π.val : Measure (T × A)).map Prod.fst=WeakProbability.toMeasure p.2 :=
    congrArg (fun μ : ProbabilityMeasure T => (μ : Measure T)) hπ.1
  have hfst' : ((planLaw x r ξ lo hi p).val : Measure (T × A)).map Prod.fst=
      WeakProbability.toMeasure p.2 :=
    congrArg (fun μ : ProbabilityMeasure T => (μ : Measure T))
      (planLaw_spec x r ξ lo hi p).1
  let τ : Plan (A := A) (WeakProbability.toMeasure p.2) := ⟨π.val,hfst⟩
  let χ : Plan (A := A) (WeakProbability.toMeasure p.2) :=
    ⟨(planLaw x r ξ lo hi p).val,hfst'⟩
  exact marginal_unique (WeakProbability.toMeasure p.2) x r (bids p) ξ hξ
    (fun i => hlo.trans_le (p.1 i).2.1) τ χ
    (integralOptimal_of_gap_eq_zero x r (bids p) ξ _ τ hπ.2)
    (integralOptimal_of_gap_eq_zero x r (bids p) ξ _ χ
      (planLaw_spec x r ξ lo hi p).2)

lemma ae_best_of_planGraph (x : ι → C(T × A,ℝ)) (r : C(T × A,ℝ))
    (ξ lo hi : ℝ) (hξ : 0 < ξ) (hlo : 0 < lo)
    (p : Parameters ι T lo hi) (π : WeakProbability.Law (T × A))
    (hπ : (p,π) ∈ planGraph x r ξ lo hi) :
    ∀ᵐ z ∂WeakProbability.toMeasure π, Best x r ξ lo hi (p,z.1) z.2 := by
  have hfst : (π.val : Measure (T × A)).map Prod.fst=WeakProbability.toMeasure p.2 :=
    congrArg (fun μ : ProbabilityMeasure T => (μ : Measure T)) hπ.1
  let τ : Plan (A := A) (WeakProbability.toMeasure p.2) := ⟨π.val,hfst⟩
  have hopt := integralOptimal_of_gap_eq_zero x r (bids p) ξ _ τ hπ.2
  have hall := Existence.Distributional.allAction_of_integralOptimal
    (WeakProbability.toMeasure p.2) τ (score x r (bids p) (marginal x τ) ξ)
    (score x r (bids p) (marginal x τ) ξ).continuous hopt
  change ∀ᵐ z ∂WeakProbability.toMeasure π, ∀ a',
    score x r (bids p) (ambientMarginal x π.val) ξ (z.1,a') ≤
      score x r (bids p) (ambientMarginal x π.val) ξ z at hall
  rw [planGraph_marginal x r ξ lo hi hξ hlo p π hπ] at hall
  exact hall

theorem observable_mean_unique (x : ι → C(T × A,ℝ)) (r w : C(T × A,ℝ))
    (ξ lo hi : ℝ) (hξ : 0 < ξ) (hlo : 0 < lo)
    (p : Parameters ι T lo hi)
    (hone : ∀ᵐ t ∂WeakProbability.toMeasure p.2, ∀ a a',
      Best x r ξ lo hi (p,t) a → Best x r ξ lo hi (p,t) a' → w (t,a)=w (t,a'))
    (π : WeakProbability.Law (T × A)) (hπ : (p,π) ∈ planGraph x r ξ lo hi) :
    ambientMean π.val w = ambientMean (planLaw x r ξ lo hi p).val w := by
  let g : T → ℝ := fun t => w (t,fallback x r ξ lo hi (p,t))
  have hg : Measurable g := w.continuous.measurable.comp
    (measurable_id.prodMk ((measurable_fallback x r ξ lo hi).comp
      (measurable_const.prodMk measurable_id)))
  have he (τ : WeakProbability.Law (T × A))
      (hτ : (p,τ) ∈ planGraph x r ξ lo hi) :
      ambientMean τ.val w = ∫ t, g t ∂WeakProbability.toMeasure p.2 := by
    have hfst : (τ.val : Measure (T × A)).map Prod.fst=WeakProbability.toMeasure p.2 :=
      congrArg (fun μ : ProbabilityMeasure T => (μ : Measure T)) hτ.1
    have hone' : ∀ᵐ z ∂WeakProbability.toMeasure τ, ∀ a a',
        Best x r ξ lo hi (p,z.1) a → Best x r ξ lo hi (p,z.1) a' →
          w (z.1,a)=w (z.1,a') := by
      have hh := hone
      rw [← hfst] at hh
      exact ae_of_ae_map measurable_fst.aemeasurable hh
    have hzg : ∀ᵐ z ∂WeakProbability.toMeasure τ, w z=g z.1 := by
      filter_upwards [hone',ae_best_of_planGraph x r ξ lo hi hξ hlo p τ hτ] with z hz hb
      exact hz z.2 (fallback x r ξ lo hi (p,z.1)) hb (fallback_best x r ξ lo hi _)
    calc
      ambientMean τ.val w = ∫ z, g z.1 ∂WeakProbability.toMeasure τ := integral_congr_ae hzg
      _ = ∫ t, g t ∂WeakProbability.toMeasure p.2 := by
        rw [← hfst,integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
        rfl
  exact (he π hπ).trans (he _ (planLaw_spec x r ξ lo hi p)).symm

theorem continuous_observable_on_unique_best {P : Type*} [TopologicalSpace P]
    (x : ι → C(T × A,ℝ)) (r w : C(T × A,ℝ))
    (ξ lo hi : ℝ) (hξ : 0 < ξ) (hlo : 0 < lo)
    (p : P → Parameters ι T lo hi) (hp : Continuous p)
    (hone : ∀ y, ∀ᵐ t ∂WeakProbability.toMeasure (p y).2, ∀ a a',
      Best x r ξ lo hi (p y,t) a → Best x r ξ lo hi (p y,t) a' →
        w (t,a)=w (t,a')) :
    Continuous (fun y => ambientMean (planLaw x r ξ lo hi (p y)).val w) := by
  let G : Set (P × WeakProbability.Law (T × A)) :=
    {z | (p z.1,z.2) ∈ planGraph x r ξ lo hi}
  have hG : IsClosed G := (isClosed_planGraph x r ξ lo hi).preimage
    ((hp.comp continuous_fst).prodMk continuous_snd)
  apply continuous_unique_compact_factor G hG
    (fun π : WeakProbability.Law (T × A) => ambientMean π.val w)
    ((ProbabilityMeasure.continuous_integral_continuousMap w).comp
      WeakProbability.continuous_val)
  · intro y
    exact ⟨planLaw x r ξ lo hi (p y),planLaw_spec x r ξ lo hi (p y)⟩
  · intro y π hπ
    exact observable_mean_unique x r w ξ lo hi hξ hlo (p y) (hone y) π hπ

end FCAppendix.Affine.Tail04.EqualPrivateMeasurable
