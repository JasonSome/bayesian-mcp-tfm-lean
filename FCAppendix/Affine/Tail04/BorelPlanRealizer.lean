import FCAppendix.Affine.Tail04.WeakProbability
import FCAppendix.Affine.FiniteSelector
import FCAppendix.Proposer.MeasurableExactCapacity

noncomputable section
namespace FCAppendix.Affine.Tail04.BorelPlanRealizer
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Classical

variable {P T A : Type*} [MeasurableSpace P]
  [TopologicalSpace T] [MeasurableSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace A] [MeasurableSpace A] [MetrizableSpace A] [BorelSpace A]
  [StandardBorelSpace A] [Fintype A] [Nonempty A]

variable (μ : P → WeakProbability.Law T) (π : P → WeakProbability.Law (T×A))
  (hπ : Measurable π) (u : P×T → A → ℝ)
  (hu : Measurable (Function.uncurry u))
  (hfst : ∀ p,((π p).val : Measure (T×A)).map Prod.fst=WeakProbability.toMeasure (μ p))
  (hall : ∀ p,∀ᵐ z ∂WeakProbability.toMeasure (π p),∀ a',u (p,z.1) a'≤ u (p,z.1) z.2)

def Best (z : P×T) (a : A) : Prop := ∀ a',u z a'≤ u z a

include hu in
omit [TopologicalSpace T] [PolishSpace T] [BorelSpace T] [TopologicalSpace A] [MetrizableSpace A] [BorelSpace A] [StandardBorelSpace A] [Nonempty A] in
lemma measurableSet_best : MeasurableSet {z : (P×T)×A | Best u z.1 z.2} := by
  simp only [Best,setOf_forall]
  exact MeasurableSet.iInter (fun a' => measurableSet_le
    (hu.comp (measurable_fst.prodMk measurable_const)) hu)

def fallback (z : P×T) : A := FiniteSelector.select (u z)
omit [MeasurableSpace P] [TopologicalSpace T] [MeasurableSpace T] [PolishSpace T] [BorelSpace T] [TopologicalSpace A] [MeasurableSpace A] [MetrizableSpace A] [BorelSpace A] [StandardBorelSpace A] in
lemma fallback_best (z : P×T) : Best u z (fallback u z) := FiniteSelector.select_max (u z)
include hu in
omit [TopologicalSpace T] [PolishSpace T] [BorelSpace T] [TopologicalSpace A] [MetrizableSpace A] [BorelSpace A] in
lemma measurable_fallback : Measurable (fallback u) :=
  FiniteSelector.measurable_select u (fun _ => hu.comp (measurable_id.prodMk measurable_const))

def jointKernel : Kernel P (T×A) := WeakProbability.kernel π hπ
instance : IsMarkovKernel (jointKernel π hπ) := by unfold jointKernel;infer_instance

def rawKernel : Kernel (P×T) A := (jointKernel π hπ).condKernel
instance : IsMarkovKernel (rawKernel π hπ) := by unfold rawKernel;infer_instance

def fiber (κ : Kernel (P×T) A) (p : P) : Kernel T A :=
  κ.comap (fun t => (p,t)) measurable_prodMk_left
instance (κ : Kernel (P×T) A) [IsMarkovKernel κ] (p : P) : IsMarkovKernel (fiber κ p) := by
  unfold fiber;infer_instance

include hfst in
omit [StandardBorelSpace A] [Nonempty A] in
lemma jointKernel_fst (p : P) : (jointKernel π hπ).fst p=WeakProbability.toMeasure (μ p) := hfst p

include hfst in
lemma raw_disintegrates (p : P) :
    WeakProbability.toMeasure (μ p) ⊗ₘ fiber (rawKernel π hπ) p=
      WeakProbability.toMeasure (π p) := by
  apply Measure.ext
  intro S hS
  rw [Measure.compProd_apply hS]
  have h := congrArg (fun κ : Kernel P (T×A) => κ p S)
    (Kernel.disintegrate (jointKernel π hπ) (jointKernel π hπ).condKernel)
  rw [Kernel.compProd_apply hS,jointKernel_fst μ π hπ hfst] at h
  exact h

include hu hfst hall in
set_option maxHeartbeats 800000 in
lemma raw_ae_best (p : P) :
    ∀ᵐ t ∂WeakProbability.toMeasure (μ p),∀ᵐ a ∂rawKernel π hπ (p,t),Best u (p,t) a := by
  have hS : MeasurableSet {z : T×A | Best u (p,z.1) z.2} :=
    (measurableSet_best u hu).preimage
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hj : ∀ᵐ z ∂(WeakProbability.toMeasure (μ p) ⊗ₘ fiber (rawKernel π hπ) p),
      Best u (p,z.1) z.2 := by
    rw [raw_disintegrates μ π hπ hfst]
    exact hall p
  exact (Measure.ae_compProd_iff hS).mp hj

def goodSignals : Set (P×T) := {z | rawKernel π hπ z {a | ¬Best u z a}=0}
include hu in
lemma measurableSet_goodSignals : MeasurableSet (goodSignals π hπ u) :=
  measurableSet_eq_fun
    (Kernel.measurable_kernel_prodMk_left (measurableSet_best u hu).compl) measurable_const

include hu hfst hall in
lemma ae_goodSignals (p : P) :
    ∀ᵐ t ∂WeakProbability.toMeasure (μ p),(p,t)∈goodSignals π hπ u :=
  (raw_ae_best μ π hπ u hu hfst hall p).mono (fun _ h => ae_iff.mp h)

def policyKernel : Kernel (P×T) A :=
  Kernel.piecewise (measurableSet_goodSignals π hπ u hu) (rawKernel π hπ)
    (Kernel.deterministic (fallback u) (measurable_fallback u hu))
instance : IsMarkovKernel (policyKernel π hπ u hu) := by unfold policyKernel;infer_instance

lemma policy_best (z : P×T) : ∀ᵐ a ∂policyKernel π hπ u hu z,Best u z a := by
  by_cases hz : z∈goodSignals π hπ u
  · simp only [policyKernel,Kernel.piecewise_apply,if_pos hz]
    exact ae_iff.mpr hz
  · simp only [policyKernel,Kernel.piecewise_apply,if_neg hz,Kernel.deterministic_apply]
    apply (ae_dirac_iff ((measurableSet_best u hu).preimage
      (measurable_const.prodMk measurable_id))).mpr
    exact fallback_best u z

include hfst hall in
lemma policy_disintegrates (p : P) :
    WeakProbability.toMeasure (μ p) ⊗ₘ fiber (policyKernel π hπ u hu) p=
      WeakProbability.toMeasure (π p) := by
  have he : fiber (policyKernel π hπ u hu) p=ᵐ[WeakProbability.toMeasure (μ p)]
      fiber (rawKernel π hπ) p := by
    filter_upwards [ae_goodSignals μ π hπ u hu hfst hall p] with t ht
    change policyKernel π hπ u hu (p,t)=rawKernel π hπ (p,t)
    simp only [policyKernel,Kernel.piecewise_apply,if_pos ht]
  exact (Measure.compProd_congr he).trans (raw_disintegrates μ π hπ hfst p)

include hfst hall in
theorem exists_sampler :
    ∃ f : (P×T) → unitInterval → A,
      Measurable (Function.uncurry f) ∧
      (∀ z,volume.map (f z)=policyKernel π hπ u hu z) ∧
      (∀ z s,Best u z (f z s)) ∧
      ∀ p,((WeakProbability.toMeasure (μ p)).prod (volume : Measure unitInterval)).map
        (fun z : T×unitInterval => (z.1,f (p,z.1) z.2))=WeakProbability.toMeasure (π p) := by
  obtain ⟨raw,hraw,hlaw⟩ := (policyKernel π hπ u hu).exists_measurable_map_eq_unitInterval
  let f : (P×T) → unitInterval → A := fun z s =>
    if Best u z (raw z s) then raw z s else fallback u z
  have hs : MeasurableSet {z : (P×T)×unitInterval | Best u z.1 (raw z.1 z.2)} :=
    (measurableSet_best u hu).preimage (measurable_fst.prodMk hraw)
  have hf : Measurable (Function.uncurry f) :=
    Measurable.ite hs hraw ((measurable_fallback u hu).comp measurable_fst)
  have hflaw (z : P×T) : volume.map (f z)=policyKernel π hπ u hu z := by
    have hrawz : Measurable (raw z) := hraw.comp (measurable_const.prodMk measurable_id)
    have hb := policy_best π hπ u hu z
    rw [←hlaw z] at hb
    have hgood : ∀ᵐ s ∂(volume : Measure unitInterval),Best u z (raw z s) :=
      (ae_map_iff hrawz.aemeasurable ((measurableSet_best u hu).preimage
        (measurable_const.prodMk measurable_id))).mp hb
    have he : f z=ᵐ[(volume : Measure unitInterval)] raw z := by
      filter_upwards [hgood] with s hs
      simp only [f,if_pos hs]
    exact (Measure.map_congr he).trans (hlaw z)
  refine ⟨f,hf,hflaw,?_,?_⟩
  · intro z s
    dsimp only [f]
    split_ifs with h
    · exact h
    · exact fallback_best u z
  · intro p
    have hf' : Measurable (fun z : T×unitInterval => f (p,z.1) z.2) :=
      hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hm := measurable_fst.prodMk hf'
    rw [←policy_disintegrates μ π hπ u hu hfst hall p]
    apply Measure.ext
    intro S hS
    rw [Measure.map_apply hm hS,Measure.prod_apply (hS.preimage hm),Measure.compProd_apply hS]
    apply lintegral_congr
    intro t
    change volume {s | (t,f (p,t) s)∈S}=policyKernel π hπ u hu (p,t) {a | (t,a)∈S}
    have hft : Measurable (f (p,t)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [←hflaw (p,t)]
    exact (Measure.map_apply hft (hS.preimage measurable_prodMk_left)).symm

end FCAppendix.Affine.Tail04.BorelPlanRealizer
