import FCAppendix.Existence.R01PayOnceBroadcastLaw
import Mathlib.Probability.Kernel.Composition.Lemmas

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional

def physicalNetType (W g : ℝ) (hW : 0≤W) (v : ℝ) : Value W :=
  ⟨min W (max 0 (v-g)),le_min hW (le_max_left _ _),min_le_left _ _⟩

theorem continuous_physicalNetType (W g : ℝ) (hW : 0≤W) :
    Continuous (physicalNetType W g hW) :=
  (continuous_const.min (continuous_const.max (continuous_id.sub continuous_const))).subtype_mk _

@[simp] theorem physicalNetType_eq_net (W g : ℝ) (hW : 0≤W) (v : ℝ)
    (hv : max 0 (v-g)≤W) : (physicalNetType W g hW v).1=max 0 (v-g) := min_eq_right hv

theorem physicalNetType_eq_zero_iff (W g : ℝ) (hW : 0<W) (v : ℝ) :
    (physicalNetType W g hW.le v).1=0 ↔ v≤g := by
  constructor
  · intro h
    by_contra hv
    have hvg : 0<v-g := sub_pos.mpr (lt_of_not_ge hv)
    have hm : 0 < min W (max 0 (v-g)) := lt_min hW (lt_of_lt_of_le hvg (le_max_right _ _))
    exact (ne_of_gt hm) h
  · intro hv
    change min W (max 0 (v-g))=0
    rw [max_eq_left (sub_nonpos.mpr hv),min_eq_right hW.le]

def physicalNetLaw (W g : ℝ) (hW : 0≤W) (F : Measure ℝ) : Measure (Value W) :=
  F.map (physicalNetType W g hW)

instance physicalNetLaw_probability (W g : ℝ) (hW : 0≤W)
    (F : Measure ℝ) [IsProbabilityMeasure F] : IsProbabilityMeasure (physicalNetLaw W g hW F) :=
  Measure.isProbabilityMeasure_map (continuous_physicalNetType W g hW).measurable.aemeasurable

def physicalKernel (W g : ℝ) (hW : 0≤W) (σ : Kernel (Value W) (FloorAction 0 W)) :
    Kernel ℝ (FloorAction 0 W) :=
  σ.comap (physicalNetType W g hW) (continuous_physicalNetType W g hW).measurable

instance physicalKernel_markov (W g : ℝ) (hW : 0≤W)
    (σ : Kernel (Value W) (FloorAction 0 W)) [IsMarkovKernel σ] :
    IsMarkovKernel (physicalKernel W g hW σ) := inferInstanceAs
      (IsMarkovKernel (σ.comap (physicalNetType W g hW) (continuous_physicalNetType W g hW).measurable))

theorem map_compProd_comap {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] (F : Measure X) [IsProbabilityMeasure F]
    (f : X→Y) (hf : Measurable f) (σ : Kernel Y A) [IsMarkovKernel σ] :
    (F ⊗ₘ σ.comap f hf).map (fun z : X×A=>(f z.1,z.2))=(F.map f) ⊗ₘ σ := by
  have hmap : Measurable (fun z : X×A=>(f z.1,z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  ext S hS
  rw [Measure.map_apply hmap hS,Measure.compProd_apply (hS.preimage hmap)]
  letI : IsProbabilityMeasure (F.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  rw [Measure.compProd_apply hS,lintegral_map (Kernel.measurable_kernel_prodMk_left hS) hf]
  rfl

theorem physicalKernel_jointLaw (W g : ℝ) (hW : 0≤W)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (σ : Kernel (Value W) (FloorAction 0 W)) [IsMarkovKernel σ] :
    (F ⊗ₘ physicalKernel W g hW σ).map
      (fun z : ℝ×FloorAction 0 W=>(physicalNetType W g hW z.1,z.2))=
      physicalNetLaw W g hW F ⊗ₘ σ :=
  map_compProd_comap F (physicalNetType W g hW)
    (continuous_physicalNetType W g hW).measurable σ

theorem physicalKernel_actionLaw (W g : ℝ) (hW : 0≤W)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (σ : Kernel (Value W) (FloorAction 0 W)) [IsMarkovKernel σ] :
    (F ⊗ₘ physicalKernel W g hW σ).map Prod.snd=
      (physicalNetLaw W g hW F ⊗ₘ σ).map Prod.snd := by
  have h := congrArg (fun ν : Measure (Value W × FloorAction 0 W)=>ν.map Prod.snd)
    (physicalKernel_jointLaw W g hW F σ)
  have hmap : Measurable (fun z : ℝ×FloorAction 0 W=>(physicalNetType W g hW z.1,z.2)) :=
    ((continuous_physicalNetType W g hW).measurable.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map measurable_snd hmap] at h
  exact h

theorem exists_physical_broadcast_kernel (W g : ℝ) (hW : 0<W)
    (N n c : ℕ) (hN : 0<N) (hn : 2≤n) (hc1 : 1≤c) (hcm : c<N+1)
    (F : Measure ℝ) [IsProbabilityMeasure F] :
    ∃ (π : FloorLaw 0 W (physicalNetLaw W g hW.le F))
      (σ : Kernel (Value W) (FloorAction 0 W)),
      IsMarkovKernel σ ∧ physicalNetLaw W g hW.le F ⊗ₘ σ=
        (π.1 : Measure (Value W × FloorAction 0 W)) ∧
      (F ⊗ₘ physicalKernel W g hW.le σ).map
        (fun z : ℝ×FloorAction 0 W=>(physicalNetType W g hW.le z.1,z.2))=
        (π.1 : Measure (Value W × FloorAction 0 W)) ∧
      (∀ᵐv ∂F,∀ᵐa ∂physicalKernel W g hW.le σ v,∀a' : FloorAction 0 W,
        positivePayoff N n c π.1 (physicalNetType W g hW.le v,a')≤
          positivePayoff N n c π.1 (physicalNetType W g hW.le v,a)) ∧
      (∀ᵐv ∂F,∀ᵐa ∂physicalKernel W g hW.le σ v,
        (v≤g ↔ present a=false) ∧ (present a=true→0<bid a)) := by
  obtain ⟨π,σ,hσ,hdis,hIC,hσIC,hσsupport,hzero⟩ :=
    exists_bounded_broadcast_law W hW N n c hN hn hc1 hcm (physicalNetLaw W g hW.le F)
  letI : IsMarkovKernel σ := hσ
  refine ⟨π,σ,hσ,hdis,(physicalKernel_jointLaw W g hW.le F σ).trans hdis,?_,?_⟩
  · exact ae_of_ae_map (continuous_physicalNetType W g hW.le).measurable.aemeasurable hσIC
  · have hs := ae_of_ae_map (continuous_physicalNetType W g hW.le).measurable.aemeasurable hσsupport
    filter_upwards [hs] with v hv
    filter_upwards [hv] with a ha
    exact ⟨(physicalNetType_eq_zero_iff W g hW v).symm.trans ha.1,ha.2⟩

theorem physicalNetType_eq_net_ae (W g : ℝ) (hW : 0≤W) (F : Measure ℝ)
    (hbounded : ∀ᵐv ∂F,max 0 (v-g)≤W) :
    ∀ᵐv ∂F,(physicalNetType W g hW v).1=max 0 (v-g) :=
  hbounded.mono (fun v hv=>physicalNetType_eq_net W g hW v hv)

theorem physicalNetType_eq_sub_of_positive (W g : ℝ) (hW : 0≤W) (v : ℝ)
    (hv : g<v) (hbounded : max 0 (v-g)≤W) :
    (physicalNetType W g hW v).1=v-g := by
  rw [physicalNetType_eq_net W g hW v hbounded,max_eq_right (sub_nonneg.mpr hv.le)]

theorem physicalNetLaw_positive_atomless (W g : ℝ) (hW : 0<W)
    (F : Measure ℝ) (hbounded : ∀ᵐv ∂F,max 0 (v-g)≤W)
    (hatom : ∀v,g<v→F {v}=0) (w : Value W) (hw : 0<w.1) :
    physicalNetLaw W g hW.le F {w}=0 := by
  unfold physicalNetLaw
  rw [Measure.map_apply (continuous_physicalNetType W g hW.le).measurable (measurableSet_singleton w)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hnull := hatom (g+w.1) (by linarith)
  filter_upwards [hbounded,measure_eq_zero_iff_ae_notMem.mp hnull] with v hv hneq
  intro hmem
  have he : physicalNetType W g hW.le v=w := hmem
  have hvpos : g<v := by
    by_contra h
    have hz := (physicalNetType_eq_zero_iff W g hW v).mpr (le_of_not_gt h)
    rw [he] at hz
    linarith
  have hnet := physicalNetType_eq_sub_of_positive W g hW.le v hvpos hv
  have hval := congrArg Subtype.val he
  rw [hnet] at hval
  apply hneq
  change v=g+w.1
  linarith

theorem physicalNetLaw_real_positive_atomless (W g : ℝ) (hW : 0<W)
    (F : Measure ℝ) (hbounded : ∀ᵐv ∂F,max 0 (v-g)≤W)
    (hatom : ∀v,g<v→F {v}=0) (w : ℝ) (hw : 0<w) :
    (physicalNetLaw W g hW.le F).map (Subtype.val : Value W→ℝ) {w}=0 := by
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton w)]
  by_cases hwW : w≤W
  · let wb : Value W := ⟨w,hw.le,hwW⟩
    have he : (Subtype.val : Value W→ℝ) ⁻¹' {w}={wb} := by
      ext z
      simp only [mem_preimage,mem_singleton_iff]
      exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
    rw [he]
    exact physicalNetLaw_positive_atomless W g hW F hbounded hatom wb hw
  · have he : (Subtype.val : Value W→ℝ) ⁻¹' {w}=∅ := by
      ext z
      simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
      intro h
      exact hwW (h ▸ z.2.2)
    rw [he,measure_empty]

end FCAppendix.Existence.PayOnceBounded
