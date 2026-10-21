import FCAppendix.Existence.R01PayOnceNativeUsers
import FCAppendix.Existence.R01PayOnceNativeService
import FCAppendix.Existence.R01PayOnceMonotoneRepresentative

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded

theorem bounded_positiveQ_of_physical {W : ℝ} (g : ℝ) (hW : 0<W)
    (N n c : ℕ) (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (σ : Kernel (Value W) (FloorAction 0 W)) [IsMarkovKernel σ]
    (hphysical : ∀ᵐv ∂F,∀ᵐa ∂physicalKernel W g hW.le σ v,
      g<v→0<positiveQ N n c π a) :
    ∀ᵐw ∂physicalNetLaw W g hW.le F,∀ᵐa ∂σ w,
      0<w.1→0<positiveQ N n c π a := by
  let P : Value W × FloorAction 0 W→Prop := fun z=>0<z.1.1→0<positiveQ N n c π z.2
  have hPos : MeasurableSet {z : Value W × FloorAction 0 W|0<z.1.1} :=
    measurableSet_lt measurable_const measurable_fst.subtype_val
  have hQpos : MeasurableSet {z : Value W × FloorAction 0 W|0<positiveQ N n c π z.2} :=
    measurableSet_lt measurable_const ((measurable_positiveQ N n c hn π).comp measurable_snd)
  have hP : MeasurableSet {z|P z} := by
    convert hPos.compl.union hQpos using 1
    ext z
    simp [P,imp_iff_not_or]
  let mapType : ℝ×FloorAction 0 W→Value W × FloorAction 0 W :=
    fun z=>(physicalNetType W g hW.le z.1,z.2)
  have hmap : Measurable mapType :=
    ((continuous_physicalNetType W g hW.le).measurable.comp measurable_fst).prodMk measurable_snd
  have hphys : ∀ᵐz ∂(F ⊗ₘ physicalKernel W g hW.le σ),P (mapType z) := by
    apply Measure.ae_compProd_of_ae_ae (hP.preimage hmap)
    filter_upwards [hphysical] with v hv
    filter_upwards [hv] with a ha
    intro hw
    apply ha
    by_contra h
    have hz := (physicalNetType_eq_zero_iff W g hW v).mpr (le_of_not_gt h)
    exact (ne_of_gt hw) hz
  have hpush := (ae_map_iff hmap.aemeasurable hP).mpr hphys
  change ∀ᵐz ∂(F ⊗ₘ physicalKernel W g hW.le σ).map
    (fun z : ℝ×FloorAction 0 W=>(physicalNetType W g hW.le z.1,z.2)),P z at hpush
  rw [physicalKernel_jointLaw] at hpush
  exact (Measure.ae_compProd_iff hP).mp hpush

theorem mixedGame_native_support {m n c : ℕ} (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (g : ℝ) (hg : 0≤g)
    (hsupport : ∀ᵐv ∂F,∀ᵐa ∂κ v,
      (v≤g ↔ present a=false) ∧ (present a=true→0<bid a)) :
    ∀ᵐv ∂F,∀ᵐa ∂(mixedGame m n c hn F κ (Schedule.once n) g hg).σ v,
      (v≤g→a=Interim.abstain n) ∧ (g<v→0<a.bid ∧ a.routeCount=n) := by
  filter_upwards [hsupport] with v hv
  change ∀ᵐa ∂(κ.map (nativeAction n)) v,_
  rw [Kernel.map_apply _ (measurable_nativeAction n W),
    (measurableEmbedding_nativeAction hn).ae_map_iff]
  filter_upwards [hv] with a ha
  cases a with
  | inl u=>
    constructor
    · intro _; cases u; rfl
    · intro hpos
      exact False.elim (not_le_of_gt hpos (ha.1.mpr rfl))
  | inr b=>
    constructor
    · intro hneg
      have hfalse:=ha.1.mp hneg
      simp [present] at hfalse
    · intro _
      exact ⟨ha.2 rfl,rfl⟩

end FCAppendix.Bayes.PayOnceConstruction
