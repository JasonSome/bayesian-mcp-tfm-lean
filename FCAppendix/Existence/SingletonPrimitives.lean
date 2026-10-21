import FCAppendix.Existence.RankEnvelopeProbability

noncomputable section
namespace FCAppendix.Existence.Singleton
open MeasureTheory Set Filter

def positiveNetLaw (F : Measure ℝ) (g : ℝ) : Measure ℝ :=
  (F.restrict (Ioi g)).map (fun v => v-g)

instance positiveNetLaw_finite (F : Measure ℝ) [IsFiniteMeasure F] (g : ℝ) :
    IsFiniteMeasure (positiveNetLaw F g) := by unfold positiveNetLaw; infer_instance

theorem positiveNetLaw_mass (F : Measure ℝ) [IsFiniteMeasure F] (g : ℝ) :
    (positiveNetLaw F g).real univ=F.real (Ioi g) := by
  have hm : Measurable (fun v : ℝ => v-g) := measurable_id.sub_const g
  rw [positiveNetLaw,map_measureReal_apply hm MeasurableSet.univ,
    preimage_univ,measureReal_restrict_apply MeasurableSet.univ,univ_inter]

theorem positiveNetLaw_mass_le_one (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ) :
    (positiveNetLaw F g).real univ ≤ 1 := by
  rw [positiveNetLaw_mass]
  have hh := measureReal_mono (μ:=F) (subset_univ (Ioi g))
  simpa only [probReal_univ] using hh

theorem positiveNetLaw_supported (F : Measure ℝ) (g : ℝ) :
    ∀ᵐ w ∂positiveNetLaw F g, 0<w := by
  apply (ae_map_iff (measurable_id.sub_const g).aemeasurable measurableSet_Ioi).mpr
  filter_upwards [ae_restrict_mem (μ:=F) measurableSet_Ioi] with v hv
  exact sub_pos.mpr hv

theorem positiveNetLaw_atomless (F : Measure ℝ) (g : ℝ)
    [NullSingletonClass (F.restrict (Ioi g))] : NullSingletonClass (positiveNetLaw F g) := by
  constructor
  intro w
  have hm : Measurable (fun v : ℝ => v-g) := measurable_id.sub_const g
  rw [positiveNetLaw,Measure.map_apply hm (measurableSet_singleton w)]
  have he : (fun v : ℝ => v-g) ⁻¹' {w}={w+g} := by
    ext v
    simp only [mem_preimage,mem_singleton_iff]
    constructor <;> intro hv <;> linarith
  rw [he,measure_singleton]

theorem positiveNetLaw_tail (F : Measure ℝ) [IsFiniteMeasure F] (g : ℝ)
    {w : ℝ} (hw : 0 ≤ w) : (positiveNetLaw F g).real (Ioi w)=F.real (Ioi (g+w)) := by
  have hm : Measurable (fun v : ℝ => v-g) := measurable_id.sub_const g
  rw [positiveNetLaw,map_measureReal_apply hm measurableSet_Ioi,
    measureReal_restrict_apply (hm measurableSet_Ioi)]
  congr 1
  ext v
  simp only [mem_inter_iff,mem_preimage,mem_Ioi]
  constructor
  · intro hv
    linarith [hv.1]
  · intro hv
    constructor <;> linarith

theorem positiveNetLaw_bounded (F : Measure ℝ) (g H : ℝ)
    (hbound : ∀ᵐ v ∂F, g<v → v-g ≤ H) :
    ∀ᵐ w ∂positiveNetLaw F g, w ∈ Ioc 0 H := by
  apply (ae_map_iff (measurable_id.sub_const g).aemeasurable measurableSet_Ioc).mpr
  filter_upwards [ae_restrict_mem (μ:=F) measurableSet_Ioi,ae_restrict_of_ae hbound] with v hv hb
  exact ⟨sub_pos.mpr hv,hb hv⟩

end FCAppendix.Existence.Singleton
