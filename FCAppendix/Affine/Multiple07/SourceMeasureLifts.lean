import FCAppendix.Affine.Multiple07.Source
import FCAppendix.Affine.LowBody.NoiseParameters
import FCAppendix.Affine.Hybrid.FavoredNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Set

def intervalValueLaw (F : Measure ℝ) (l u : ℝ) (hlu : l ≤ u) : Measure (Icc l u) :=
  F.map (Set.projIcc l u hlu)

instance intervalValueLaw_probability (F : Measure ℝ) [IsProbabilityMeasure F]
    (l u : ℝ) (hlu : l ≤ u) : IsProbabilityMeasure (intervalValueLaw F l u hlu) :=
  Measure.isProbabilityMeasure_map continuous_projIcc.measurable.aemeasurable

theorem intervalValueLaw_map_val (F : Measure ℝ) (l u : ℝ) (hlu : l ≤ u)
    (hs : ∀ᵐ v ∂F, v ∈ Icc l u) :
    (intervalValueLaw F l u hlu).map (fun v : Icc l u => (v : ℝ)) = F := by
  rw [intervalValueLaw, Measure.map_map measurable_subtype_coe continuous_projIcc.measurable]
  calc
    _ = F.map (id : ℝ → ℝ) := by
      apply Measure.map_congr
      filter_upwards [hs] with v hv
      exact congrArg Subtype.val (Set.projIcc_val hlu (⟨v, hv⟩ : Icc l u))
    _ = F := Measure.map_id

theorem intervalValueLaw_atomless (F : Measure ℝ) [NullSingletonClass F]
    (l u : ℝ) (hlu : l ≤ u) (hs : ∀ᵐ v ∂F, v ∈ Icc l u) :
    NullSingletonClass (intervalValueLaw F l u hlu) := by
  constructor
  intro x
  have hz : ((intervalValueLaw F l u hlu).map (fun v : Icc l u => (v : ℝ)))
      {(x : ℝ)} = 0 := by
    rw [intervalValueLaw_map_val F l u hlu hs]
    exact measure_singleton _
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton (x : ℝ))] at hz
  have he : (fun v : Icc l u => (v : ℝ)) ⁻¹' {(x : ℝ)} = {x} := by
    ext y
    change ((y : ℝ) = (x : ℝ)) ↔ y = x
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rwa [he] at hz

def sourceLowValueLaw : Measure (LowBody.LowValue lowCeiling) :=
  intervalValueLaw (bandLaw .low) 0 lowCeiling (by norm_num [lowCeiling])

instance sourceLowValueLaw_probability : IsProbabilityMeasure sourceLowValueLaw := by
  unfold sourceLowValueLaw
  infer_instance

theorem sourceLowValueLaw_map_val :
    sourceLowValueLaw.map (fun v : LowBody.LowValue lowCeiling => (v : ℝ)) = bandLaw .low := by
  apply intervalValueLaw_map_val
  simpa only [bandLower, bandUpper, lowCeiling] using bandLaw_support Band.low

instance sourceLowValueLaw_atomless : NullSingletonClass sourceLowValueLaw := by
  apply intervalValueLaw_atomless
  simpa only [bandLower, bandUpper, lowCeiling] using bandLaw_support Band.low

theorem sourceLowValueLaw_positive :
    ∀ᵐ (v : LowBody.LowValue lowCeiling) ∂sourceLowValueLaw, 0 < (v : ℝ) := by
  have hz : sourceLowValueLaw {v : LowBody.LowValue lowCeiling | (v : ℝ) = 0} = 0 := by
    have h : (sourceLowValueLaw.map (fun v : LowBody.LowValue lowCeiling => (v : ℝ)))
        {0} = 0 := by
      rw [sourceLowValueLaw_map_val]
      exact measure_singleton _
    rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton (0 : ℝ))] at h
    exact h
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with v hv
  exact lt_of_le_of_ne v.property.1 (Ne.symm hv)

def sourceActiveValueLaw (r : Partition) :
    Measure (Hybrid.ActiveValue (activeLower r) (activeUpper r)) :=
  intervalValueLaw (activeValueLaw r) (activeLower r) (activeUpper r)
    (by cases r <;> norm_num [activeLower, activeUpper])

instance sourceActiveValueLaw_probability (r : Partition) :
    IsProbabilityMeasure (sourceActiveValueLaw r) := by
  unfold sourceActiveValueLaw
  infer_instance

theorem sourceActiveValueLaw_map_val (r : Partition) :
    (sourceActiveValueLaw r).map
      (fun v : Hybrid.ActiveValue (activeLower r) (activeUpper r) => (v : ℝ)) =
      activeValueLaw r :=
  intervalValueLaw_map_val _ _ _ _ (activeValueLaw_support r)

instance sourceActiveValueLaw_atomless (r : Partition) :
    NullSingletonClass (sourceActiveValueLaw r) :=
  intervalValueLaw_atomless _ _ _ _ (activeValueLaw_support r)

def sourceUpperValueLaw (r : Partition) : Measure (Icc (upperLower r) (2301 / 2000 : ℝ)) :=
  intervalValueLaw (upperValueLaw r) (upperLower r) (2301 / 2000)
    (by cases r <;> norm_num [upperLower])

instance sourceUpperValueLaw_probability (r : Partition) :
    IsProbabilityMeasure (sourceUpperValueLaw r) := by
  unfold sourceUpperValueLaw
  infer_instance

theorem sourceUpperValueLaw_map_val (r : Partition) :
    (sourceUpperValueLaw r).map
      (fun v : Icc (upperLower r) (2301 / 2000 : ℝ) => (v : ℝ)) = upperValueLaw r :=
  intervalValueLaw_map_val _ _ _ _ (upperValueLaw_support r)

instance sourceUpperValueLaw_atomless (r : Partition) :
    NullSingletonClass (sourceUpperValueLaw r) :=
  intervalValueLaw_atomless _ _ _ _ (upperValueLaw_support r)

theorem original_value_law_from_compact_carriers (r : Partition) :
    sourceValueLaw =
      ENNReal.ofReal (3 / 200 : ℝ) •
        sourceLowValueLaw.map (fun v : LowBody.LowValue lowCeiling => (v : ℝ)) +
      ENNReal.ofReal (activeMass r) •
        (sourceActiveValueLaw r).map
          (fun v : Hybrid.ActiveValue (activeLower r) (activeUpper r) => (v : ℝ)) +
      ENNReal.ofReal (upperMass r) •
        (sourceUpperValueLaw r).map
          (fun v : Icc (upperLower r) (2301 / 2000 : ℝ) => (v : ℝ)) := by
  rw [sourceLowValueLaw_map_val, sourceActiveValueLaw_map_val, sourceUpperValueLaw_map_val]
  exact sourceValueLaw_decomposition r

theorem map_fst_physical_joint {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (P : Measure (X × Y)) (f : X → ℝ) (g : Y → A)
    (hf : Measurable f) (hg : Measurable g) :
    (P.map (fun x => (f x.1, g x.2))).map Prod.fst = (P.map Prod.fst).map f := by
  calc
    _ = P.map (Prod.fst ∘ fun x => (f x.1, g x.2)) := by
      simpa only [Function.comp_def] using
        (Measure.map_map measurable_fst ((hf.comp measurable_fst).prodMk (hg.comp measurable_snd)))
    _ = P.map (f ∘ Prod.fst) := rfl
    _ = _ := (Measure.map_map hf measurable_fst).symm

end FCAppendix.Affine.Multiple07
