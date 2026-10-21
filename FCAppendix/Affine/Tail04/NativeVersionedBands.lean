import FCAppendix.Affine.Tail04.NativeVersionedCounts

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

lemma low_shape (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    ∀ᵐ x ∂((data s hs V k hk).PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ s.scalar.U ∧ x.2.routeCount = 2 := by
  have hfull : ∀ᵐ v ∂s.valueMeasure,v ∈ V.valueSet := by
    rw [← NativeSource.input_original_values s hs]
    exact V.full_valueSet
  apply Measure.ae_compProd_of_ae_ae
    ((measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))
  have hv : ∀ᵐ v ∂P.originalLowLaw.map Subtype.val,v ≤ P.d0 := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Iic).mpr
    exact Eventually.of_forall (fun v => v.2.2)
  filter_upwards [(low_ac s).ae_le hfull,hv] with v hV hv
  exact (V.common_bands v hV k).mono (fun a ha =>
    ⟨(ha.1 hv).1.trans (NativeSource.input s hs).d_lt_L.le |>.trans
      (NativeSource.input s hs).L_lt_U.le,(ha.1 hv).2⟩)

lemma active_shape (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    ∀ᵐ x ∂((data s hs V k hk).PA : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ s.scalar.U ∧ x.2.routeCount = 2 := by
  have hfull : ∀ᵐ v ∂s.valueMeasure,v ∈ V.valueSet := by
    rw [← NativeSource.input_original_values s hs]
    exact V.full_valueSet
  apply Measure.ae_compProd_of_ae_ae
    ((measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))
  have hv : ∀ᵐ v ∂P.originalPartialLaw.map Subtype.val,v ∈ P.partialValues := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
    exact Eventually.of_forall (fun v => v.2)
  filter_upwards [(active_ac s).ae_le hfull,hv] with v hV hv
  exact (V.common_bands v hV k).mono (fun a ha => ⟨(ha.2.1 hv).1.2,(ha.2.1 hv).2⟩)

lemma row_bid_atomless (mu : ProbabilityMeasure ℝ) (hmu : (mu : Measure ℝ) ≪ s.valueMeasure)
    (k : ℕ) (y : ℝ) :
    (row mu (V.toNativeFamilyData.game k).σ : Measure (ℝ × JointAction 2))
      {x | x.2.bid = y} = 0 := by
  have hac : (mu : Measure ℝ) ≪ (V.toNativeFamilyData.game k).F := by
    rw [V.toNativeFamilyData.original_F k,NativeSource.input_original_values s hs]
    exact hmu
  apply hac.compProd_left (V.toNativeFamilyData.game k).σ
  haveI := V.toNativeFamilyData.bid_atomless k
  have hz : (((V.toNativeFamilyData.game k).F ⊗ₘ
    (V.toNativeFamilyData.game k).σ).map (fun x => x.2.bid)) {y} = 0 := measure_singleton y
  rw [Measure.map_apply (show Measurable (fun x : ℝ × JointAction 2 => x.2.bid) from
    (measurable_bid 2).comp measurable_snd)
    (measurableSet_singleton y)] at hz
  exact hz

end FCAppendix.Affine.Tail04.NativeVersionedSource
