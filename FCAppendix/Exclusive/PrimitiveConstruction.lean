import FCAppendix.Exclusive.BroadcastConstruction
import Mathlib.Probability.Distributions.Bernoulli

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Set Filter

theorem nullSingletonClass_map_of_injective
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (mu : Measure X) [NullSingletonClass mu] {f : X → Y}
    (hf : Measurable f) (hinj : Function.Injective f) :
    NullSingletonClass (mu.map f) := by
  constructor
  intro y
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  apply Set.Countable.measure_zero
  apply Set.Subsingleton.countable
  intro x hx z hz
  exact hinj (hx.trans hz.symm)

def intervalLaw (lower width : ℝ) : Measure ℝ :=
  volume.map (fun u : unitInterval => lower+width*(u : ℝ))

theorem measurable_intervalMap (lower width : ℝ) :
    Measurable (fun u : unitInterval => lower+width*(u : ℝ)) :=
  measurable_const.add (measurable_const.mul measurable_subtype_coe)

instance intervalLaw_probability (lower width : ℝ) :
    IsProbabilityMeasure (intervalLaw lower width) :=
  Measure.isProbabilityMeasure_map (measurable_intervalMap lower width).aemeasurable

theorem intervalLaw_atomless (lower : ℝ) {width : ℝ} (hwidth : 0 < width) :
    NullSingletonClass (intervalLaw lower width) := by
  apply nullSingletonClass_map_of_injective volume (measurable_intervalMap lower width)
  intro u v huv
  apply Subtype.ext
  nlinarith

theorem intervalLaw_supported (lower : ℝ) {width : ℝ} (hwidth : 0 < width) :
    ∀ᵐ v ∂intervalLaw lower width, v ∈ Icc lower (lower+width) := by
  apply (ae_map_iff (measurable_intervalMap lower width).aemeasurable measurableSet_Icc).mpr
  exact Eventually.of_forall fun u => ⟨by nlinarith [u.property.1], by nlinarith [u.property.2]⟩

theorem intervalLaw_strict_supported (lower : ℝ) {width : ℝ} (hwidth : 0 < width) :
    ∀ᵐ v ∂intervalLaw lower width, v ∈ Ioo lower (lower+width) := by
  letI := intervalLaw_atomless lower hwidth
  filter_upwards [intervalLaw_supported lower hwidth,
    (intervalLaw lower width).ae_ne lower, (intervalLaw lower width).ae_ne (lower+width)]
    with v hv hlo hhi
  exact ⟨lt_of_le_of_ne hv.1 (Ne.symm hlo), lt_of_le_of_ne hv.2 hhi⟩

def twoBandLaw (h : unitInterval) (high low : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (h : ℝ) • high+ENNReal.ofReal (1-(h : ℝ)) • low

instance twoBandLaw_probability (h : unitInterval) (high low : Measure ℝ)
    [IsProbabilityMeasure high] [IsProbabilityMeasure low] :
    IsProbabilityMeasure (twoBandLaw h high low) := by
  constructor
  simp only [twoBandLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add h.property.1 (sub_nonneg.mpr h.property.2)]
  norm_num

instance twoBandLaw_atomless (h : unitInterval) (high low : Measure ℝ)
    [NullSingletonClass high] [NullSingletonClass low] :
    NullSingletonClass (twoBandLaw h high low) where
  measure_singleton v := by simp [twoBandLaw, Measure.add_apply, Measure.smul_apply]

theorem twoBandLaw_ae (h : unitInterval) (high low : Measure ℝ) (P : ℝ → Prop)
    (hhigh : ∀ᵐ v ∂high, P v) (hlow : ∀ᵐ v ∂low, P v) :
    ∀ᵐ v ∂twoBandLaw h high low, P v := by
  apply (ae_add_measure_iff).mpr
  exact ⟨Measure.ae_smul_measure hhigh _, Measure.ae_smul_measure hlow _⟩

theorem twoBandLaw_high_mass (h : unitInterval) (high low : Measure ℝ)
    [IsProbabilityMeasure high] [IsProbabilityMeasure low]
    (E : Set ℝ) (hE : MeasurableSet E)
    (hhigh : ∀ᵐ v ∂high, v ∈ E) (hlow : ∀ᵐ v ∂low, v ∉ E) :
    (twoBandLaw h high low).real E = (h : ℝ) := by
  have hH : high E = 1 := (mem_ae_iff_prob_eq_one hE).mp hhigh
  have hL : low E = 0 := by simpa only [ae_iff, not_not, setOf_mem_eq] using hlow
  simp [Measure.real, twoBandLaw, Measure.add_apply, Measure.smul_apply, hH, hL,
    ENNReal.toReal_ofReal h.property.1]

theorem scarce_primitive_law
    (h : unitInterval) (high : Measure ℝ) [IsProbabilityMeasure high]
    [NullSingletonClass high] (g : ℝ) {L highLo highHi : ℝ}
    (hL : 0 < L) (hseparate : g+L < highLo)
    (hhigh : ∀ᵐ v ∂high, v ∈ Icc highLo highHi) :
    let F := twoBandLaw h high (intervalLaw g L)
    IsProbabilityMeasure F ∧ NullSingletonClass F ∧
      F.real (Icc highLo highHi) = (h : ℝ) ∧
      F.real (Ioi g) = 1 ∧
      (∀ᵐ v ∂F, v ∈ Icc highLo highHi ∨ v ∈ Ioo g (g+L)) := by
  dsimp only
  letI := intervalLaw_atomless g hL
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · apply twoBandLaw_high_mass h high (intervalLaw g L) _ measurableSet_Icc hhigh
    filter_upwards [intervalLaw_supported g hL] with v hv he
    linarith [he.1, hv.2]
  · have ha : ∀ᵐ v ∂twoBandLaw h high (intervalLaw g L), v ∈ Ioi g := by
      apply twoBandLaw_ae
      · filter_upwards [hhigh] with v hv
        exact lt_of_lt_of_le (by linarith) hv.1
      · exact (intervalLaw_strict_supported g hL).mono fun _ hv => hv.1
    have hm := (mem_ae_iff_prob_eq_one measurableSet_Ioi).mp ha
    simp only [Measure.real, hm, ENNReal.toReal_one]
  · apply twoBandLaw_ae
    · exact hhigh.mono fun _ hv => Or.inl hv
    · exact (intervalLaw_strict_supported g hL).mono fun _ hv => Or.inr hv

def scaledHighLaw {eps : ℝ} (H : ℝ)
    (nu : Measure (Icc (1-eps) (1+eps))) : Measure ℝ :=
  nu.map (fun v : Icc (1-eps) (1+eps) => H*(v : ℝ))

theorem measurable_highScale (eps H : ℝ) :
    Measurable (fun v : Icc (1-eps) (1+eps) => H*(v : ℝ)) :=
  measurable_const.mul measurable_subtype_coe

instance scaledHighLaw_probability {eps : ℝ} (H : ℝ)
    (nu : Measure (Icc (1-eps) (1+eps))) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (scaledHighLaw H nu) :=
  Measure.isProbabilityMeasure_map (measurable_highScale eps H).aemeasurable

theorem scaledHighLaw_atomless {eps : ℝ} {H : ℝ} (hH : 0 < H)
    (nu : Measure (Icc (1-eps) (1+eps))) [NullSingletonClass nu] :
    NullSingletonClass (scaledHighLaw H nu) := by
  apply nullSingletonClass_map_of_injective nu (measurable_highScale eps H)
  intro u v huv
  apply Subtype.ext
  exact (mul_left_cancel₀ hH.ne') huv

theorem scaledHighLaw_supported {eps H : ℝ} (hH : 0 < H)
    (nu : Measure (Icc (1-eps) (1+eps))) :
    ∀ᵐ v ∂scaledHighLaw H nu, v ∈ Icc (H*(1-eps)) (H*(1+eps)) := by
  apply (ae_map_iff (measurable_highScale eps H).aemeasurable measurableSet_Icc).mpr
  exact Eventually.of_forall fun v =>
    ⟨mul_le_mul_of_nonneg_left v.property.1 hH.le,
      mul_le_mul_of_nonneg_left v.property.2 hH.le⟩

theorem twoBandLaw_map (h : unitInterval) (high low : Measure ℝ)
    {X : Type*} [MeasurableSpace X] {f : ℝ → X} (hf : Measurable f) :
    (twoBandLaw h high low).map f =
      ENNReal.ofReal (h : ℝ) • high.map f+
        ENNReal.ofReal (1-(h : ℝ)) • low.map f := by
  rw [twoBandLaw, Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul]

end FCAppendix.Bayes.ExclusiveConstruction
