import FCAppendix.Exclusive.PrimitiveConstruction

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Set Filter

theorem intervalLaw_Iic (g : ℝ) {L q : ℝ} (hL : 0 < L) (hq : q ∈ Icc (0:ℝ) 1) :
    intervalLaw g L (Iic (g+L*q)) = ENNReal.ofReal q := by
  rw [intervalLaw, Measure.map_apply (measurable_intervalMap g L) measurableSet_Iic]
  have he : (fun u : unitInterval => g+L*(u : ℝ)) ⁻¹' Iic (g+L*q) =
      Iic (⟨q,hq⟩ : unitInterval) := by
    ext u
    change g+L*(u : ℝ) ≤ g+L*q ↔ (u : ℝ) ≤ q
    constructor <;> intro hh <;> nlinarith
  rw [he,unitInterval.volume_Iic]

theorem scarce_efficient_cutoff
    (h : unitInterval) (high : Measure ℝ) [IsProbabilityMeasure high]
    (g : ℝ) {L highLo beta : ℝ} (hL : 0 < L) (hseparate : g+L < highLo)
    (hhigh : ∀ᵐ v ∂high, highLo ≤ v)
    (hhbeta : (h : ℝ) < beta) (hbeta : beta < 1) :
    let vStar := g+L*(1-beta)/(1-(h : ℝ))
    vStar ∈ Ioo g (g+L) ∧
      (twoBandLaw h high (intervalLaw g L)).real (Iic vStar) = 1-beta ∧
      (twoBandLaw h high (intervalLaw g L)).real (Ioi vStar) = beta := by
  have hh1 : (h : ℝ) < 1 := hhbeta.trans hbeta
  have hden : 0 < 1-(h : ℝ) := sub_pos.mpr hh1
  let q := (1-beta)/(1-(h : ℝ))
  have hq0 : 0 < q := div_pos (sub_pos.mpr hbeta) hden
  have hq1 : q < 1 := (div_lt_one hden).mpr (by linarith)
  have he : g+L*(1-beta)/(1-(h : ℝ)) = g+L*q := by dsimp [q]; ring
  dsimp only
  rw [he]
  have hvin : g+L*q ∈ Ioo g (g+L) := by
    constructor <;> nlinarith [mul_pos hL hq0,mul_pos hL (sub_pos.mpr hq1)]
  have hH : high (Iic (g+L*q)) = 0 := by
    apply measure_mono_null (show Iic (g+L*q) ⊆ {v | highLo ≤ v}ᶜ from ?_)
      (ae_iff.mp hhigh)
    intro v hv hpos
    change v ≤ g+L*q at hv
    change highLo ≤ v at hpos
    linarith [hvin.2]
  have hF : (twoBandLaw h high (intervalLaw g L)).real (Iic (g+L*q)) = 1-beta := by
    rw [Measure.real,twoBandLaw,Measure.add_apply,Measure.smul_apply,
      Measure.smul_apply,hH,intervalLaw_Iic g hL ⟨hq0.le,hq1.le⟩]
    simp only [smul_eq_mul,mul_zero,zero_add,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr h.property.2),ENNReal.toReal_ofReal hq0.le]
    dsimp [q]
    field_simp [hden.ne']
  refine ⟨hvin,hF,?_⟩
  have hc := probReal_compl_eq_one_sub (μ := twoBandLaw h high (intervalLaw g L))
    (s := Iic (g+L*q))
    measurableSet_Iic
  rw [compl_Iic] at hc
  rw [hc,hF]
  ring

def normalizedUniformMap (eps : ℝ) (heps : 0 ≤ eps) (u : unitInterval) :
    Icc (1-eps) (1+eps) :=
  ⟨1-eps+2*eps*(u : ℝ),by
    constructor <;> nlinarith [mul_nonneg heps u.property.1,
      mul_nonneg heps (sub_nonneg.mpr u.property.2)]⟩

theorem continuous_normalizedUniformMap (eps : ℝ) (heps : 0 ≤ eps) :
    Continuous (normalizedUniformMap eps heps) := by
  apply Continuous.subtype_mk
  exact continuous_const.add (continuous_const.mul continuous_subtype_val)

def normalizedUniformLaw (eps : ℝ) (heps : 0 ≤ eps) : Measure (Icc (1-eps) (1+eps)) :=
  volume.map (normalizedUniformMap eps heps)

instance normalizedUniformLaw_probability (eps : ℝ) (heps : 0 ≤ eps) :
    IsProbabilityMeasure (normalizedUniformLaw eps heps) :=
  Measure.isProbabilityMeasure_map (continuous_normalizedUniformMap eps heps).measurable.aemeasurable

theorem normalizedUniformLaw_atomless {eps : ℝ} (heps : 0 < eps) :
    NullSingletonClass (normalizedUniformLaw eps heps.le) := by
  apply nullSingletonClass_map_of_injective volume
    (continuous_normalizedUniformMap eps heps.le).measurable
  intro u v huv
  apply Subtype.ext
  have he := congrArg Subtype.val huv
  change 1-eps+2*eps*(u : ℝ) = 1-eps+2*eps*(v : ℝ) at he
  nlinarith

end FCAppendix.Bayes.ExclusiveConstruction
