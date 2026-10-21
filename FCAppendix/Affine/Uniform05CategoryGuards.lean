import FCAppendix.Affine.Uniform05LawGuards

noncomputable section
namespace FCAppendix.Affine.Uniform05
open Set MeasureTheory ProbabilityTheory

namespace RestrictedLaw
variable {i : Row}

lemma value_closed_interval_mass (G : RestrictedLaw i) {b : ℝ}
    (_hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (G.1 : Measure (ℝ × Bid i)) {p | 0 ≤ p.1 ∧ p.1 ≤ b*t i} =
      ENNReal.ofReal b := by
  have ht := t_pos i
  have hsub : Icc (0 : ℝ) (b*t i) ⊆ Icc (0 : ℝ) (t i) := by
    intro v hv
    exact ⟨hv.1, hv.2.trans (by nlinarith)⟩
  change (G.1 : Measure (ℝ × Bid i)) (Prod.fst ⁻¹' Icc (0 : ℝ) (b*t i)) = _
  rw [← Measure.map_apply measurable_fst measurableSet_Icc,G.2.1]
  simp only [lowerValueMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_Icc,inter_eq_left.mpr hsub,Real.volume_Icc,
    sub_zero]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp [ht.ne']

theorem seed_mass_lower (G : RestrictedLaw i) :
    ENNReal.ofReal ((1 : ℝ)/2) ≤
      (G.bidLaw : Measure (Bid i)) {b | (b : ℝ) ≤ (1 : ℝ)/2*t i} := by
  rw [bidLaw_coe,Measure.map_apply measurable_snd
    (measurableSet_le measurable_subtype_coe measurable_const)]
  have hinc : ∀ᵐ p ∂(G.1 : Measure (ℝ × Bid i)),
      p ∈ {p | 0 ≤ p.1 ∧ p.1 ≤ (1 : ℝ)/2*t i} →
      p ∈ Prod.snd ⁻¹' {b : Bid i | (b : ℝ) ≤ (1 : ℝ)/2*t i} := by
    filter_upwards [G.2.2] with p hp
    intro hv
    exact hp.2.2.trans hv.2
  have hh := measure_mono_ae hinc
  change (G.1 : Measure (ℝ × Bid i)) {p | 0 ≤ p.1 ∧ p.1 ≤ (1 : ℝ)/2*t i} ≤
    (G.1 : Measure (ℝ × Bid i)) (Prod.snd ⁻¹' {b : Bid i | (b : ℝ) ≤ (1 : ℝ)/2*t i}) at hh
  rw [value_closed_interval_mass G (by norm_num) (by norm_num)] at hh
  exact hh

theorem low_category_mass_upper (G : RestrictedLaw i) :
    (G.bidLaw : Measure (Bid i)) {b | (b : ℝ) ≤ kappa i*cap i} ≤
      ENNReal.ofReal (x i+1/200) := by
  rw [bidLaw_coe,Measure.map_apply measurable_snd
    (measurableSet_le measurable_subtype_coe measurable_const)]
  have hinc : ∀ᵐ p ∂(G.1 : Measure (ℝ × Bid i)),
      p ∈ Prod.snd ⁻¹' {b : Bid i | (b : ℝ) ≤ kappa i*cap i} →
      p ∈ {p | 0 ≤ p.1 ∧ p.1 ≤ (x i+1/200)*t i} := by
    filter_upwards [G.2.2] with p hp
    intro hb
    have hv := low_category_imp_value_le i (t_pos i) (zc_receipt_guard i)
      hp.2.1 hb
    exact ⟨hp.1.1,by dsimp [zc, lambda] at hv; nlinarith⟩
  have hh := measure_mono_ae hinc
  change (G.1 : Measure (ℝ × Bid i)) (Prod.snd ⁻¹' {b : Bid i | (b : ℝ) ≤ kappa i*cap i}) ≤
    (G.1 : Measure (ℝ × Bid i)) {p | 0 ≤ p.1 ∧ p.1 ≤ (x i+1/200)*t i} at hh
  rw [value_closed_interval_mass G
    (by cases i <;> norm_num [x]) (by cases i <;> norm_num [x])] at hh
  exact hh

theorem unconditional_seed_mass_lower (G : RestrictedLaw i) :
    ENNReal.ofReal ((1 : ℝ)/2*t i) ≤ ENNReal.ofReal (t i)*
      (G.bidLaw : Measure (Bid i)) {b | (b : ℝ) ≤ (1 : ℝ)/2*t i} := by
  have hh := mul_le_mul_right G.seed_mass_lower (ENNReal.ofReal (t i))
  rw [← ENNReal.ofReal_mul (t_pos i).le] at hh
  simpa only [mul_comm (t i) ((1 : ℝ)/2)] using hh

theorem unconditional_low_category_mass_upper (G : RestrictedLaw i) :
    ENNReal.ofReal (t i)*
      (G.bidLaw : Measure (Bid i)) {b | (b : ℝ) ≤ kappa i*cap i} ≤
      ENNReal.ofReal (zc i) := by
  have hh := mul_le_mul_right G.low_category_mass_upper (ENNReal.ofReal (t i))
  rw [← ENNReal.ofReal_mul (t_pos i).le] at hh
  convert! hh using 1
  congr 1
  unfold zc lambda
  ring

theorem seed_guard_statistics_zero (G : RestrictedLaw i) {b : ℝ}
    (hb : b ≤ (1 : ℝ)/2*t i) :
    lawWeight i G b = 0 ∧
    exposure (xi i) (G.multiplier-guardRadius i) b = 0 ∧
    rejectionExposure (rejectionScale i) G.rejectionRoot b = 0 := by
  have ht := t_pos i
  have hroot := G.multiplier_guards.1
  have hr := G.rejectionRoot_guards.1
  have hshift := shifted_multiplier_guards i G
  have hshift' : (52 : ℝ)/100*t i < G.multiplier-guardRadius i :=
    (le_max_right _ _).trans_lt hshift
  have hbroot : b ≤ G.multiplier := by nlinarith
  refine ⟨?_,exposure_zero (by nlinarith),rejectionExposure_zero (by nlinarith)⟩
  unfold lawWeight
  rw [exposure_zero hbroot]
  exact guardWeight_zero (requiredDemand_range i).1 (by linarith [(requiredDemand_range i).1])

end RestrictedLaw
end FCAppendix.Affine.Uniform05
