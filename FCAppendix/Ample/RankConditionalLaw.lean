import FCAppendix.Ample.RankMeasureBasics
import Mathlib.Probability.ConditionalProbability

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ENNReal
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem rank_activeDrawLaw_probability (Γ : FiniteGame m n c Seed)
    (hh : 0 < Γ.F.real (Ioi Γ.g)) : IsProbabilityMeasure (activeDrawLaw Γ) := by
  let E : Set (ℝ × JointAction n) := {x | Γ.g < x.1}
  have he : (Γ.F ⊗ₘ Γ.σ) E = Γ.F (Ioi Γ.g) := by
    apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
    exact joint_value_probability Γ (Ioi Γ.g) measurableSet_Ioi
  have hne : (Γ.F ⊗ₘ Γ.σ) E ≠ 0 := by
    intro hz
    have hzero : Γ.F.real (Ioi Γ.g) = 0 := by
      rw [Measure.real, ← he, hz, ENNReal.toReal_zero]
    exact hh.ne' hzero
  have hp := cond_isProbabilityMeasure_of_finite hne (measure_ne_top _ _)
  simpa only [ProbabilityTheory.cond, he, activeDrawLaw, E] using hp

theorem rank_activeDrawLaw_ae_of_joint (Γ : FiniteGame m n c Seed)
    {P : ℝ × JointAction n → Prop} (hP : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), P x) :
    ∀ᵐ x ∂activeDrawLaw Γ, P x := by
  have hr := ae_restrict_of_ae (s := {x | Γ.g < x.1}) hP
  rw [ae_iff] at hr ⊢
  simp only [activeDrawLaw, Measure.smul_apply, smul_eq_mul, hr, mul_zero]

theorem rank_activeDrawLaw_positive (Γ : FiniteGame m n c Seed) :
    ∀ᵐ x ∂activeDrawLaw Γ, Γ.g < x.1 := by
  have hr := ae_restrict_mem (μ := Γ.F ⊗ₘ Γ.σ) (s := {x | Γ.g < x.1})
    (measurableSet_lt measurable_const measurable_fst)
  rw [ae_iff] at hr ⊢
  simp only [Set.mem_setOf_eq] at hr
  simp only [activeDrawLaw, Measure.smul_apply, smul_eq_mul, hr, mul_zero]

theorem rank_activeDrawLaw_real_apply (Γ : FiniteGame m n c Seed)
    (E : Set (ℝ × JointAction n)) :
    (activeDrawLaw Γ).real E =
      (Γ.F ⊗ₘ Γ.σ).real (E ∩ {x | Γ.g < x.1}) / Γ.F.real (Ioi Γ.g) := by
  rw [activeDrawLaw, measureReal_ennreal_smul_apply, ENNReal.toReal_inv,
    measureReal_restrict_apply' (measurableSet_lt measurable_const measurable_fst)]
  simp only [Measure.real, div_eq_mul_inv, mul_comm]

theorem rank_conditional_exception_bound (Γ : FiniteGame m n c Seed)
    (hh : 0 < Γ.F.real (Ioi Γ.g)) {Bad E : Set (ℝ × JointAction n)}
    (hsub : Bad ≤ᵐ[activeDrawLaw Γ] E) {η : ℝ} (hη : 0 < η)
    (hmass : (Γ.F ⊗ₘ Γ.σ).real E < Γ.F.real (Ioi Γ.g)*η) :
    activeDrawLaw Γ Bad < ENNReal.ofReal η := by
  letI := rank_activeDrawLaw_probability Γ hh
  have hreal : (activeDrawLaw Γ).real E < η := by
    rw [rank_activeDrawLaw_real_apply]
    apply (div_lt_iff₀ hh).mpr
    exact (measureReal_mono inter_subset_left).trans_lt (by simpa only [mul_comm] using hmass)
  have hENN : activeDrawLaw Γ E < ENNReal.ofReal η := by
    rw [← ofReal_measureReal (μ := activeDrawLaw Γ) (s := E)]
    exact (ENNReal.ofReal_lt_ofReal_iff hη).mpr hreal
  exact (measure_mono_ae hsub).trans_lt hENN

end FCAppendix.Bayes
