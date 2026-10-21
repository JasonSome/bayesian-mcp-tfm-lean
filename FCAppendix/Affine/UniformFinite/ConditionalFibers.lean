import FCAppendix.Affine.UniformFinite.NativeFocalSeed
import FCAppendix.Affine.Hybrid.NativeRows

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Literal
open Set MeasureTheory ProbabilityTheory Filter Classical
open scoped BigOperators

theorem integral_eq_of_finite_conditional {X K : Type*} [MeasurableSpace X]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : Measure X) [IsFiniteMeasure μ] (tag : X→ K) (htag : Measurable tag)
    (f g : X→ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hcell : ∀k,μ (tag ⁻¹' {k})≠0→
      (∫x,f x ∂cond μ (tag ⁻¹' {k}))=∫x,g x ∂cond μ (tag ⁻¹' {k})) :
    (∫x,f x ∂μ)=∫x,g x ∂μ := by
  have hrepr (F : X→ℝ) : F=fun x=>∑k,(tag ⁻¹' {k}).indicator F x := by
    funext x
    simp only [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff]
    simp
  have hfi (k : K) : Integrable ((tag ⁻¹' {k}).indicator f) μ :=
    hf.indicator (htag (measurableSet_singleton k))
  have hgi (k : K) : Integrable ((tag ⁻¹' {k}).indicator g) μ :=
    hg.indicator (htag (measurableSet_singleton k))
  conv_lhs => rw [hrepr f]
  conv_rhs => rw [hrepr g]
  rw [integral_finsetSum _ (fun k _=> hfi k),integral_finsetSum _ (fun k _=> hgi k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_indicator (htag (measurableSet_singleton k)),
    integral_indicator (htag (measurableSet_singleton k)),
    ← Hybrid.measure_smul_cond μ (tag ⁻¹' {k}),integral_smul_measure,integral_smul_measure]
  by_cases hz : μ (tag ⁻¹' {k})=0
  · simp only [hz,ENNReal.toReal_zero,zero_smul]
  · rw [hcell k hz]

theorem conditional_product_cell {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (ν : ι→ Measure X) [∀a,IsProbabilityMeasure (ν a)]
    (C : ι→ Set X) (hC : ∀a,MeasurableSet (C a)) :
    cond (Measure.pi ν) (Set.univ.pi C)=Measure.pi (fun a=> cond (ν a) (C a)) := by
  symm
  apply Measure.pi_eq
  intro E hE
  rw [cond_apply (MeasurableSet.univ_pi hC)]
  have he : Set.univ.pi C ∩ Set.univ.pi E=Set.univ.pi (fun a=> C a∩E a) :=
    Set.pi_inter_distrib.symm
  rw [he,Measure.pi_pi,Measure.pi_pi]
  simp_rw [cond_apply (hC _)]
  rw [ENNReal.prod_inv_distrib (by
    intro a _ b _ _
    exact Or.inr (measure_ne_top (ν b) _)),← Finset.prod_mul_distrib]

theorem product_cell_coordinate_nonzero {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (ν : ι→ Measure X) [∀a,IsProbabilityMeasure (ν a)] (C : ι→ Set X)
    (h : (Measure.pi ν) (Set.univ.pi C)≠0) (a : ι) : ν a (C a)≠0 := by
  rw [Measure.pi_pi] at h
  exact (Finset.prod_ne_zero_iff.mp h) a (Finset.mem_univ a)

end FCAppendix.Affine.UniformFinite.Literal
