import FCAppendix.Affine.Tail04.BoundedProbabilityIntegral

noncomputable section
namespace FCAppendix.Affine.Tail04.FinitePayoffLinearity
open MeasureTheory Set
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

lemma row_mix (f g : X→ℝ) (w z : ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫x,w*f x+z*g x ∂μ)=w*(∫x,f x ∂μ)+z*(∫x,g x ∂μ) := by
  rw [integral_add (hf.const_mul w) (hg.const_mul z),integral_const_mul,integral_const_mul]

lemma test_mix (a f g : X→ℝ) (w z : ℝ)
    (hf : Integrable (fun x=> a x*f x) μ) (hg : Integrable (fun x=> a x*g x) μ) :
    (∫x,a x*(w*f x+z*g x) ∂μ)=
      w*(∫x,a x*f x ∂μ)+z*(∫x,a x*g x ∂μ) := by
  have he (x : X) : a x*(w*f x+z*g x)=w*(a x*f x)+z*(a x*g x) := by ring
  simp_rw [he]
  exact row_mix μ _ _ w z hf hg

lemma test_sum {I : Type*} [Fintype I] (a : X→ℝ) (w : I→ℝ) (f : I→ X→ℝ)
    (hf : ∀i,Integrable (fun x=> a x*f i x) μ) :
    (∫x,a x*(∑i,w i*f i x) ∂μ)=∑i,w i*(∫x,a x*f i x ∂μ) := by
  simp_rw [Finset.mul_sum]
  have he (i : I) (x : X) : a x*(w i*f i x)=w i*(a x*f i x) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _=>(hf i).const_mul (w i))]
  simp only [integral_const_mul]

lemma continuous_integrable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [CompactSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (f : Y→ℝ) (hf : Continuous f) : Integrable f ν := by
  let F : C(Y,ℝ):=⟨f,hf⟩
  exact BoundedProbabilityIntegral.integrable ν f hf.measurable
    (fun y => show |F y| ≤ ‖F‖ from by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm y)

end FCAppendix.Affine.Tail04.FinitePayoffLinearity
