import FCAppendix.Affine.Tail04.RealIntegralTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.BoundedProbabilityIntegral
open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma measurable_integral (μ : Measure Y) [SFinite μ] (f : X×Y→ℝ)
    (hf : Measurable f) : Measurable (fun x=>∫y,f (x,y) ∂μ) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

lemma integrable (μ : Measure X) [IsFiniteMeasure μ] (f : X→ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀x,|f x|≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x=> by
    simpa only [Real.norm_eq_abs] using hC x)

lemma prod (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X×Y→ℝ) (hf : Measurable f) {C : ℝ} (hC : ∀x,|f x|≤ C) :
    (∫z,f z ∂μ.prod ν)=∫x,∫y,f (x,y) ∂ν ∂μ := integral_prod _ (integrable _ f hf hC)

lemma swap (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X×Y→ℝ) (hf : Measurable f) {C : ℝ} (hC : ∀x,|f x|≤ C) :
    (∫x,∫y,f (x,y) ∂ν ∂μ)=∫y,∫x,f (x,y) ∂μ ∂ν :=
  integral_integral_swap (integrable _ f hf hC)

lemma map (μ : Measure X) [IsFiniteMeasure μ] (g : X→ Y) (hg : Measurable g)
    (f : Y→ℝ) (hf : Measurable f) :
    (∫y,f y ∂μ.map g)=∫x,f (g x) ∂μ := integral_map hg.aemeasurable hf.aestronglyMeasurable

lemma bound (μ : Measure X) [IsProbabilityMeasure μ] (f : X→ℝ) {C : ℝ}
    (hC : ∀x,|f x|≤ C) : |∫x,f x ∂μ|≤ C := by
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=μ) (f:=f) (C:=C)
      (ae_of_all _ fun x=> by simpa only [Real.norm_eq_abs] using hC x)

lemma surplus (μ : Measure X) [IsProbabilityMeasure μ] (p I : X→ℝ)
    (hp : Measurable p) (hI : Measurable I) {B : ℝ} (hpB : ∀x,|p x|≤ B)
    (hI01 : ∀x,I x∈Set.Icc (0:ℝ) 1) (v : ℝ) :
    (∫x,(v-p x)*I x ∂μ)=v*(∫x,I x ∂μ)-(∫x,p x*I x ∂μ) := by
  have hi:=integrable μ I hI (fun x=> by
    rw [abs_of_nonneg (hI01 x).1]
    exact (hI01 x).2)
  have hpi:=integrable μ (fun x=> p x*I x) (hp.mul hI) (fun x=> by
    rw [abs_mul,abs_of_nonneg (hI01 x).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hI01 x).2).trans (hpB x))
  simp_rw [sub_mul]
  rw [integral_sub (hi.const_mul v) hpi,integral_const_mul]

lemma branch (μ : Measure X) [IsProbabilityMeasure μ] (p I : X→ℝ)
    (hp : Measurable p) (hI : Measurable I) {B : ℝ} (hpB : ∀x,|p x|≤ B)
    (hI01 : ∀x,I x∈Set.Icc (0:ℝ) 1) (v w a : ℝ) :
    (∫x,(v-p x)*(w*a+(1-w)*I x) ∂μ)=
      v*(w*a+(1-w)*(∫x,I x ∂μ))-
        (w*a*(∫x,p x ∂μ)+(1-w)*(∫x,p x*I x ∂μ)) := by
  have hpi:=integrable μ (fun x=> p x*I x) (hp.mul hI) (fun x=> by
    rw [abs_mul,abs_of_nonneg (hI01 x).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hI01 x).2).trans (hpB x))
  have hp':=integrable μ p hp hpB
  have hi:=integrable μ I hI (fun x=> by
    rw [abs_of_nonneg (hI01 x).1]
    exact (hI01 x).2)
  have he (x : X) : (v-p x)*(w*a+(1-w)*I x)=
      (v*w*a-w*a*p x)+(1-w)*(v*I x-p x*I x) := by ring
  simp_rw [he]
  change (∫x, ((fun x => v*w*a-w*a*p x) +
    fun x => (1-w)*(v*I x-p x*I x)) x ∂μ)=_
  have hleft : Integrable (fun x => v*w*a-w*a*p x) μ :=
    (integrable_const _).sub (hp'.const_mul _)
  have hright : Integrable (fun x => (1-w)*(v*I x-p x*I x)) μ :=
    ((hi.const_mul v).sub hpi).const_mul _
  have hsplit : (∫x,(v*w*a-w*a*p x)+(1-w)*(v*I x-p x*I x) ∂μ)=
      (∫x,v*w*a-w*a*p x ∂μ)+(∫x,(1-w)*(v*I x-p x*I x) ∂μ) :=
    integral_add hleft hright
  change (∫x,(v*w*a-w*a*p x)+(1-w)*(v*I x-p x*I x) ∂μ)=_
  rw [hsplit]
  have hsub : (∫x,v*w*a-w*a*p x ∂μ)=(∫x,v*w*a ∂μ)-(∫x,w*a*p x ∂μ) :=
    integral_sub (integrable_const _) (hp'.const_mul _)
  have hsub2 : (∫x,v*I x-p x*I x ∂μ)=(∫x,v*I x ∂μ)-(∫x,p x*I x ∂μ) :=
    integral_sub (hi.const_mul v) hpi
  rw [hsub, integral_const, integral_const_mul, integral_const_mul, hsub2, integral_const_mul]
  simp only [probReal_univ,one_smul]
  ring

lemma iterated_three {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure X) (ν : Measure Y) (θ : Measure Z) (κ : Measure W)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure θ] [IsProbabilityMeasure κ]
    (f : X×(Y×(Z×W))→ℝ) (hf : Measurable f) {C : ℝ} (hC : ∀x,|f x|≤ C) :
    Integrable (fun x=>∫y,∫z,∫w,f (x,y,z,w) ∂κ ∂θ ∂ν) μ := by
  have h4 : Measurable (fun z : ((X×Y)×Z)×W => f (z.1.1.1,z.1.1.2,z.1.2,z.2)) :=
    hf.comp (by fun_prop)
  have h3 := measurable_integral κ _ h4
  have h2 := measurable_integral θ _ h3
  have h1 := measurable_integral ν _ h2
  apply integrable μ _ h1
  intro x
  exact bound ν _ (fun y=> bound θ _ (fun z=> bound κ _ (fun w=> hC (x,y,z,w))))

end FCAppendix.Affine.Tail04.BoundedProbabilityIntegral
