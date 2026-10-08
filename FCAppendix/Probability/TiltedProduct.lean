import FCAppendix.Probability.ExponentialTilt
import Mathlib.MeasureTheory.Integral.Pi

namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

def iidSum (X : Ω → ℝ) (N : ℕ) (r : Fin N → Ω) : ℝ := ∑ i, X (r i)

theorem measurable_iidSum {X : Ω → ℝ} (hX : Measurable X) (N : ℕ) :
    Measurable (iidSum X N) :=
  Finset.measurable_sum _ (fun i _ => hX.comp (measurable_pi_apply i))

theorem integral_exp_iidSum (μ : Measure Ω) [SigmaFinite μ] (X : Ω → ℝ) (u : ℝ) (N : ℕ) :
    (∫ r, Real.exp (u*iidSum X N r) ∂Measure.pi (fun _ : Fin N => μ)) =
      (∫ ω, Real.exp (u*X ω) ∂μ)^N := by
  simp only [iidSum,Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_pow (ι := Fin N) (fun ω => Real.exp (u*X ω)),Fintype.card_fin]

theorem cgf_iidSum (μ : Measure Ω) [SigmaFinite μ] (X : Ω → ℝ) (u : ℝ) (N : ℕ) :
    cgf (iidSum X N) (Measure.pi (fun _ : Fin N => μ)) u = (N:ℝ)*cgf X μ u := by
  rw [cgf,mgf,integral_exp_iidSum,Real.log_pow]
  rfl

theorem pi_tilted_eq_tilted_iidSum (μ : Measure Ω) [SigmaFinite μ]
    (X : Ω → ℝ) (u : ℝ) (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ.tilted (fun ω => u*X ω)) =
      (Measure.pi (fun _ : Fin N => μ)).tilted (fun r => u*iidSum X N r) := by
  apply Measure.pi_eq
  intro s hs
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hs),
    integral_exp_iidSum]
  have he (r : Fin N → Ω) :
      Real.exp (u*iidSum X N r)/(∫ ω, Real.exp (u*X ω) ∂μ)^N =
        ∏ i, (Real.exp (u*X (r i))/(∫ ω, Real.exp (u*X ω) ∂μ)) := by
    simp only [iidSum,Finset.mul_sum,Real.exp_sum,Finset.prod_div_distrib,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp_rw [he]
  rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod
    (fun (_ : Fin N) (ω : Ω) => Real.exp (u*X ω)/(∫ ω, Real.exp (u*X ω) ∂μ))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => by positivity))]
  apply Finset.prod_congr rfl
  intro i _
  exact (tilted_apply_eq_ofReal_integral' _ (hs i)).symm

variable (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}

theorem isProbabilityMeasure_unitInterval_tilted (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) (u : ℝ) :
    IsProbabilityMeasure (μ.tilted (fun ω => u*X ω)) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_of_bounded μ hX.aemeasurable hb u)

omit [IsProbabilityMeasure μ] in

theorem unitInterval_tilted (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) (u : ℝ) :
    ∀ᵐ ω ∂μ.tilted (fun ω => u*X ω), X ω ∈ Icc 0 1 :=
  (tilted_absolutelyContinuous μ _) hb

theorem integrable_exp_mul_iidSum (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) (u : ℝ) (N : ℕ) :
    Integrable (fun r => Real.exp (u*iidSum X N r)) (Measure.pi (fun _ : Fin N => μ)) := by
  apply integrable_exp_mul_of_bounded _ (measurable_iidSum hX N).aemeasurable
  exact rowSum_bounded _ (Y := fun (i : Fin N) (r : Fin N → Ω) => X (r i))
    (fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hb)

theorem isProbabilityMeasure_tilted_iidSum (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) (u : ℝ) (N : ℕ) :
    IsProbabilityMeasure ((Measure.pi (fun _ : Fin N => μ)).tilted (fun r => u*iidSum X N r)) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_iidSum μ hX hb u N)

theorem integral_tilted_iidSum (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) (u : ℝ) (N : ℕ) :
    (∫ r, iidSum X N r ∂(Measure.pi (fun _ : Fin N => μ)).tilted (fun r => u*iidSum X N r)) =
      (N:ℝ)*(∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) := by
  let ν := μ.tilted (fun ω => u*X ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_unitInterval_tilted μ hX hb u
  have hi : Integrable X ν := Integrable.of_mem_Icc 0 1 hX.aemeasurable (unitInterval_tilted μ hb u)
  rw [← pi_tilted_eq_tilted_iidSum]
  unfold iidSum
  rw [integral_finsetSum _ (fun i _ => integrable_comp_eval hi)]
  change (∑ i : Fin N, ∫ r, X (r i) ∂Measure.pi (fun _ : Fin N => ν)) = (N:ℝ)*(∫ ω, X ω ∂ν)
  have he (i : Fin N) : (∫ r, X (r i) ∂Measure.pi (fun _ : Fin N => ν)) = ∫ ω, X ω ∂ν :=
    integral_comp_eval (μ := fun _ : Fin N => ν) (i := i) hX.aestronglyMeasurable
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem variance_tilted_iidSum (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) (u : ℝ) (N : ℕ) :
    variance (iidSum X N) ((Measure.pi (fun _ : Fin N => μ)).tilted (fun r => u*iidSum X N r)) =
      (N:ℝ)*variance X (μ.tilted (fun ω => u*X ω)) := by
  let ν := μ.tilted (fun ω => u*X ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_unitInterval_tilted μ hX hb u
  have hlp : MemLp X 2 ν := MemLp.of_bound hX.aestronglyMeasurable 1
    ((unitInterval_tilted μ hb u).mono fun ω hω => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hω.1] using hω.2)
  rw [← pi_tilted_eq_tilted_iidSum]
  unfold iidSum
  have he : (fun r : Fin N → Ω => ∑ i, X (r i)) = ∑ i : Fin N, (fun r => X (r i)) := by
    funext r
    simp only [Finset.sum_apply]
  rw [he,variance_sum_pi (fun _ : Fin N => hlp)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rfl

end FCAppendix.ExponentialTilt
