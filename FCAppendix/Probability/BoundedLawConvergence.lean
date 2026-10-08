import FCAppendix.Probability.ExponentialTilt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace FCAppendix.BoundedLawConvergence
open MeasureTheory ProbabilityTheory Filter Topology Set Real

theorem tendsto_integral_of_unit_support {α : Type*} {l : Filter α}
    {ν : α → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν a : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hweak : Tendsto ν l (𝓝 μ)) {F : ℝ → ℝ} (hF : Continuous F) :
    Tendsto (fun a => ∫ x, F x ∂(ν a : Measure ℝ)) l
      (𝓝 (∫ x, F x ∂(μ : Measure ℝ))) := by
  let clip : C(ℝ, Icc (0 : ℝ) 1) :=
    ⟨fun x => ⟨max 0 (min 1 x), le_max_left _ _,
        max_le (by norm_num) (min_le_left _ _)⟩,
      (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _⟩
  let test : BoundedContinuousFunction ℝ ℝ :=
    (BoundedContinuousFunction.mkOfCompact
      (⟨fun x : Icc (0 : ℝ) 1 => F x, hF.comp continuous_subtype_val⟩ :
        C(Icc (0 : ℝ) 1, ℝ))).compContinuous clip
  have heq : ∀ x ∈ Icc (0 : ℝ) 1, test x = F x := by
    intro x hx
    change F (max 0 (min 1 x)) = F x
    rw [min_eq_right hx.2, max_eq_right hx.1]
  have hi (κ : ProbabilityMeasure ℝ) (hκ : ∀ᵐ x ∂(κ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) :
      (∫ x, test x ∂(κ : Measure ℝ)) = ∫ x, F x ∂(κ : Measure ℝ) :=
    integral_congr_ae (hκ.mono fun x hx => heq x hx)
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) test
  simpa only [hi μ hμ, hi _ (hν _)] using ht

theorem tendsto_mgf {α : Type*} {l : Filter α}
    {ν : α → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν a : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hweak : Tendsto ν l (𝓝 μ)) (u : ℝ) :
    Tendsto (fun a => mgf id (ν a : Measure ℝ) u) l (𝓝 (mgf id (μ : Measure ℝ) u)) :=
  tendsto_integral_of_unit_support hν hμ hweak (by fun_prop)

theorem tendsto_cgf {α : Type*} {l : Filter α}
    {ν : α → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν a : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hweak : Tendsto ν l (𝓝 μ)) (u : ℝ) :
    Tendsto (fun a => cgf id (ν a : Measure ℝ) u) l (𝓝 (cgf id (μ : Measure ℝ) u)) := by
  have hp := mgf_pos (ExponentialTilt.integrable_exp_mul_of_bounded
    (μ : Measure ℝ) measurable_id.aemeasurable hμ u)
  exact (tendsto_mgf hν hμ hweak u).log hp.ne'

theorem tendsto_deriv_cgf {α : Type*} {l : Filter α}
    {ν : α → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν a : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hweak : Tendsto ν l (𝓝 μ)) (u : ℝ) :
    Tendsto (fun a => deriv (cgf id (ν a : Measure ℝ)) u) l
      (𝓝 (deriv (cgf id (μ : Measure ℝ)) u)) := by
  have hi (κ : ProbabilityMeasure ℝ) (hκ : ∀ᵐ x ∂(κ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) :
      u ∈ interior (integrableExpSet id (κ : Measure ℝ)) := by
    rw [ExponentialTilt.integrableExpSet_eq_univ_of_bounded
      (κ : Measure ℝ) measurable_id.aemeasurable hκ, interior_univ]
    trivial
  simp_rw [deriv_cgf (hi _ (hν _)), deriv_cgf (hi _ hμ)]
  exact (tendsto_integral_of_unit_support hν hμ hweak (by fun_prop)).div
    (tendsto_mgf hν hμ hweak u)
    (mgf_pos (ExponentialTilt.integrable_exp_mul_of_bounded
      (μ : Measure ℝ) measurable_id.aemeasurable hμ u)).ne'

theorem tendsto_tilted_mean {α : Type*} {l : Filter α}
    {ν : α → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν a : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hweak : Tendsto ν l (𝓝 μ)) (u : ℝ) :
    Tendsto (fun a => ∫ x, x ∂((ν a : Measure ℝ).tilted (fun x => u * x))) l
      (𝓝 (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x)))) := by
  have hi (κ : ProbabilityMeasure ℝ) (hκ : ∀ᵐ x ∂(κ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) :
      u ∈ interior (integrableExpSet id (κ : Measure ℝ)) := by
    rw [ExponentialTilt.integrableExpSet_eq_univ_of_bounded
      (κ : Measure ℝ) measurable_id.aemeasurable hκ, interior_univ]
    trivial
  change Tendsto (fun a => ∫ x, id x ∂((ν a : Measure ℝ).tilted (fun x => u * id x))) l
    (𝓝 (∫ x, id x ∂((μ : Measure ℝ).tilted (fun x => u * id x))))
  simp_rw [integral_tilted_mul_self (hi _ (hν _)), integral_tilted_mul_self (hi _ hμ)]
  exact tendsto_deriv_cgf hν hμ hweak u

theorem cgf_eq_of_identDistrib {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    (h : IdentDistrib X Y P Q) : cgf X P = cgf Y Q := by
  funext u
  exact congrArg log (mgf_congr_of_identDistrib X Y h u)

theorem tilted_mean_eq_of_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    (h : IdentDistrib X Y P Q) {u : ℝ}
    (hX : u ∈ interior (integrableExpSet X P))
    (hY : u ∈ interior (integrableExpSet Y Q)) :
    (∫ ω, X ω ∂(P.tilted (fun ω => u * X ω))) =
      ∫ ω, Y ω ∂(Q.tilted (fun ω => u * Y ω)) := by
  rw [integral_tilted_mul_self hX, integral_tilted_mul_self hY, cgf_eq_of_identDistrib h]

end FCAppendix.BoundedLawConvergence
