import FCAppendix.Probability.Resample
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Pi

namespace FCAppendix.Resample

open MeasureTheory ProbabilityTheory Filter

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]

theorem integral_resample_bounded
    (μ : Measure α) [IsProbabilityMeasure μ] (l : ι)
    (Φ : α → (ι → α) → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (B : ℝ) (hB : ∀ u d, ‖Φ u d‖ ≤ B)
    (hinv : ∀ u d u', Φ u (Function.update d l u') = Φ u d) :
    (∫ d, Φ (d l) d ∂Measure.pi (fun _ : ι => μ)) =
      ∫ u, ∫ d, Φ u d ∂Measure.pi (fun _ : ι => μ) ∂μ := by
  have hcomp := hΦ.comp ((measurable_pi_apply l).prodMk (measurable_id (α := ι → α)))
  change Measurable (fun d : ι → α => Φ (d l) d) at hcomp
  have hi : Integrable (Function.uncurry Φ) (μ.prod (Measure.pi (fun _ : ι => μ))) :=
    Integrable.of_bound hΦ.aestronglyMeasurable B (Eventually.of_forall fun p => hB p.1 p.2)
  calc
    _ = ∫ p : α × (ι → α),
        Φ ((Function.update p.2 l p.1) l) (Function.update p.2 l p.1)
          ∂μ.prod (Measure.pi (fun _ : ι => μ)) := by
      conv_lhs => rw [← map_update_eq μ l]
      exact integral_map_of_stronglyMeasurable (measurable_update_pair l) hcomp.stronglyMeasurable
    _ = ∫ p : α × (ι → α), Φ p.1 p.2 ∂μ.prod (Measure.pi (fun _ : ι => μ)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by dsimp only; rw [Function.update_self, hinv]
    _ = _ := integral_prod _ hi

theorem integral_mul_coordinate_of_invariant
    (μ : Measure α) [IsProbabilityMeasure μ] (l : ι)
    (f : α → ℝ) (g : (ι → α) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Bf Bg : ℝ) (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ d, ‖g d‖ ≤ Bg)
    (hinv : ∀ d u, g (Function.update d l u) = g d) :
    (∫ d, f (d l) * g d ∂Measure.pi (fun _ : ι => μ)) =
      (∫ u, f u ∂μ) * ∫ d, g d ∂Measure.pi (fun _ : ι => μ) := by
  have hmeas : Measurable (Function.uncurry (fun u d => f u * g d)) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hh := integral_resample_bounded μ l (fun u d => f u * g d) hmeas (Bf * Bg)
    (fun u d => by rw [norm_mul]; exact mul_le_mul (hBf u) (hBg d) (norm_nonneg _) ((norm_nonneg _).trans (hBf u)))
    (fun u d u' => by rw [hinv])
  rw [hh]
  simp_rw [integral_const_mul]
  exact integral_mul_const _ _

theorem integral_mul_coordinate_prod_of_invariant
    {δ : Type*} [MeasurableSpace δ]
    (ν : Measure δ) [IsProbabilityMeasure ν] (μ : Measure α) [IsProbabilityMeasure μ]
    (l : ι) (f : α → ℝ) (g : δ × (ι → α) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Bf Bg : ℝ) (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ d, ‖g d‖ ≤ Bg)
    (hinv : ∀ d s u, g (d, Function.update s l u) = g (d, s)) :
    (∫ z : δ × (ι → α), f (z.2 l) * g z ∂ν.prod (Measure.pi (fun _ : ι => μ))) =
      (∫ u, f u ∂μ) * ∫ z, g z ∂ν.prod (Measure.pi (fun _ : ι => μ)) := by
  have hfg : Measurable (fun z : δ × (ι → α) => f (z.2 l) * g z) :=
    (hf.comp ((measurable_pi_apply l).comp measurable_snd)).mul hg
  have hi : Integrable (fun z : δ × (ι → α) => f (z.2 l) * g z)
      (ν.prod (Measure.pi (fun _ : ι => μ))) := by
    apply Integrable.of_bound hfg.aestronglyMeasurable (Bf * Bg)
    apply Eventually.of_forall
    intro z
    rw [norm_mul]
    exact mul_le_mul (hBf _) (hBg z) (norm_nonneg _) ((norm_nonneg (f (z.2 l))).trans (hBf (z.2 l)))
  have hgi : Integrable g (ν.prod (Measure.pi (fun _ : ι => μ))) :=
    Integrable.of_bound hg.aestronglyMeasurable Bg (Eventually.of_forall hBg)
  rw [integral_prod _ hi, integral_prod _ hgi, ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro d
  exact integral_mul_coordinate_of_invariant μ l f (fun s => g (d, s)) hf
    (hg.comp (measurable_const.prodMk measurable_id)) Bf Bg hBf (fun s => hBg (d, s)) (hinv d)

end FCAppendix.Resample

namespace FCAppendix.ConditionalAveraging

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem integral_observation_prod
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (σ : Measure γ) [IsProbabilityMeasure σ] (T : α → β) (hT : Measurable T)
    (κ : Kernel β α) [IsMarkovKernel κ]
    (hκ : μ.map (fun x => (T x, x)) = ν ⊗ₘ κ)
    (f : (β × α) × γ → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ z, ‖f z‖ ≤ B) :
    (∫ z : α × γ, f ((T z.1, z.1), z.2) ∂μ.prod σ) =
      ∫ y, ∫ z : α × γ, f ((y, z.1), z.2) ∂(κ y).prod σ ∂ν := by
  let H : β × α → ℝ := fun p => ∫ s, f (p, s) ∂σ
  have hH : Measurable H := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hbound : ∀ p, ‖H p‖ ≤ B := by
    intro p
    simpa only [H, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := σ) (Eventually.of_forall fun s => hB (p, s)))
  have hi : Integrable (fun z : α × γ => f ((T z.1, z.1), z.2)) (μ.prod σ) :=
    Integrable.of_bound (hf.comp ((hT.comp measurable_fst).prodMk measurable_fst |>.prodMk measurable_snd)).aestronglyMeasurable
      B (Eventually.of_forall fun z => hB _)
  have hHi : Integrable H (ν ⊗ₘ κ) :=
    Integrable.of_bound hH.aestronglyMeasurable B (Eventually.of_forall hbound)
  calc
    _ = ∫ x, H (T x, x) ∂μ := integral_prod _ hi
    _ = ∫ p, H p ∂(ν ⊗ₘ κ) := by
      rw [← hκ]
      exact (integral_map_of_stronglyMeasurable (hT.prodMk measurable_id) hH.stronglyMeasurable).symm
    _ = ∫ y, ∫ x, H (y, x) ∂κ y ∂ν := MeasureTheory.Measure.integral_compProd hHi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      symm
      apply integral_prod
      have hmeas : Measurable (fun z : α × γ => f ((y, z.1), z.2)) :=
        hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
      exact Integrable.of_bound hmeas.aestronglyMeasurable B (Eventually.of_forall fun z => hB _)

theorem integral_observation_private_seed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (σ : Measure γ) [IsProbabilityMeasure σ] (T : α → β) (hT : Measurable T)
    (κ : Kernel β α) [IsMarkovKernel κ]
    (hκ : μ.map (fun x => (T x, x)) = ν ⊗ₘ κ)
    (l : ι) (f : β × γ → ℝ) (g : (β × α) × (ι → γ) → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (Bf Bg : ℝ) (hBf : ∀ z, ‖f z‖ ≤ Bf) (hBg : ∀ z, ‖g z‖ ≤ Bg)
    (hinv : ∀ y d s u, g ((y, d), Function.update s l u) = g ((y, d), s)) :
    (∫ z : α × (ι → γ), f (T z.1, z.2 l) * g ((T z.1, z.1), z.2)
      ∂μ.prod (Measure.pi (fun _ : ι => σ))) =
    ∫ y, (∫ u, f (y, u) ∂σ) *
      (∫ z : α × (ι → γ), g ((y, z.1), z.2) ∂(κ y).prod (Measure.pi (fun _ : ι => σ))) ∂ν := by
  have hprod : Measurable (fun z : (β × α) × (ι → γ) => f (z.1.1, z.2 l) * g z) :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_pi_apply l).comp measurable_snd))).mul hg
  have hbound : ∀ z : (β × α) × (ι → γ), ‖f (z.1.1, z.2 l) * g z‖ ≤ Bf * Bg := by
    intro z
    rw [norm_mul]
    exact mul_le_mul (hBf (z.1.1, z.2 l)) (hBg z) (norm_nonneg _)
      ((norm_nonneg (f (z.1.1, z.2 l))).trans (hBf (z.1.1, z.2 l)))
  have heq := integral_observation_prod μ ν (Measure.pi (fun _ : ι => σ)) T hT κ hκ
    (fun z : (β × α) × (ι → γ) => f (z.1.1, z.2 l) * g z) hprod (Bf * Bg) hbound
  rw [heq]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  exact Resample.integral_mul_coordinate_prod_of_invariant (κ y) σ l
    (fun u => f (y, u)) (fun z : α × (ι → γ) => g ((y, z.1), z.2))
    (hf.comp (measurable_const.prodMk measurable_id))
    (hg.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    Bf Bg (fun u => hBf (y, u)) (fun z => hBg _) (fun d s u => hinv y d s u)

end FCAppendix.ConditionalAveraging
