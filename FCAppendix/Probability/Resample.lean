import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

namespace FCAppendix
namespace Resample

open MeasureTheory
open scoped BigOperators ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]

omit [Fintype ι] in
theorem measurable_update_pair (l : ι) :
    Measurable (fun p : α × (ι → α) => Function.update p.2 l p.1) := by
  rw [measurable_pi_iff]
  intro i
  by_cases h : i = l
  · subst h
    simpa using measurable_fst
  · simpa [Function.update, h, Function.comp_def] using (measurable_pi_apply i).comp measurable_snd

theorem map_update_eq (μ : Measure α) [IsProbabilityMeasure μ] (l : ι) :
    (μ.prod (Measure.pi fun _ : ι => μ)).map (fun p => Function.update p.2 l p.1) =
      Measure.pi fun _ : ι => μ := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_update_pair l) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : α × (ι → α) => Function.update p.2 l p.1) ⁻¹' (Set.univ.pi s) =
      s l ×ˢ Set.univ.pi (Function.update s l Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h l, fun i => ?_⟩
      by_cases hi : i = l
      · subst hi
        simp
      · simpa [Function.update, hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = l
      · subst hi
        simpa using h1
      · simpa [Function.update, hi] using h2 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hprod : ∏ i, μ (Function.update s l Set.univ i) = ∏ i ∈ Finset.univ.erase l, μ (s i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
    simp only [Function.update_self, measure_univ, one_mul]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hprod, ← Finset.mul_prod_erase Finset.univ (fun i => μ (s i)) (Finset.mem_univ l)]

theorem lintegral_resample (μ : Measure α) [IsProbabilityMeasure μ] (l : ι)
    (Φ : α → (ι → α) → ℝ≥0∞) (hΦ : Measurable (Function.uncurry Φ))
    (hinv : ∀ u d u', Φ u (Function.update d l u') = Φ u d) :
    ∫⁻ d, Φ (d l) d ∂(Measure.pi fun _ : ι => μ) =
      ∫⁻ u, ∫⁻ d, Φ u d ∂(Measure.pi fun _ : ι => μ) ∂μ := by
  have hT := measurable_update_pair (α := α) l
  have hcomp : Measurable (fun d : ι → α => Φ (d l) d) := by
    exact hΦ.comp (show Measurable (fun d : ι → α => (d l, d)) from
      (measurable_pi_apply l).prodMk measurable_id)
  conv_lhs => rw [← map_update_eq μ l, lintegral_map hcomp hT]
  have hpt : ∀ p : α × (ι → α),
      Φ ((Function.update p.2 l p.1) l) (Function.update p.2 l p.1) = Φ p.1 p.2 := by
    intro p
    rw [Function.update_self, hinv]
  simp_rw [hpt]
  exact lintegral_prod _ hΦ.aemeasurable

theorem ae_resample (μ : Measure α) [IsProbabilityMeasure μ] (l : ι)
    (P : α → (ι → α) → Prop)
    (hP : MeasurableSet {p : α × (ι → α) | P p.1 p.2})
    (hinv : ∀ u d u', P u (Function.update d l u') ↔ P u d)
    (h : ∀ᵐ u ∂μ, ∀ᵐ d ∂(Measure.pi fun _ : ι => μ), P u d) :
    ∀ᵐ d ∂(Measure.pi fun _ : ι => μ), P (d l) d := by
  have hpair : Measurable (fun d : ι → α => (d l, d)) :=
    (measurable_pi_apply l).prodMk measurable_id
  rw [← map_update_eq μ l]
  apply (ae_map_iff (measurable_update_pair l).aemeasurable (hpair hP)).mpr
  have hp := (Measure.ae_prod_iff_ae_ae hP).mpr h
  filter_upwards [hp] with p hp
  simpa only [Function.update_self, hinv] using hp

end Resample
end FCAppendix
