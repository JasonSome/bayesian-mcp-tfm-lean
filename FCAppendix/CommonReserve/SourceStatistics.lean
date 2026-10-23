import FCAppendix.CommonReserve.TieSymmetry

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ProbabilityTheory

variable {m n : ℕ} {D Seed : Type*} [MeasurableSpace D] [MeasurableSpace Seed]

theorem integral_coordinate_seed (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (j : Fin n)
    (f : D × Seed → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ p, ‖f p‖ ≤ B) :
    (∫ ω : D × (Fin n → Seed), f (ω.1, ω.2 j)
      ∂μ.prod (Measure.pi fun _ : Fin n => ν)) =
      ∫ d, ∫ s, f (d, s) ∂ν ∂μ := by
  have hpres := (MeasurePreserving.id μ).prod
    (measurePreserving_eval (fun _ : Fin n => ν) j)
  have hi : Integrable f (μ.prod ν) :=
    Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)
  calc
    _ = ∫ p, f p ∂(μ.prod (Measure.pi fun _ : Fin n => ν)).map
        (fun ω : D × (Fin n → Seed) => (ω.1, ω.2 j)) :=
      (integral_map_of_stronglyMeasurable hpres.measurable hf.stronglyMeasurable).symm
    _ = ∫ p, f p ∂μ.prod ν := by
      have hmap : (μ.prod (Measure.pi fun _ : Fin n => ν)).map
          (fun ω : D × (Fin n → Seed) => (ω.1, ω.2 j)) = μ.prod ν := hpres.map_eq
      rw [hmap]
    _ = _ := integral_prod _ hi

lemma measurable_weighted_membership
    (S : D → Finset (Fin m)) (hS : Measurable S) (w : D → ℝ)
    (hw : Measurable w) (i : Fin m) :
    Measurable (fun d => if i ∈ S d then w d else 0) := by
  classical
  exact Measurable.ite
    (hS (MeasurableSet.of_discrete : MeasurableSet {T : Finset (Fin m) | i ∈ T}))
    hw measurable_const

lemma integrable_weighted_membership (μ : Measure D) [IsProbabilityMeasure μ]
    (S : D → Finset (Fin m)) (hS : Measurable S) (w : D → ℝ)
    (hw : Measurable w) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ d, ‖w d‖ ≤ B)
    (i : Fin m) : Integrable (fun d => if i ∈ S d then w d else 0) μ := by
  classical
  apply Integrable.of_bound (measurable_weighted_membership S hS w hw i).aestronglyMeasurable B
  exact Eventually.of_forall fun d => by split <;> simp_all

lemma integrable_localPositiveStatistic
    {X : Type*} [MeasurableSpace X] {c : ℕ}
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (entry : X → Option ℝ) (hentry : Measurable entry)
    (weight : X → ℝ) (hweight : Measurable weight) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖weight x‖ ≤ B) (i : Fin m) :
    Integrable (fun d => localPositiveStatistic ν policy entry weight d i)
      (Measure.pi fun _ : Fin m => μ) := by
  classical
  apply Integrable.of_bound
    (measurable_localPositiveStatistic ν policy hp entry hentry weight hweight i).aestronglyMeasurable B
  apply Eventually.of_forall
  intro d
  apply (norm_integral_le_integral_norm _).trans
  have hi : Integrable (fun s => if i ∈ positiveSelection (fun l => entry (d l))
      (policy (fun l => entry (d l)) s).val then weight (d i) else 0) ν := by
    apply integrable_weighted_membership ν _
      ((measurable_positiveSelection_policy policy hp).comp
        (measurable_const.prodMk measurable_id)) _ measurable_const B hB0
      (fun _ => hB _) i
  have hh := integral_mono hi.norm (integrable_const B)
    (fun s => show ‖(if i ∈ positiveSelection (fun l => entry (d l))
      (policy (fun l => entry (d l)) s).val then weight (d i) else 0)‖ ≤ B by
        split <;> simp_all)
  simpa using hh

end FCAppendix.CommonReserve
