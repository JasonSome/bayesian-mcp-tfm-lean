import FCAppendix.Proposer.MeasurableLotteryPolicy
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory
variable {X Ω : Type*} [MeasurableSpace X] [Fintype Ω] [Nonempty Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [StandardBorelSpace Ω]

private def supportScan (μ : FiniteLaw Ω) (fallback : Ω) : List Ω → Ω
  | [] => fallback
  | ω :: rest => if 0 < μ.mass ω then ω else supportScan μ fallback rest

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [StandardBorelSpace Ω] in
private lemma supportScan_pos (μ : FiniteLaw Ω) (fallback : Ω) (xs : List Ω)
    (hex : ∃ ω ∈ xs, 0 < μ.mass ω) : 0 < μ.mass (supportScan μ fallback xs) := by
  induction xs with
  | nil => simp at hex
  | cons ω rest ih =>
    by_cases hω : 0 < μ.mass ω
    · simpa only [supportScan, if_pos hω] using hω
    · simp only [supportScan, if_neg hω]
      apply ih
      rcases hex with ⟨v, hv, hp⟩
      rcases List.mem_cons.mp hv with he | hr
      · subst v
        exact False.elim (hω hp)
      · exact ⟨v, hr, hp⟩

omit [Nonempty Ω] [MeasurableSingletonClass Ω] [StandardBorelSpace Ω] in
private lemma measurable_supportScan (μ : X → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω))
    (fallback : Ω) (xs : List Ω) :
    Measurable (fun x => supportScan (μ x) fallback xs) := by
  induction xs with
  | nil => exact measurable_const
  | cons ω rest ih =>
    exact Measurable.ite (measurableSet_lt measurable_const (hμ ω)) measurable_const ih

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [StandardBorelSpace Ω] in
private lemma exists_positive_mass (μ : FiniteLaw Ω) : ∃ ω, 0 < μ.mass ω := by
  by_contra hn
  push Not at hn
  have hz : ∀ ω, μ.mass ω = 0 := fun ω => le_antisymm (hn ω) (μ.nonneg ω)
  have ht := μ.total
  simp only [hz, Finset.sum_const_zero] at ht
  norm_num at ht

theorem exists_support_sampler (μ : X → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) :
    ∃ f : X → unitInterval → Ω,
      Measurable (Function.uncurry f) ∧
      (∀ x u, 0 < (μ x).mass (f x u)) ∧
      ∀ x, volume.map (f x) = FiniteLaw.probabilityMeasure (μ x) := by
  classical
  obtain ⟨raw, hraw, hlaw⟩ := FiniteLaw.exists_measurable_sampler μ hμ
  let fallback : Ω := Classical.choice ‹Nonempty Ω›
  let repair : X → Ω := fun x => supportScan (μ x) fallback Finset.univ.toList
  have hrepair : Measurable repair := measurable_supportScan μ hμ fallback _
  have hrepairpos (x : X) : 0 < (μ x).mass (repair x) := by
    apply supportScan_pos
    obtain ⟨ω,hω⟩ := exists_positive_mass (μ x)
    exact ⟨ω, by simp, hω⟩
  have hmass : Measurable (fun y : X × unitInterval => (μ y.1).mass (raw y.1 y.2)) := by
    have he : (fun y : X × unitInterval => (μ y.1).mass (raw y.1 y.2)) =
        fun y => ∑ ω, if raw y.1 y.2 = ω then (μ y.1).mass ω else 0 := by
      funext y
      simp
    rw [he]
    exact Finset.measurable_sum _ (fun ω _ =>
      Measurable.ite (measurableSet_eq_fun hraw measurable_const)
        ((hμ ω).comp measurable_fst) measurable_const)
  let f : X → unitInterval → Ω := fun x u =>
    if 0 < (μ x).mass (raw x u) then raw x u else repair x
  have hf : Measurable (Function.uncurry f) :=
    Measurable.ite (measurableSet_lt measurable_const hmass) hraw
      (hrepair.comp measurable_fst)
  refine ⟨f, hf, ?_, ?_⟩
  · intro x u
    dsimp only [f]
    split_ifs with h
    · exact h
    · exact hrepairpos x
  · intro x
    have hrx : Measurable (raw x) := hraw.comp (measurable_const.prodMk measurable_id)
    have hs := FiniteLaw.probabilityMeasure_ae_mass_ne_zero (μ x)
    rw [← hlaw x] at hs
    have hp : ∀ᵐ u ∂(volume : Measure unitInterval), 0 < (μ x).mass (raw x u) := by
      have hh := (ae_map_iff hrx.aemeasurable (by measurability)).mp hs
      filter_upwards [hh] with u hu
      exact lt_of_le_of_ne ((μ x).nonneg _) hu.symm
    have heq : f x =ᵐ[(volume : Measure unitInterval)] raw x := by
      filter_upwards [hp] with u hu
      simp only [f, if_pos hu]
    exact (Measure.map_congr heq).trans (hlaw x)

end FCAppendix.Affine.Hybrid
