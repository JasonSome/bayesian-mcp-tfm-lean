import FCAppendix.Game.PosteriorBeliefs

noncomputable section
namespace FCAppendix.Affine.FiniteSelector
open MeasureTheory Set

variable {X A : Type*} [MeasurableSpace X] [Fintype A] [Nonempty A]

def maxIndices (f : A → ℝ) : Finset (Fin (Fintype.card A)) :=
  Finset.univ.filter (fun i => ∀ a : A, f a ≤ f ((Fintype.equivFin A).symm i))

theorem maxIndices_nonempty (f : A → ℝ) : (maxIndices f).Nonempty := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A) f Finset.univ_nonempty
  refine ⟨Fintype.equivFin A a, ?_⟩
  simp only [maxIndices, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  exact fun b => ha b (Finset.mem_univ b)

def select (f : A → ℝ) : A :=
  (Fintype.equivFin A).symm ((maxIndices f).min' (maxIndices_nonempty f))

theorem select_max (f : A → ℝ) (a : A) : f a ≤ f (select f) := by
  have hm := Finset.min'_mem (maxIndices f) (maxIndices_nonempty f)
  simp only [maxIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  exact hm a

theorem select_eq_iff (f : A → ℝ) (a : A) :
    select f = a ↔
      (∀ b : A, f b ≤ f a) ∧
      (∀ b : A, Fintype.equivFin A b < Fintype.equivFin A a → f b < f a) := by
  classical
  constructor
  · intro ha
    refine ⟨fun b => ha ▸ select_max f b, ?_⟩
    intro b hba
    have hle : f b ≤ f a := ha ▸ select_max f b
    by_contra hnot
    have heq : f b = f a := le_antisymm hle (le_of_not_gt hnot)
    have hbmem : Fintype.equivFin A b ∈ maxIndices f := by
      simp only [maxIndices, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      intro c
      rw [heq]
      exact ha ▸ select_max f c
    have hmin := Finset.min'_le (maxIndices f) _ hbmem
    have hidx : (maxIndices f).min' (maxIndices_nonempty f) = Fintype.equivFin A a := by
      simpa [select] using congrArg (Fintype.equivFin A) ha
    rw [hidx] at hmin
    exact (not_lt_of_ge hmin) hba
  · rintro ⟨hmax, hfirst⟩
    have hamem : Fintype.equivFin A a ∈ maxIndices f := by
      simp only [maxIndices, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      exact hmax
    have hle := Finset.min'_le (maxIndices f) _ hamem
    have hge : Fintype.equivFin A a ≤ (maxIndices f).min' (maxIndices_nonempty f) := by
      by_contra hnot
      have hlt := lt_of_not_ge hnot
      have hs := hfirst (select f) (by simpa [select] using hlt)
      exact (not_lt_of_ge (select_max f a)) hs
    have heq := le_antisymm hle hge
    simp [select, heq]

theorem measurable_select [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : X → A → ℝ) (hf : ∀ a, Measurable (fun x => f x a)) :
    Measurable (fun x => select (f x)) := by
  classical
  apply measurable_to_countable'
  intro a
  have he : (fun x => select (f x)) ⁻¹' {a} =
      (⋂ b : A, {x | f x b ≤ f x a}) ∩
      ⋂ b : A, {x | Fintype.equivFin A b < Fintype.equivFin A a → f x b < f x a} := by
    ext x
    simp [select_eq_iff]
  rw [he]
  refine (MeasurableSet.iInter fun b => measurableSet_le (hf b) (hf a)).inter ?_
  apply MeasurableSet.iInter
  intro b
  by_cases hba : Fintype.equivFin A b < Fintype.equivFin A a
  · simpa [hba] using measurableSet_lt (hf b) (hf a)
  · simp [hba]
end FCAppendix.Affine.FiniteSelector
