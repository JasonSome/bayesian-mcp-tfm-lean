import FCAppendix.Probability.PiBinomial

noncomputable section
namespace FCAppendix.CommonReserve
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

variable {m : ℕ} {D : Type*} [MeasurableSpace D]

theorem iid_relabel_measurePreserving (μ : Measure D) [IsProbabilityMeasure μ]
    (e : Equiv.Perm (Fin m)) :
    MeasurePreserving (fun d : Fin m → D => d ∘ e.symm)
      (Measure.pi fun _ : Fin m => μ) (Measure.pi fun _ : Fin m => μ) := by
  convert measurePreserving_piCongrLeft (fun _ : Fin m => μ) e using 1
  funext d i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

theorem iid_integral_eq (μ : Measure D) [IsProbabilityMeasure μ]
    (f : (Fin m → D) → Fin m → ℝ) (hf : ∀ i, Measurable (fun d => f d i))
    (he : ∀ (e : Equiv.Perm (Fin m)) d i, f (d ∘ e.symm) (e i) = f d i)
    (i l : Fin m) :
    (∫ d, f d i ∂(Measure.pi fun _ : Fin m => μ)) =
      ∫ d, f d l ∂(Measure.pi fun _ : Fin m => μ) := by
  let e := Equiv.swap i l
  have hi : e i = l := Equiv.swap_apply_left _ _
  have hp := iid_relabel_measurePreserving μ e
  calc
    _ = ∫ d, f (d ∘ e.symm) l ∂(Measure.pi fun _ : Fin m => μ) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun d => by
        change f d i = f (d ∘ e.symm) l
        rw [← hi]
        exact (he e d i).symm
    _ = ∫ d, f d l ∂(Measure.pi fun _ : Fin m => μ).map
        (fun d : Fin m → D => d ∘ e.symm) :=
      (integral_map_of_stronglyMeasurable hp.measurable (hf l).stronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

theorem iid_integral_eq_identity_average (μ : Measure D) [IsProbabilityMeasure μ]
    (f : (Fin m → D) → Fin m → ℝ) (hf : ∀ i, Measurable (fun d => f d i))
    (he : ∀ (e : Equiv.Perm (Fin m)) d i, f (d ∘ e.symm) (e i) = f d i)
    (i : Fin m) :
    (∫ d, f d i ∂(Measure.pi fun _ : Fin m => μ)) =
      (∑ l : Fin m, ∫ d, f d l ∂(Measure.pi fun _ : Fin m => μ)) / m := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt i.isLt)
  simp_rw [← iid_integral_eq μ f hf he i]
  simp [hm]

def equalShare (A : Set D) (B : (Fin m → D) → ℝ)
    (d : Fin m → D) (i : Fin m) : ℝ := by
  classical
  exact if d i ∈ A then B d / ((Finset.univ.filter (fun l => d l ∈ A)).card : ℝ) else 0

omit [MeasurableSpace D] in
theorem equalShare_nonneg (A : Set D) (B : (Fin m → D) → ℝ)
    (hB : ∀ d, 0 ≤ B d) (d : Fin m → D) (i : Fin m) : 0 ≤ equalShare A B d i := by
  classical
  unfold equalShare
  split
  · exact div_nonneg (hB d) (Nat.cast_nonneg _)
  · exact le_rfl

omit [MeasurableSpace D] in
theorem equalShare_le (A : Set D) (B : (Fin m → D) → ℝ)
    (hB : ∀ d, 0 ≤ B d) (d : Fin m → D) (i : Fin m) : equalShare A B d i ≤ B d := by
  classical
  unfold equalShare
  split
  next hi =>
    have hc : 0 < (Finset.univ.filter (fun l => d l ∈ A)).card :=
      Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    apply div_le_self (hB d)
    exact_mod_cast (Nat.succ_le_of_lt hc)
  · exact hB d

omit [MeasurableSpace D] in
theorem sum_equalShare_le (A : Set D) (B : (Fin m → D) → ℝ)
    (hB : ∀ d, 0 ≤ B d) (d : Fin m → D) :
    (∑ i : Fin m, equalShare A B d i) ≤ B d := by
  classical
  let S := Finset.univ.filter (fun l => d l ∈ A)
  have he : (∑ i : Fin m, equalShare A B d i) =
      (S.card : ℝ) * (B d / S.card) := by
    simp only [equalShare, ← Finset.sum_filter]
    simp [S]
  rw [he]
  by_cases hs : S.card = 0
  · simpa [hs] using hB d
  · have hsR : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs
    rw [mul_div_cancel₀ _ hsR]

omit [MeasurableSpace D] in
theorem equalShare_relabel (A : Set D) (B : (Fin m → D) → ℝ)
    (hB : ∀ (e : Equiv.Perm (Fin m)) d, B (d ∘ e.symm) = B d)
    (e : Equiv.Perm (Fin m)) (d : Fin m → D) (i : Fin m) :
    equalShare A B (d ∘ e.symm) (e i) = equalShare A B d i := by
  classical
  have he : Finset.univ.filter (fun l => (d ∘ e.symm) l ∈ A) =
      (Finset.univ.filter (fun l => d l ∈ A)).map e.toEmbedding := by
    ext l
    simp
  have hc : (Finset.univ.filter (fun l => d (e.symm l) ∈ A)).card =
      (Finset.univ.filter (fun l => d l ∈ A)).card := by
    simpa only [Function.comp_apply, Finset.card_map] using congrArg Finset.card he
  simp only [equalShare, Function.comp_apply, Equiv.symm_apply_apply, hB, hc]

theorem measurable_equalShare (A : Set D) (hA : MeasurableSet A)
    (B : (Fin m → D) → ℝ) (hB : Measurable B) (i : Fin m) :
    Measurable (fun d => equalShare A B d i) := by
  classical
  have hc : Measurable (fun d : Fin m → D =>
      ((Finset.univ.filter (fun l => d l ∈ A)).card : ℝ)) := by
    have he : (fun d : Fin m → D => ((Finset.univ.filter (fun l => d l ∈ A)).card : ℝ)) =
        fun d => ∑ l : Fin m, if d l ∈ A then (1 : ℝ) else 0 := by
      funext d
      simp
    rw [he]
    exact Finset.measurable_sum _ fun l _ => Measurable.ite
      ((measurable_pi_apply l) hA) measurable_const measurable_const
  exact Measurable.ite ((measurable_pi_apply i) hA) (hB.div hc) measurable_const

theorem integrable_equalShare (μ : Measure D) [IsProbabilityMeasure μ]
    (A : Set D) (hA : MeasurableSet A) (B : (Fin m → D) → ℝ)
    (hB : Measurable B) (hB0 : ∀ d, 0 ≤ B d)
    (R : ℝ) (hR : ∀ d, B d ≤ R) (i : Fin m) :
    Integrable (fun d => equalShare A B d i) (Measure.pi fun _ : Fin m => μ) := by
  apply Integrable.of_bound (measurable_equalShare A hA B hB i).aestronglyMeasurable R
  exact Eventually.of_forall fun d => by
    rw [Real.norm_eq_abs, abs_of_nonneg (equalShare_nonneg A B hB0 d i)]
    exact (equalShare_le A B hB0 d i).trans (hR d)

end FCAppendix.CommonReserve
