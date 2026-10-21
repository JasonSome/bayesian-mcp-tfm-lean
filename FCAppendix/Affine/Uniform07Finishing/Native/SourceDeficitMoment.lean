import FCAppendix.Affine.Uniform07Finishing.Native.SourceSamplingProbability

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Bayes Game Set Classical
open StrictNative ConditionalSuccess
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

lemma clipped_budget_difference_le (c N H₀ H₁ : ℕ) :
    max (min (c-H₀) N) (min (c-H₁) N) -
      min (min (c-H₀) N) (min (c-H₁) N) ≤ max H₀ H₁-min H₀ H₁ := by
  omega

omit [Nonempty (Fin m)] in

theorem sourceContextDeficit_le_abs (c : ℕ) (X : ClassifiedContext m) :
    sourceContextDeficit c X ≤ |(X.2.1 : ℝ)-(X.2.2 : ℝ)| := by
  have h := clipped_budget_difference_le c (Weighted.presentSet X.1).card X.2.1 X.2.2
  have hbudget : (max (Weighted.budget c 0 X) (Weighted.budget c 1 X)-
      Weighted.commonBudget c X : ℕ) ≤ max X.2.1 X.2.2-min X.2.1 X.2.2 := by
    simpa [Weighted.budget,Weighted.commonBudget,contextUpper] using h
  have he : ((max X.2.1 X.2.2-min X.2.1 X.2.2 : ℕ) : ℝ) =
      |(X.2.1 : ℝ)-(X.2.2 : ℝ)| := by
    by_cases hle : X.2.1 ≤ X.2.2
    · rw [max_eq_right hle,min_eq_left hle,Nat.cast_sub hle,
        abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hle))]
      ring
    · have hle' : X.2.2 < X.2.1 := lt_of_not_ge hle
      rw [max_eq_left hle'.le,min_eq_right hle'.le,Nat.cast_sub hle'.le,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle'.le))]
  exact (by
    unfold sourceContextDeficit
    exact_mod_cast hbudget : sourceContextDeficit c X ≤
    ((max X.2.1 X.2.2-min X.2.1 X.2.2 : ℕ) : ℝ)).trans_eq he

omit [Nonempty (Fin m)] in
lemma observedContext_upper_bounds (R : ℝ) (j : Fin 2) (L : LocalList m) :
    (observedContext R j L).2.1 ≤ m ∧ (observedContext R j L).2.2 ≤ m := by
  have hh : StrictTags.localCount R R L 2 ≤ m := by
    unfold StrictTags.localCount
    calc
      _ ≤ ∑ _ : Fin m, 1 := Finset.sum_le_sum (fun u _ => by split_ifs <;> omega)
      _ = m := by simp
  have ht : m-StrictTags.localCount R R L 0-StrictTags.localCount R R L 2 ≤ m :=
    (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  by_cases hj : j = 0 <;> simp only [observedContext,hj,if_true,if_false]
  · exact ⟨hh,ht⟩
  · exact ⟨ht,hh⟩

omit [Nonempty (Fin m)] in
lemma sourceContextGap_abs_le {X : ClassifiedContext m}
    (hX : X.2.1 ≤ m ∧ X.2.2 ≤ m) :
    |(X.2.1 : ℝ)-(X.2.2 : ℝ)| ≤ (m : ℝ) := by
  have h₀ : (X.2.1 : ℝ) ≤ m := by exact_mod_cast hX.1
  have h₁ : (X.2.2 : ℝ) ≤ m := by exact_mod_cast hX.2
  have hn₀ := Nat.cast_nonneg (α := ℝ) X.2.1
  have hn₁ := Nat.cast_nonneg (α := ℝ) X.2.2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

omit [Nonempty (Fin m)] in

theorem sourceContextDeficit_integral_le_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ℕ) (C : Ω → ClassifiedContext m) (hC : Measurable C)
    (hcounts : ∀ x, (C x).2.1 ≤ m ∧ (C x).2.2 ≤ m)
    (M : ℝ) (hM : 0 ≤ M)
    (hsecond : (∫ x, ((C x).2.1-(C x).2.2 : ℝ)^2 ∂μ) ≤ M) :
    (∫ x, sourceContextDeficit c (C x) ∂μ) ≤ Real.sqrt M := by
  let f := fun x => sourceContextDeficit c (C x)
  let g := fun x => ((C x).2.1 : ℝ)-((C x).2.2 : ℝ)
  have hf : Measurable f := (measurable_sourceContextDeficit c).comp hC
  have hg : Measurable g :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hC.snd.fst).sub
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hC.snd.snd)
  have hfi : Integrable f μ := integrable_sourceContextDeficit μ c C hC
  have hfi2 : Integrable (fun x => f x^2) μ := by
    apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable ((m : ℝ)^2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (sourceContextDeficit_bounds c (C x)).1
      (sourceContextDeficit_bounds c (C x)).2 2
  have hgi2 : Integrable (fun x => g x^2) μ := by
    apply Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable ((m : ℝ)^2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (g x))
      (sourceContextGap_abs_le (hcounts x)) 2
  have hsq : (∫ x, f x^2 ∂μ) ≤ M := by
    apply (integral_mono hfi2 hgi2 (fun x => ?_)).trans hsecond
    simpa only [sq_abs] using pow_le_pow_left₀ (sourceContextDeficit_bounds c (C x)).1
      (sourceContextDeficit_le_abs c (C x)) 2
  let I := ∫ x, f x ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun x => (sourceContextDeficit_bounds c (C x)).1)
  have hvar : (∫ x, (f x-I)^2 ∂μ) = (∫ x, f x^2 ∂μ)-I^2 := by
    calc
      _ = ∫ x, (f x^2-(2*I)*f x)+I^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, f x^2 ∂μ)-(2*I)*I+I^2 := by
        rw [integral_add (f := fun x : Ω => f x^2-(2*I)*f x) (g := fun _ : Ω => I^2)
          (hfi2.sub (hfi.const_mul (2*I))) (integrable_const _),
          integral_sub (f := fun x : Ω => f x^2) (g := fun x : Ω => (2*I)*f x)
            hfi2 (hfi.const_mul (2*I)),integral_const_mul,integral_const]
        simp only [probReal_univ,one_smul,I]
      _ = _ := by ring
  have hvar0 : 0 ≤ ∫ x : Ω, (f x-I)^2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (f x-I))
  rw [hvar] at hvar0
  have hI2 : I^2 ≤ M := by linarith
  exact (Real.le_sqrt hI hM).mpr hI2

omit [Nonempty (Fin m)] in

theorem source_deviation_deficit_integral_le_sqrt
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ]
    (c : ℕ) (R : ℝ) (i : Fin m) (A : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (M : ℝ) (hM : 0 ≤ M)
    (hsecond : (∫ d, ((observedContext R j (deviationList i A d τ j)).2.1-
      (observedContext R j (deviationList i A d τ j)).2.2 : ℝ)^2
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ M) :
    (∫ d, sourceContextDeficit c (observedContext R j (deviationList i A d τ j))
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ Real.sqrt M :=
  sourceContextDeficit_integral_le_sqrt _ c _
    ((measurable_observedContext R j).comp (measurable_deviationList_profile i A τ j))
    (fun _ => observedContext_upper_bounds R j _) M hM hsecond

end FCAppendix.Affine.Uniform07Finishing
