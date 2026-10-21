import FCAppendix.Affine.Hybrid.FocalReciprocalSampling
import FCAppendix.Probability.FiniteAveraging
import FCAppendix.Affine.Hybrid.FavoredPayoffContinuity

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Classical
open scoped BigOperators

lemma integrable_fixed_focal_reciprocal_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {L U b : ℝ} (hL : 0 < L)
    (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (D : Finset ι) (i : ι) :
    Integrable (fun x : ι → ℝ =>
      |(∑ j ∈ D, (Function.update x i b j)⁻¹) / (D.card : ℝ) - ∫ y, y⁻¹ ∂G|)
      (Measure.pi (fun _ : ι => G)) := by
  have hi : Integrable (fun y : ℝ => y⁻¹) G := by
    apply Integrable.of_bound measurable_inv.aestronglyMeasurable (1/L)
    filter_upwards [hbox] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hL.trans_le hy.1).le)]
    exact (reciprocal_box_bounds hL hy).2
  have hj (j : ι) : Integrable (fun x : ι → ℝ => (Function.update x i b j)⁻¹)
      (Measure.pi (fun _ : ι => G)) := by
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using
        (integrable_const (b⁻¹) : Integrable (fun _ : ι → ℝ => b⁻¹) _)
    · simpa only [Function.update_of_ne h] using (integrable_comp_eval (i := j) hi)
  exact (((integrable_finsetSum D (fun j _ => hj j)).div_const _).sub
    (integrable_const _)).abs

lemma integral_finite_expect {α Ω : Type*} [MeasurableSpace α] [Fintype Ω]
    (P : Measure α) (C : FiniteLaw Ω) (f : α → Ω → ℝ)
    (hi : ∀ t, Integrable (fun x => f x t) P) :
    (∫ x, C.expect (f x) ∂P) = C.expect (fun t => ∫ x, f x t ∂P) := by
  unfold FiniteLaw.expect
  rw [integral_finsetSum _ (fun t _ => (hi t).const_mul _)]
  simp_rw [integral_const_mul]

theorem integral_rank_expect_le_two {ι α : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [MeasurableSpace α] (P : Measure α)
    (row : α → ι → ℝ) (hrow : Measurable row) (F : α → ι → ℝ) (C : ℝ)
    (hi : ∀ t, Integrable (fun x => F x t) P)
    (hF : ∀ᵐ x ∂P, ∀ t, 0 ≤ F x t) (hC : ∀ t, (∫ x, F x t ∂P) ≤ C) :
    (∫ x, (rankLaw (row x)).expect (F x) ∂P) ≤ 2*C := by
  have hw (t : ι) : AEStronglyMeasurable (fun x => (rankLaw (row x)).mass t) P :=
    ((measurable_rankLaw_mass t).comp hrow).aestronglyMeasurable
  have hprod (t : ι) : Integrable (fun x => (rankLaw (row x)).mass t * F x t) P := by
    apply (hi t).bdd_mul (c := 1) (hw t)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg ((rankLaw (row x)).nonneg t)]
      exact FiniteLaw.mass_le_one _ _)
  have hpoint : ∀ᵐ x ∂P, (rankLaw (row x)).expect (F x) ≤
      ∑ t, (2/(Fintype.card ι : ℝ))*F x t := by
    filter_upwards [hF] with x hx
    exact Finset.sum_le_sum (fun t _ =>
      mul_le_mul_of_nonneg_right (rankLaw_mass_le (row x) t) (hx t))
  have hh := integral_mono_ae (integrable_finsetSum _ (fun t _ => hprod t))
    (integrable_finsetSum _ (fun t _ => (hi t).const_mul _)) hpoint
  rw [integral_finsetSum _ (fun t _ => (hi t).const_mul _)] at hh
  simp_rw [integral_const_mul] at hh
  have hsum : (∑ t : ι, (2/(Fintype.card ι : ℝ))*(∫ x, F x t ∂P)) ≤
      ∑ _t : ι, (2/(Fintype.card ι : ℝ))*C := by
    exact Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hC t) (by positivity))
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (∑ _t : ι, (2/(Fintype.card ι : ℝ))*C) = 2*C := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  exact hh.trans (hsum.trans_eq he)

theorem favored_reciprocal_sampling_L1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (G : Measure ℝ) [IsProbabilityMeasure G] {L U b : ℝ}
    (hL : 0 < L) (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hb : b ∈ Icc L U)
    (K : ℕ) (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K) (hKN : K < Fintype.card ι) (i : ι) :
    (∫ x : ι → ℝ, (rankLaw (Function.update x i b)).expect (fun t =>
      (conditionalFill K t).expect (fun E =>
        |(∑ j ∈ Finset.univ \ E, (Function.update x i b j)⁻¹) /
          ((Finset.univ \ E).card : ℝ) - ∫ y, y⁻¹ ∂G|))
      ∂Measure.pi (fun _ : ι => G)) ≤
      2*((1/L)/Real.sqrt ((Fintype.card ι-K : ℕ) : ℝ)+(1/L)/(Fintype.card ι-K : ℕ)) := by
  let P := Measure.pi (fun _ : ι => G)
  let F : (ι → ℝ) → ι → ℝ := fun x t => (conditionalFill K t).expect (fun E =>
    |(∑ j ∈ Finset.univ \ E, (Function.update x i b j)⁻¹) /
      ((Finset.univ \ E).card : ℝ) - ∫ y, y⁻¹ ∂G|)
  have hi (t : ι) : Integrable (fun x => F x t) P := by
    apply integrable_finsetSum
    intro E _
    exact (integrable_fixed_focal_reciprocal_error G hL hbox (Finset.univ \ E) i).const_mul _
  have hrow : Measurable (fun x : ι → ℝ => Function.update x i b) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_const : Measurable (fun _ : ι → ℝ => b))
    · simpa only [Function.update_of_ne hj] using (measurable_pi_apply j)
  apply integral_rank_expect_le_two P (fun x => Function.update x i b)
    hrow F _ hi
  · exact Filter.Eventually.of_forall (fun x t =>
      (conditionalFill K t).expect_nonneg (fun _ => abs_nonneg _))
  · intro t
    rw [show (∫ x, F x t ∂P) = (conditionalFill K t).expect (fun E =>
      ∫ x, |(∑ j ∈ Finset.univ \ E, (Function.update x i b j)⁻¹) /
        ((Finset.univ \ E).card : ℝ) - ∫ y, y⁻¹ ∂G| ∂P) from
      integral_finite_expect P _ _ (fun E =>
        integrable_fixed_focal_reciprocal_error G hL hbox (Finset.univ \ E) i)]
    apply FiniteLaw.expect_le_const_of_support
    intro E hE
    have hcard := (conditionalFill_implements hN hK hKN.le t).1 E hE
    have hD : (Finset.univ \ E).card = Fintype.card ι-K := by
      simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,hcard]
    have hn : (Finset.univ \ E).Nonempty := Finset.card_pos.mp (by rw [hD]; omega)
    simpa only [hD] using fixed_focal_subset_reciprocal_L1 G hL hbox hb (Finset.univ \ E) hn i

end FCAppendix.Affine.Hybrid
