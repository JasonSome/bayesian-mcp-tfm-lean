import FCAppendix.Affine.Hybrid.HarmonicStability

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma measurable_fixedFocalRow (i : ι) (b : ℝ) :
    Measurable (fun x : ι → ℝ => Function.update x i b) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using (measurable_const : Measurable (fun _ : ι → ℝ => b))
  · simpa only [Function.update_of_ne hj] using (measurable_pi_apply j)

lemma ae_fixedFocalRow_box (G : Measure ℝ) [IsProbabilityMeasure G]
    {L U b : ℝ} (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hb : b ∈ Icc L U) (i : ι) :
    ∀ᵐ x ∂Measure.pi (fun _ : ι => G), ∀ j, Function.update x i b j ∈ Icc L U := by
  have hr : ∀ᵐ x ∂Measure.pi (fun _ : ι => G), ∀ j, x j ∈ Icc L U := ae_all_iff.mpr
    (fun j => (measurePreserving_eval (fun _ : ι => G) j).quasiMeasurePreserving.ae hbox)
  filter_upwards [hr] with x hx j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using hb
  · simpa only [Function.update_of_ne hj] using hx j

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_finiteMultiplier (xi : ℝ) (D : Finset ι) (r : ℕ) :
    Measurable (fun b : ι → ℝ => finiteMultiplier xi b D r) := by
  exact measurable_const.div (Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).inv))

lemma integrable_fixed_focal_multiplier (G : Measure ℝ) [IsProbabilityMeasure G]
    {L U b : ℝ} (hL : 0 < L) (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hb : b ∈ Icc L U)
    (xi : ℝ) (D : Finset ι) (r : ℕ) (i : ι) :
    Integrable (fun x : ι → ℝ => finiteMultiplier xi (Function.update x i b) D r)
      (Measure.pi (fun _ : ι => G)) := by
  by_cases hD : D.Nonempty
  · apply Integrable.of_bound
      ((measurable_finiteMultiplier xi D r).comp (measurable_fixedFocalRow i b)).aestronglyMeasurable
      (|finiteReceiptFactor xi D.card r| *U)
    filter_upwards [ae_fixedFocalRow_box G hbox hb i] with x hx
    have hU : 0 < U := hL.trans_le (hb.1.trans hb.2)
    have hs := (subset_reciprocalMean_bounds hL _ hx D hD).1
    have hs0 := (one_div_pos.mpr hU).trans_le hs
    have hi : 1/((∑ j ∈ D, (Function.update x i b j)⁻¹)/(D.card : ℝ)) ≤ U := by
      have hh := one_div_le_one_div_of_le (one_div_pos.mpr hU) hs
      simpa using hh
    change ‖finiteMultiplier xi (Function.update x i b) D r‖ ≤ _
    rw [Real.norm_eq_abs,finiteMultiplier_eq_factor_div_mean xi _ D r hD,
      abs_div,abs_of_pos hs0,div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
  · have hE : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    simp only [hE,finiteMultiplier,Finset.card_empty,Nat.cast_zero,Finset.sum_empty,div_zero]
    exact integrable_const _

omit [DecidableEq ι] in
lemma integrable_rank_expect {α : Type*} [MeasurableSpace α] [Nonempty ι]
    (P : Measure α) (row : α → ι → ℝ) (hrow : Measurable row) (F : α → ι → ℝ)
    (hi : ∀ t, Integrable (fun x => F x t) P) :
    Integrable (fun x => (rankLaw (row x)).expect (F x)) P := by
  apply integrable_finsetSum
  intro t _
  apply (hi t).bdd_mul (c := 1)
    (((measurable_rankLaw_mass t).comp hrow).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖(rankLaw (row x)).mass t‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg ((rankLaw (row x)).nonneg t)]
    exact FiniteLaw.mass_le_one _ _)

lemma expect_le_expect_on_support {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    {f g : Ω → ℝ} (h : ∀ t, P.mass t ≠ 0 → f t ≤ g t) : P.expect f ≤ P.expect g := by
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : P.mass t = 0
  · simp only [ht,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h t ht) (P.nonneg t)

theorem favored_multiplier_L1 [Nonempty ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {L U b h0 : ℝ}
    (hL : 0 < L) (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hb : b ∈ Icc L U)
    (hh0 : |h0| ≤ 1) (xi : ℝ) (r K : ℕ)
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K) (hKN : K < Fintype.card ι) (i : ι) :
    (∫ x : ι → ℝ, (favoredSetLaw (Function.update x i b) K).expect (fun E =>
      |finiteMultiplier xi (Function.update x i b) (Finset.univ \ E) r-h0/reciprocalMean G|)
      ∂Measure.pi (fun _ : ι => G)) ≤
      U*|finiteReceiptFactor xi (Fintype.card ι-K) r-h0|+
      U^2*(2*((1/L)/Real.sqrt ((Fintype.card ι-K : ℕ) : ℝ)+(1/L)/(Fintype.card ι-K : ℕ))) := by
  let P := Measure.pi (fun _ : ι => G)
  let Q : (ι → ℝ) → ℝ := fun x => (favoredSetLaw (Function.update x i b) K).expect (fun E =>
    |finiteMultiplier xi (Function.update x i b) (Finset.univ \ E) r-h0/reciprocalMean G|)
  let R : (ι → ℝ) → ℝ := fun x => (favoredSetLaw (Function.update x i b) K).expect (fun E =>
    |(∑ j ∈ Finset.univ \ E, (Function.update x i b j)⁻¹) / ((Finset.univ \ E).card : ℝ)-reciprocalMean G|)
  have hQi : Integrable Q P := by
    dsimp only [Q]
    simp only [favoredSetLaw,FiniteLaw.expect_finiteMix]
    apply integrable_rank_expect P _ (measurable_fixedFocalRow i b)
    intro t
    apply integrable_finsetSum
    intro E _
    exact (((integrable_fixed_focal_multiplier G hL hbox hb xi (Finset.univ \ E) r i).sub
      (integrable_const _)).abs).const_mul _
  have hRi : Integrable R P := by
    dsimp only [R]
    simp only [favoredSetLaw,FiniteLaw.expect_finiteMix]
    apply integrable_rank_expect P _ (measurable_fixedFocalRow i b)
    intro t
    apply integrable_finsetSum
    intro E _
    exact (integrable_fixed_focal_reciprocal_error G hL hbox (Finset.univ \ E) i).const_mul _
  have hpoint : ∀ᵐ x ∂P, Q x ≤
      U*|finiteReceiptFactor xi (Fintype.card ι-K) r-h0|+U^2*R x := by
    filter_upwards [ae_fixedFocalRow_box G hbox hb i] with x hx
    have hc : ∀ E, (favoredSetLaw (Function.update x i b) K).mass E ≠ 0 →
        (Finset.univ \ E).card = Fintype.card ι-K := by
      intro E hE
      have he := favoredSetLaw_support (Function.update x i b) hN hK hKN.le E hE
      simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,he]
    have hh : Q x ≤ (favoredSetLaw (Function.update x i b) K).expect (fun E =>
        U*|finiteReceiptFactor xi (Fintype.card ι-K) r-h0|+
        U^2*|(∑ j ∈ Finset.univ \ E, (Function.update x i b j)⁻¹)/
          ((Finset.univ \ E).card : ℝ)-reciprocalMean G|) := by
      apply expect_le_expect_on_support
      intro E hE
      have hcard := hc E hE
      have hD : (Finset.univ \ E).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
      simpa only [hcard] using finiteMultiplier_error G hL (hb.1.trans hb.2) hbox hh0 xi
        (Function.update x i b) hx (Finset.univ \ E) r hD
    simpa only [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_const_mul] using hh
  have hh := integral_mono_ae hQi ((integrable_const _).add (hRi.const_mul _)) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) (hRi.const_mul _),integral_const,
    probReal_univ,one_smul,integral_const_mul] at hh
  have hs : (∫ x, R x ∂P) ≤ 2*((1/L)/Real.sqrt ((Fintype.card ι-K : ℕ) : ℝ)+
      (1/L)/(Fintype.card ι-K : ℕ)) := by
    simpa only [R,P,reciprocalMean,favoredSetLaw,FiniteLaw.expect_finiteMix] using
      favored_reciprocal_sampling_L1 G hL hbox hb K hN hK hKN i
  change (∫ x, Q x ∂P) ≤ _
  nlinarith [sq_nonneg U]

end FCAppendix.Affine.Hybrid
