import FCAppendix.Affine.Uniform06.LiteralSharpRent
import FCAppendix.Affine.Uniform06.SharpICAbsorption

noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceSharpDensityConstants

open MeasureTheory Set Filter Topology LowBody
open Rank LiteralSharpRent LiteralWeakRent LiteralLowDuplicate SourceRankRates
open PureRankCounts PureRankProbability
open FCAppendix.Affine.Uniform07

def scaledCoefficient (i : Row) (m : ℕ) : ℝ :=
  8*80000*((m-1:ℕ):ℝ)*pureRare m/(rentConstant i*Lm i m)

def densityConstant (i : Row) : ℝ := 48*80000/rentConstant i

theorem densityConstant_pos (i : Row) : 0 < densityConstant i := by
  unfold densityConstant
  exact div_pos (by norm_num) (rentConstant_pos i)

theorem source_rank_kernel_monotone {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N c : ℕ) :
    Monotone (fun b => pureRank N c ((1+t)/2) (sourceRank t G b)) := by
  letI := sourceRivalLaw_probability ht G
  intro a b hab
  have hsub : higherAtSet b ⊆ higherAtSet a := by
    rintro ⟨k,w⟩ hw
    rcases hw with hk | hk | ⟨hk,hw⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr ⟨hk,hab.trans_lt hw⟩)
  have he : {ω : Fin N → RowRival | PiBinomial.count (higherAtSet a) Finset.univ ω < c} ⊆
      {ω | PiBinomial.count (higherAtSet b) Finset.univ ω < c} := by
    intro ω hω
    exact (count_mono_of_subset hsub ω).trans_lt hω
  have hh := measureReal_mono (μ := Measure.pi fun _ : Fin N => sourceRivalLaw t G) he
  rw [iid_count_lt_eq_binomBelow _ _ (measurableSet_higherAtSet a),
    iid_count_lt_eq_binomBelow _ _ (measurableSet_higherAtSet b)] at hh
  simpa only [Finset.card_univ,Fintype.card_fin,
    source_higher_probability ht.1 ht.2 G a,source_higher_probability ht.1 ht.2 G b,pureRank] using hh

theorem eventually_pureRare_relative (i : Row) :
    ∀ᶠ m : ℕ in atTop, 0 < Lm i m ∧
      pureRare m/Lm i m ≤ Real.exp (-(6/1000000:ℝ)*(m:ℝ)) := by
  filter_upwards [eventually_Lm_lower i] with m hL
  have hp := (Real.exp_pos _).trans_le hL
  refine ⟨hp,(div_le_iff₀ hp).mpr ?_⟩
  have hh := mul_le_mul_of_nonneg_left hL
    (Real.exp_pos (-(6/1000000:ℝ)*(m:ℝ))).le
  convert! hh using 1
  unfold pureRare
  rw [← Real.exp_add]
  congr 1
  ring

theorem scaledCoefficient_tendsto_zero (i : Row) :
    Tendsto (scaledCoefficient i) atTop (𝓝 0) := by
  let K := (8*80000:ℝ)/rentConstant i
  have hK : 0 ≤ K := by dsimp [K]; exact div_nonneg (by norm_num) (rentConstant_pos i).le
  have ht : Tendsto (fun m : ℕ => K*((m:ℝ)*Real.exp (-(6/1000000:ℝ)*(m:ℝ)))) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (6/1000000)
      (by norm_num)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def,Real.rpow_one,mul_zero] using hh.const_mul K
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventually_pureRare_relative i] with m hm
    unfold scaledCoefficient
    exact div_nonneg (by unfold pureRare; positivity) (mul_pos (rentConstant_pos i) hm.1).le
  · filter_upwards [eventually_pureRare_relative i] with m hm
    have hN : ((m-1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
    have hratio0 : 0 ≤ pureRare m/Lm i m :=
      div_nonneg (by unfold pureRare; positivity) hm.1.le
    have h₁ := mul_le_mul_of_nonneg_right hN hratio0
    have h₂ := mul_le_mul_of_nonneg_left hm.2 (Nat.cast_nonneg m)
    have hh := mul_le_mul_of_nonneg_left (h₁.trans h₂) hK
    convert! hh using 1
    dsimp only [scaledCoefficient,K]
    field_simp [(rentConstant_pos i).ne',hm.1.ne']

theorem eventually_equal_derivative_le_Lm (i : Row) :
    ∀ᶠ m : ℕ in atTop, 2*equalRare i m/xi i ≤ Lm i m := by
  have he := tendsto_exp_affine_nat (equalRelativeGap_pos i) (equalRateConstant i)
  filter_upwards [eventually_Lm_lower i,eventually_ge_atTop (2:ℕ),
    he.eventually_lt_const (half_pos (xi_pos i))] with m hL hm hsmall
  have hp := (Real.exp_pos _).trans_le hL
  have hbound : equalRare i m ≤
      Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)*Lm i m := by
    have hh := mul_le_mul_of_nonneg_left hL
      (Real.exp_pos (equalRateConstant i-(m:ℝ)*equalRelativeGap i)).le
    have heq : Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)*
        Real.exp (-(m:ℝ)*(3/1000000))=
          Real.exp (equalRateConstant i-(m:ℝ)*LowChernoff.sourceGap i) := by
      rw [← Real.exp_add]
      congr 1
      unfold equalRelativeGap
      ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (source_equal_exponent_upper i (by omega))).trans hh
  have hprod := mul_le_mul_of_nonneg_right hsmall.le hp.le
  apply (div_le_iff₀ (xi_pos i)).mpr
  nlinarith

theorem eventually_sharp_absorption_small (i : Row) :
    ∀ᶠ m : ℕ in atTop,
      0 ≤ scaledCoefficient i m ∧ scaledCoefficient i m < 1 ∧
      8*80000*((m-1:ℕ):ℝ)*pureRare m < rentConstant i*Lm i m ∧
      2*equalRare i m/xi i ≤ Lm i m := by
  filter_upwards [eventually_pureRare_relative i,eventually_equal_derivative_le_Lm i,
    (scaledCoefficient_tendsto_zero i).eventually_lt_const zero_lt_one]
    with m hL hE hε
  have hden := mul_pos (rentConstant_pos i) hL.1
  refine ⟨by unfold scaledCoefficient; exact div_nonneg (by unfold pureRare; positivity) hden.le,hε,?_,hE⟩
  exact (div_lt_one hden).mp hε

end FCAppendix.Affine.Uniform06.SourceSharpDensityConstants
