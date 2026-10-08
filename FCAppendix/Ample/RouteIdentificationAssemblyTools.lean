import FCAppendix.Ample.ActualAggregateTransfer
import FCAppendix.Ample.ActualRouteCompactness

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

namespace RouteIdentificationDetails
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma route_zero_eq_one_sub_positive_sum (Γ : FiniteGame m n c Seed) :
    actualRouteMass Γ 0 = 1 - ∑ j ∈ Finset.Icc 1 n, actualRouteMass Γ j := by
  have hs := actualRouteMass_zero_add_positive Γ
  linarith

lemma count_success_eq_one_sub_zero (μ : CountLaw n) :
    μ.success = 1 - μ.prob (fun r => r.val=0) := by
  have hh := μ.prob_compl (fun r => r.val=0)
  rw [← hh, FiniteLaw.prob_eq_expect]
  change μ.expect (fun r => successIndicator r.val) =
    μ.expect (fun r => if ¬ r.val=0 then (1 : ℝ) else 0)
  apply μ.expect_congr
  intro r
  by_cases hr : r.val=0 <;> simp [successIndicator, hr]

lemma population_zero_profile (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (d : UserProfile m n) :
    (∑ i : Fin m, (profileCountLaw Γ d i).prob (fun r => r.val=0))/(m : ℝ) =
      1-profileCoverage Γ d := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsum : ∑ i : Fin m, (profileCountLaw Γ d i).success =
      (m : ℝ)-∑ i : Fin m, (profileCountLaw Γ d i).prob (fun r => r.val=0) := by
    simp_rw [count_success_eq_one_sub_zero]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold profileCoverage
  rw [hsum]
  field_simp [hmR]
  ring

lemma finite_coverage_eq_one_sub_population_zero (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) : finiteCoverage Γ = 1-actualPopulationInclusionMass Γ 0 := by
  have hzero : actualPopulationInclusionMass Γ 0 = 1-finiteCoverage Γ := by
    unfold actualPopulationInclusionMass
    simp_rw [population_zero_profile Γ hm]
    rw [integral_sub (integrable_const (1 : ℝ)) (integrable_profileCoverage Γ hm)]
    simp only [integral_const, probReal_univ, one_smul, finiteCoverage]
  linarith

lemma load_limit_from_population_counts {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) {pi : ℕ → ℝ}
    (hM : ∀ᶠ t in atTop, 0 < M t)
    (hc : ∀ j ∈ Finset.Icc 1 n, Tendsto
      (fun t => actualPopulationInclusionMass (Γ t) j) atTop (𝓝 (pi j))) :
    Tendsto (fun t => finiteLoad (Γ t)) atTop
      (𝓝 (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j)) := by
  have hh := tendsto_finsetSum (Finset.Icc 1 n)
    (fun j hj => (hc j hj).const_mul (j : ℝ))
  apply hh.congr'
  filter_upwards [hM] with t ht
  exact (load_as_finite_count_sum (Γ t) ht).symm

end RouteIdentificationDetails
end FCAppendix.Bayes
