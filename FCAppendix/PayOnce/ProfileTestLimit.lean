import FCAppendix.PayOnce.FullSequenceAllocation
import FCAppendix.PayOnce.BinomialContinuity
import FCAppendix.PayOnce.ProfileCountLaw

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CovarianceConcentration
open scoped BigOperators
variable {M C : ℕ → ℕ} {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem profile_test_limit_of_marginal_gap
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hm : ∀ t, 0 < M t) (hcm : ∀ t, C t ≤ M t)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    {g L : ℝ} (hL : 0 < L)
    (hgap : Tendsto (fun t => ∫ d, populationMean (fun i =>
      |analyticalProfileMarginal (Γ t) hn (hcm t) d i-Limit.pStar n L ((d i).1.1-g)|)
        ∂userProfileLaw (Γ t)) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : Continuous f) (hfb : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1)
    {K : ℝ} (hK : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |f x-f y| ≤ K*|x-y|) :
    Tendsto (fun t => ∫ d, populationMean (fun i => f (analyticalProfileMarginal (Γ t) hn (hcm t) d i))
      ∂userProfileLaw (Γ t)) atTop (𝓝 (∫ v, f (Limit.pStar n L (v-g)) ∂F)) := by
  let p := fun t => analyticalProfileMarginal (Γ t) hn (hcm t)
  let q := fun t (d : UserProfile (M t) n) i => Limit.pStar n L ((d i).1.1-g)
  have hp t i : Measurable (fun d => p t d i) := measurable_analyticalProfileMarginal (Γ t) _ _ i
  have hq t i : Measurable (fun d => q t d i) := (Limit.measurable_pStar n L).comp
    (((measurable_fst.comp measurable_fst).comp (measurable_pi_apply i)).sub_const g)
  have hpb t d i := analyticalProfileMarginal_bounds (Γ t) hn (hcm t) d i
  have hqb t d i : q t d i ∈ Icc (0:ℝ) 1 := ⟨Limit.pStar_nonneg,Limit.pStar_le_one hL.le⟩
  have htest := tendsto_population_test_gap (fun t => userProfileLaw (Γ t)) p q hp hq hpb hqb f hf hfb hK hgap
  apply tendsto_population_expectation_of_gap (fun t => userProfileLaw (Γ t))
    (fun t d i => f (p t d i)) (fun t d i => f (q t d i))
    (fun t i => hf.measurable.comp (hp t i)) (fun t i => hf.measurable.comp (hq t i))
    (fun t d i => hfb _ (hpb t d i)) (fun t d i => hfb _ (hqb t d i)) _ htest
  intro t
  have hfv : Measurable (fun v : ℝ => f (Limit.pStar n L (v-g))) :=
    hf.measurable.comp ((Limit.measurable_pStar n L).comp (measurable_id.sub_const g))
  calc
    _ = ∫ x : ℝ × JointAction n, f (Limit.pStar n L (x.1-g)) ∂((Γ t).F ⊗ₘ (Γ t).σ) := by
      apply integral_profile_mean_action (Γ t) (hm t) _ (hfv.comp measurable_fst) (K := 1)
      intro x
      have hb := hfb (Limit.pStar n L (x.1-g)) ⟨Limit.pStar_nonneg,Limit.pStar_le_one hL.le⟩
      simp only [Function.comp_apply,Real.norm_eq_abs]
      rw [abs_of_nonneg hb.1]
      exact hb.2
    _ = ∫ v, f (Limit.pStar n L (v-g)) ∂F := by
      have hmap : Measure.map Prod.fst ((Γ t).F ⊗ₘ (Γ t).σ) = F := by
        change ((Γ t).F ⊗ₘ (Γ t).σ).fst = F
        rw [Measure.fst_compProd,hF t]
      rw [← hmap]
      exact (integral_map measurable_fst.aemeasurable hfv.aestronglyMeasurable).symm

end FCAppendix.Bayes
