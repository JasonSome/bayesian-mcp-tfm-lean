import FCAppendix.Exclusive.BayesianKernel
import FCAppendix.Exclusive.MixtureBounds
import FCAppendix.PayOnce.ProfileExpectations

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce.CovarianceConcentration
open scoped BigOperators ProbabilityTheory

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def exclusiveMixture (Γ : FiniteGame m n c Seed) :
    Measure (UserProfile m n × Fin m) := populationLaw (userProfileLaw Γ)

noncomputable def exclusiveMixtureP (Γ : FiniteGame m n c Seed)
    (z : UserProfile m n × Fin m) : ℝ := exclusiveProfileMarginal Γ z.1 z.2

instance exclusiveMixture_isProbabilityMeasure (Γ : FiniteGame m n c Seed)
    [Nonempty (Fin m)] : IsProbabilityMeasure (exclusiveMixture Γ) :=
  inferInstanceAs (IsProbabilityMeasure (populationLaw (userProfileLaw Γ)))

theorem ae_exclusiveMixture_of_all (Γ : FiniteGame m n c Seed)
    [Nonempty (Fin m)] (P : UserProfile m n → Fin m → Prop)
    (hP : ∀ᵐ d ∂userProfileLaw Γ, ∀ i, P d i) :
    ∀ᵐ z ∂exclusiveMixture Γ, P z.1 z.2 := by
  have h := (measurePreserving_fst (μ := userProfileLaw Γ)
    (ν := uniformOn (univ : Set (Fin m)))).quasiMeasurePreserving.ae hP
  exact h.mono fun z hz => hz z.2

theorem measurable_exclusiveMixtureP (Γ : FiniteGame m n c Seed) :
    Measurable (exclusiveMixtureP Γ) :=
  measurable_from_prod_countable_left (measurable_exclusiveProfileMarginal Γ)

theorem exclusiveMixture_value_mass (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (exclusiveMixture Γ).real {z | (z.1 z.2).1.1 ∈ E} = Γ.F.real E := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let f : ℝ × JointAction n → ℝ := fun x => E.indicator (fun _ => (1 : ℝ)) x.1
  have hf : Measurable f := (measurable_const.indicator hE).comp measurable_fst
  have hb (x : ℝ × JointAction n) : ‖f x‖ ≤ 1 := by
    simp only [f, indicator_apply]
    split_ifs <;> norm_num
  have hzmeas : Measurable (fun z : UserProfile m n × Fin m => (z.1 z.2).1.1) :=
    measurable_from_prod_countable_left fun i =>
      measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))
  have hZE : MeasurableSet {z : UserProfile m n × Fin m | (z.1 z.2).1.1 ∈ E} :=
    hE.preimage hzmeas
  have hI := integrable_populationLaw_of_bound (userProfileLaw Γ)
    (fun d i => f (d i).1)
    (fun i => hf.comp (measurable_fst.comp (measurable_pi_apply i)))
    (fun d i => hb (d i).1)
  have he : (∫ z, f (z.1 z.2).1 ∂exclusiveMixture Γ) = Γ.F.real E := by
    rw [exclusiveMixture, integral_populationLaw (userProfileLaw Γ)
      (fun (d : UserProfile m n) (i : Fin m) => f (d i).1) hI,
      integral_profile_mean_action Γ hm f hf hb]
    have hp : MeasurePreserving Prod.fst (Γ.F ⊗ₘ Γ.σ) Γ.F :=
      ⟨measurable_fst, Measure.fst_compProd Γ.F Γ.σ⟩
    rw [← integral_indicator_one (μ := Γ.F) hE]
    have hi := integral_map (μ := Γ.F ⊗ₘ Γ.σ) hp.measurable.aemeasurable
      ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator hE).aestronglyMeasurable
    rw [hp.map_eq] at hi
    exact hi.symm
  rw [← integral_indicator_one hZE]
  exact he

theorem exclusiveMixture_mean (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hn : 0 < n) :
    (∫ z, exclusiveMixtureP Γ z ∂exclusiveMixture Γ) = finiteLoad Γ / n := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hi := integrable_populationLaw_of_bound (userProfileLaw Γ)
    (exclusiveProfileMarginal Γ) (measurable_exclusiveProfileMarginal Γ)
    (C := 1) (fun d i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (exclusiveProfileMarginal_bounds Γ hn d i).1]
      exact (exclusiveProfileMarginal_bounds Γ hn d i).2)
  change (∫ z, exclusiveProfileMarginal Γ z.1 z.2 ∂populationLaw (userProfileLaw Γ)) = _
  rw [integral_populationLaw _ _ hi]
  have he (d : UserProfile m n) : populationMean (exclusiveProfileMarginal Γ d) =
      profileLoad Γ d / n := by
    simp only [populationMean, exclusiveProfileMarginal, profileLoad, Fintype.card_fin,
      ← Finset.sum_div]
    ring
  simp_rw [he]
  rw [integral_div]
  rfl

theorem exclusiveMixture_success (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (B : PosteriorSystem Γ)
    (hB : ExclusiveOptimalOnPath Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hr : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = k + 1)) :
    (∫ z, PayOnce.success (k + 1) (exclusiveMixtureP Γ z) ∂exclusiveMixture Γ) =
      finiteCoverage Γ := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let j : Fin (k + 1) := ⟨0, by omega⟩
  have hi := integrable_populationLaw_of_bound (userProfileLaw Γ)
    (fun d i => PayOnce.success (k + 1) (exclusiveProfileMarginal Γ d i))
    (fun i => (PayOnce.continuous_success (k + 1)).measurable.comp
      (measurable_exclusiveProfileMarginal Γ i))
    (C := 1) (fun d i => by
      have hb := exclusiveProfileMarginal_bounds Γ (by omega) d i
      have hs0 : 0 ≤ PayOnce.success (k + 1) (exclusiveProfileMarginal Γ d i) := by
        simpa only [IndependentCounts.binomial_success, PayOnce.success] using
          (IndependentCounts.binomial (k + 1) (exclusiveProfileMarginal Γ d i) hb.1 hb.2).success_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hs0]
      exact PayOnce.success_le_one (k + 1) _ hb.2)
  change (∫ z, PayOnce.success (k + 1) (exclusiveProfileMarginal Γ z.1 z.2)
    ∂populationLaw (userProfileLaw Γ)) = _
  rw [integral_populationLaw _
    (fun d i => PayOnce.success (k + 1) (exclusiveProfileMarginal Γ d i)) hi]
  apply integral_congr_ae
  filter_upwards [ae_exclusive_profile_laws Γ hk B hB hsym hr j] with d hd
  unfold populationMean profileCoverage
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hd.1 i, IndependentCounts.binomial_success]
  rfl

theorem exclusiveMixture_support (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (B : PosteriorSystem Γ)
    (hB : ExclusiveOptimalOnPath Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hr : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = k + 1))
    (E : Set ℝ) (hout : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.1 ∉ E → x.2.routeCount = 0) :
    ∀ᵐ z ∂exclusiveMixture Γ, (z.1 z.2).1.1 ∉ E → exclusiveMixtureP Γ z = 0 := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let j : Fin (k + 1) := ⟨0, by omega⟩
  have hdraw := ae_all_iff.mpr fun i =>
    (profileAction_measurePreserving Γ i).quasiMeasurePreserving.ae hout
  apply ae_exclusiveMixture_of_all Γ
    (fun d i => (d i).1.1 ∉ E → exclusiveProfileMarginal Γ d i = 0)
  filter_upwards [ae_exclusive_profile_laws Γ hk B hB hsym hr j, hdraw] with d hd he
  intro i hi
  exact hd.2.2 i (he i hi)

theorem exclusiveMixture_mean_le_capacity (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (B : PosteriorSystem Γ)
    (hB : ExclusiveOptimalOnPath Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hr : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = k + 1)) :
    (∫ z, exclusiveMixtureP Γ z ∂exclusiveMixture Γ) ≤ (c : ℝ) / m := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let j : Fin (k + 1) := ⟨0, by omega⟩
  have hi := integrable_populationLaw_of_bound (userProfileLaw Γ)
    (exclusiveProfileMarginal Γ) (measurable_exclusiveProfileMarginal Γ)
    (C := 1) (fun d i => by
      have hb := exclusiveProfileMarginal_bounds Γ (by omega) d i
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2)
  change (∫ z, exclusiveProfileMarginal Γ z.1 z.2 ∂populationLaw (userProfileLaw Γ)) ≤ _
  rw [integral_populationLaw _ _ hi]
  calc
    _ ≤ ∫ _d, (c : ℝ) / m ∂userProfileLaw Γ := by
      apply integral_mono_ae
      · apply integrable_populationMean
        intro i
        exact UnitInterval.integrable _ _ (measurable_exclusiveProfileMarginal Γ i)
          (fun d => (exclusiveProfileMarginal_bounds Γ (by omega) d i).1)
          (fun d => (exclusiveProfileMarginal_bounds Γ (by omega) d i).2)
      · exact integrable_const _
      · filter_upwards [ae_exclusive_profile_laws Γ hk B hB hsym hr j] with d hd
        unfold populationMean
        rw [Fintype.card_fin, hd.2.1]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
        exact_mod_cast Nat.min_le_left c _
    _ = (c : ℝ) / m := by simp

theorem finite_exclusive_bounds (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (B : PosteriorSystem Γ)
    (hB : ExclusiveOptimalOnPath Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hr : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = k + 1))
    (E : Set ℝ) (hE : MeasurableSet E) (hh : 0 < Γ.F.real E)
    (hout : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.1 ∉ E → x.2.routeCount = 0) :
    finiteCoverage Γ ≤ Γ.F.real E * PayOnce.success (k + 1)
        (min ((c : ℝ) / ((m : ℝ) * Γ.F.real E)) 1) ∧
      ((k + 1 : ℕ) - 1 : ℝ) * (finiteCoverage Γ) ^ 2 /
        (((k + 1 : ℕ) : ℝ) ^ 2 * Γ.F.real E) ≤ finiteLoad Γ - finiteCoverage Γ := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let P := exclusiveMixture Γ
  let p := exclusiveMixtureP Γ
  let A : Set (UserProfile m (k + 1) × Fin m) := {z | (z.1 z.2).1.1 ∈ E}
  have hp : Measurable p := measurable_exclusiveMixtureP Γ
  have hp0 (z) : 0 ≤ p z := (exclusiveProfileMarginal_bounds Γ (by omega) z.1 z.2).1
  have hp1 (z) : p z ≤ 1 := (exclusiveProfileMarginal_bounds Γ (by omega) z.1 z.2).2
  have hA : MeasurableSet A := hE.preimage (measurable_from_prod_countable_left
    fun i => measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))
  have hmass : P.real A = Γ.F.real E := exclusiveMixture_value_mass Γ hm E hE
  have hz := exclusiveMixture_support Γ hk hm B hB hsym hr E hout
  have hmean := exclusiveMixture_mean_le_capacity Γ hk hm B hB hsym hr
  have hs := exclusiveMixture_success Γ hk hm B hB hsym hr
  have hl := exclusiveMixture_mean Γ hm (by omega)
  have hnR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  constructor
  · have h := Exclusive.supported_capacity_success_le P p hp hp0 hp1 A hA hz
      (k + 1) (div_nonneg (Nat.cast_nonneg c) (Nat.cast_nonneg m))
      (by rwa [hmass]) hmean
    rw [hmass, hs] at h
    simpa only [div_div] using h
  · have h := Exclusive.supported_coverage_quadratic P p hp hp0 hp1 A hA hz
      (k + 1) (by omega) (by rwa [hmass])
    rw [hmass, hs, hl, mul_div_cancel₀ _ hnR.ne'] at h
    exact h

end FCAppendix.Bayes
