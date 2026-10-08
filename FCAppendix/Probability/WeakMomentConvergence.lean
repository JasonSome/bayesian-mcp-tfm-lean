import FCAppendix.Probability.L1WeakConvergence

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem integral_tendsto_of_tendstoInDistribution
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)]
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : (t : ℕ) → Ω t → ℝ) (Z : Ω' → ℝ)
    (hweak : TendstoInDistribution X atTop Z μ ν)
    (hLp : ∀ t, MemLp (X t) 2 (μ t)) (hZ : MemLp Z 2 ν)
    (K : ℝ) (hK : ∀ᶠ t in atTop, (∫ ω, (X t ω)^2 ∂μ t) ≤ K) :
    Tendsto (fun t => ∫ ω, X t ω ∂μ t) atTop (𝓝 (∫ ω, Z ω ∂ν)) := by
  let laws : ℕ → ProbabilityMeasure ℝ := fun t =>
    ⟨(μ t).map (X t),Measure.isProbabilityMeasure_map (hweak.forall_aemeasurable t)⟩
  let lawZ : ProbabilityMeasure ℝ :=
    ⟨ν.map Z,Measure.isProbabilityMeasure_map hweak.aemeasurable_limit⟩
  have hLp' t : MemLp (fun x : ℝ => x) 2 (laws t : Measure ℝ) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hweak.forall_aemeasurable t)).mpr (hLp t)
  have hZ' : MemLp (fun x : ℝ => x) 2 (lawZ : Measure ℝ) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hweak.aemeasurable_limit).mpr hZ
  obtain ⟨T,hT⟩ := eventually_atTop.mp hK
  have hh := probabilityMeasure_mean_tendsto_of_secondMoment_bound (fun t => laws (t+T)) lawZ
    (hweak.tendsto.comp (tendsto_add_atTop_nat T)) (fun t => hLp' (t+T)) hZ' K (by
      intro t
      change (∫ x : ℝ, x^2 ∂(μ (t+T)).map (X (t+T))) ≤ K
      rw [integral_map (hweak.forall_aemeasurable _) (by fun_prop)]
      exact hT (t+T) (by omega))
  have hh' : Tendsto (fun t => ∫ x : ℝ, x ∂(laws t : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x ∂(lawZ : Measure ℝ))) :=
    (tendsto_add_atTop_iff_nat T).mp hh
  change Tendsto (fun t => ∫ x : ℝ, x ∂(μ t).map (X t)) atTop
    (𝓝 (∫ x : ℝ, x ∂ν.map Z)) at hh'
  have he : (fun t => ∫ x : ℝ, x ∂(μ t).map (X t)) = (fun t => ∫ ω, X t ω ∂μ t) := by
    funext t
    exact integral_map (hweak.forall_aemeasurable t) aestronglyMeasurable_id
  have hz : (∫ x : ℝ, x ∂ν.map Z) = ∫ ω, Z ω ∂ν :=
    integral_map hweak.aemeasurable_limit aestronglyMeasurable_id
  rw [he,hz] at hh'
  exact hh'

theorem moment_tendsto_of_tendstoInDistribution
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)]
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : (t : ℕ) → Ω t → ℝ) (Z : Ω' → ℝ)
    (hweak : TendstoInDistribution X atTop Z μ ν) (j : ℕ)
    (hLp : ∀ t, MemLp (fun ω => (X t ω)^j) 2 (μ t))
    (hZ : MemLp (fun ω => (Z ω)^j) 2 ν)
    (K : ℝ) (hK : ∀ᶠ t in atTop, (∫ ω, (X t ω)^(2*j) ∂μ t) ≤ K) :
    Tendsto (fun t => ∫ ω, (X t ω)^j ∂μ t) atTop (𝓝 (∫ ω, (Z ω)^j ∂ν)) := by
  apply integral_tendsto_of_tendstoInDistribution μ ν _ _
    (hweak.continuous_comp (g := fun x : ℝ => x^j) (by fun_prop)) hLp hZ K
  simpa only [Function.comp_def,← pow_mul,Nat.mul_comm j 2] using hK

end FCAppendix.Probability
