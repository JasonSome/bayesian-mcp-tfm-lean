import FCAppendix.CommonReserve.AnonymousEstimates
import FCAppendix.CommonReserve.AnonymousIntegrability
import FCAppendix.CommonReserve.AnonymousAcceptance
import FCAppendix.CommonReserve.IdentityAverage

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem anonymous_coverage_eq_type_integrals (Γ : Bayes.FiniteGame m n c Seed) (hm : 0 < m) :
    Bayes.finiteCoverage Γ = (∑ i, ∫ v, (Bayes.typeOutcome Γ i v).success ∂Γ.F) / m := by
  have he := Bayes.integral_conditionalTypeCountLaw_success Γ hm
  simp only [CountLaw.success, Bayes.conditionalTypeCountLaw, FiniteLaw.expect_uniformAverage] at he
  rw [integral_div, integral_finsetSum _
    (fun i _ => Bayes.integrable_typeOutcome_expect Γ i Γ.F _)] at he
  exact he.symm

theorem anonymous_load_eq_type_integrals (Γ : Bayes.FiniteGame m n c Seed) (hm : 0 < m) :
    Bayes.finiteLoad Γ = (∑ i, ∫ v, (Bayes.typeOutcome Γ i v).load ∂Γ.F) / m := by
  have he := Bayes.integral_conditionalTypeCountLaw_load Γ hm
  simp only [CountLaw.load, Bayes.conditionalTypeCountLaw, FiniteLaw.expect_uniformAverage] at he
  rw [integral_div, integral_finsetSum _
    (fun i _ => Bayes.integrable_typeOutcome_expect Γ i Γ.F _)] at he
  exact he.symm

variable {M C : ℕ → ℕ} {Γ : ∀ k, Bayes.FiniteGame (M k) n (C k) Seed}
  {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
  {g r ρ vstar : ℝ}

namespace AnonymousSourceAssumptions

theorem mixed_limits (h : AnonymousSourceAssumptions M C Γ F g r ρ vstar)
    (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ)
    (hv : v ≠ g + max r (vstar - g))
    (hν : ∀ k, ∀ᵐ a ∂ν k, (Bayes.problem (Γ k) (i k)).BestResponse v a) :
    Tendsto (fun k => (Bayes.mixedCountLaw (Γ k) (i k) (ν k)).success) atTop
      (𝓝 (if g + max r (vstar - g) < v then 1 else 0)) ∧
    Tendsto (fun k => ∫ a, anonymousCost (Γ k) (i k) a ∂ν k) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0)) := by
  let P : ℕ → InterimProblem (JointAction n) := fun k =>
    anonymousInterim (Γ k) r h.reserve_nonneg (h.uniform_ties k) (i k)
  have hS k : Measurable (P k).success := Bayes.measurable_outcome_expect (Γ k) (i k) _
  have hbr k : ∀ᵐ a ∂ν k, (P k).BestResponse v a := by
    filter_upwards [hν k] with a ha
    exact (anonymousInterim_bestResponse (Γ k) r h.reserve_nonneg
      (h.uniform_ties k) (i k) v a).mpr ha
  have hU w : Tendsto (fun k => (P k).envelope w) atTop
      (𝓝 (max (w - (g + max r (vstar - g))) 0)) := by
    simpa only [P, anonymousInterim_envelope, sub_add_eq_sub_sub] using
      (h.utility_and_counts i).1 w
  constructor
  · have hs := InterimProblem.mixed_success_tendsto P ν hS
      (g + max r (vstar - g)) v hv hbr hU
    simpa only [P, anonymousInterim, CountLaw.success, Bayes.mixedCountLaw_expect] using hs
  · exact InterimProblem.mixed_cost_tendsto P ν hS
      (g + max r (vstar - g)) v hv hbr hU

theorem actual_limits (h : AnonymousSourceAssumptions M C Γ F g r ρ vstar) :
    ∀ᵐ v ∂F, ∀ (i : ∀ k, Fin (M k)),
      Tendsto (fun k => (Bayes.typeOutcome (Γ k) (i k) v).success) atTop
        (𝓝 (if g + max r (vstar - g) < v then 1 else 0)) ∧
      Tendsto (fun k => ∫ a, anonymousCost (Γ k) (i k) a ∂(Γ k).σ v) atTop
        (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0)) := by
  have hcut : ∀ᵐ v ∂F, v ≠ g + max r (vstar - g) := by
    rw [ae_iff]
    simp
  filter_upwards [Bayes.ae_all_rows_bestResponse M C Γ F h.law h.optimal, hcut]
    with v hopt hv i
  simpa only [Bayes.mixedCountLaw_strategy_eq_typeOutcome] using
    h.mixed_limits i (fun k => (Γ k).σ v) v hv (fun k => hopt k (i k))

theorem aggregate_limits (h : AnonymousSourceAssumptions M C Γ F g r ρ vstar) :
    Tendsto (fun k => Bayes.finiteCoverage (Γ k)) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))))) ∧
    Tendsto (fun k => Bayes.finiteLoad (Γ k)) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))))) ∧
    Tendsto (fun k => Bayes.finiteLoad (Γ k) - Bayes.finiteCoverage (Γ k)) atTop (𝓝 0) := by
  have hQ : Tendsto (fun k => Bayes.finiteCoverage (Γ k)) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))))) := by
    have hh := finite_average_tendsto_of_all_selections M h.users_pos
      (fun k i => ∫ v, (Bayes.typeOutcome (Γ k) i v).success ∂F)
      (F.real (Ioi (g + max r (vstar - g))))
      (fun i => (h.utility_and_counts i).2.fst_nhds)
    simpa only [anonymous_coverage_eq_type_integrals (Γ _) (h.users_pos _), h.law] using hh
  have hL : Tendsto (fun k => Bayes.finiteLoad (Γ k)) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))))) := by
    have hh := finite_average_tendsto_of_all_selections M h.users_pos
      (fun k i => ∫ v, (Bayes.typeOutcome (Γ k) i v).load ∂F)
      (F.real (Ioi (g + max r (vstar - g))))
      (fun i => (h.utility_and_counts i).2.snd_nhds.snd_nhds)
    simpa only [anonymous_load_eq_type_integrals (Γ _) (h.users_pos _), h.law] using hh
  exact ⟨hQ, hL, by simpa only [sub_self] using hL.sub hQ⟩

end AnonymousSourceAssumptions

theorem common_reserve_anonymous
    (h : AnonymousSourceAssumptions M C Γ F g r ρ vstar) :
    AnonymousConclusions M C Γ F g r vstar := by
  have hU := fun i => (h.utility_and_counts i).1
  have ha := h.actual_limits
  have hagg := h.aggregate_limits
  refine {
    utility := hU
    utility_compact := ?_
    fixed_success := ?_
    fixed_payment := ?_
    mixed_success := ?_
    mixed_payment_integrable := ?_
    mixed_payment := ?_
    actual_success := ha.mono (fun v hv i => (hv i).1)
    actual_payment := ha.mono (fun v hv i => (hv i).2)
    coverage := hagg.1
    load := hagg.2.1
    duplicates := hagg.2.2 }
  · intro i K hK
    have hh := InterimProblem.envelope_uniformOn_compact
      (fun k => anonymousInterim (Γ k) r h.reserve_nonneg (h.uniform_ties k) (i k))
      (fun v => max (v - g - max r (vstar - g)) 0)
      (fun v => by simpa only [anonymousInterim_envelope] using hU i v) hK
    have he : (fun k =>
        (anonymousInterim (Γ k) r h.reserve_nonneg (h.uniform_ties k) (i k)).envelope) =
        (fun k v => (Bayes.problem (Γ k) (i k)).envelope v) := by
      funext k v
      exact anonymousInterim_envelope (Γ k) r h.reserve_nonneg (h.uniform_ties k) (i k) v
    rw [he] at hh
    exact hh
  · intro i v hv a hbr
    have hh := InterimProblem.bestResponse_success_tendsto
      (fun k => anonymousInterim (Γ k) r h.reserve_nonneg (h.uniform_ties k) (i k))
      (g + max r (vstar - g)) v hv a
      (fun k => (anonymousInterim_bestResponse (Γ k) r h.reserve_nonneg
        (h.uniform_ties k) (i k) v (a k)).mpr (hbr k))
      (fun w => by simpa only [anonymousInterim_envelope, sub_add_eq_sub_sub] using hU i w)
    simpa only [anonymousInterim, NearPPI.cutoffSuccess, sub_pos] using hh
  · intro i v hv a hbr
    let ν : ℕ → Measure (JointAction n) := fun k => Measure.dirac (a k)
    have hν k : ∀ᵐ b ∂ν k, (Bayes.problem (Γ k) (i k)).BestResponse v b := by
      simpa only [ν, ae_dirac_eq, Filter.eventually_pure] using hbr k
    simpa only [ν, integral_dirac] using (h.mixed_limits i ν v hv hν).2
  · intro i ν _ v hv hν
    exact (h.mixed_limits i ν v hv hν).1
  · intro i ν _ v hν k
    exact integrable_anonymousCost_of_bestResponse (Γ k) r h.reserve_nonneg
      (h.uniform_ties k) (i k) v (ν k) (hν k)
  · intro i ν _ v hv hν
    exact (h.mixed_limits i ν v hv hν).2

theorem common_reserve_anonymous_actual_payment
    (h : AnonymousSourceAssumptions M C Γ F g r ρ vstar)
    (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ)
    (hv : v ≠ g + max r (vstar - g))
    (hν : ∀ k, ∀ᵐ a ∂ν k, (Bayes.problem (Γ k) (i k)).BestResponse v a) :
    (∀ k, Integrable (anonymousActualPayment (Γ k) (i k))
      ((ν k).prod (Bayes.sampleLaw (Γ k)))) ∧
    Tendsto (fun k => ∫ p, anonymousActualPayment (Γ k) (i k) p
      ∂(ν k).prod (Bayes.sampleLaw (Γ k))) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0)) := by
  refine ⟨fun k => integrable_anonymousActualPayment_of_bestResponse (Γ k) r
    h.reserve_nonneg (h.uniform_ties k) (i k) v (ν k) (hν k), ?_⟩
  have hh := (h.mixed_limits i ν v hv hν).2
  exact hh.congr fun k => (anonymous_mixed_actual_payment_eq_cost (Γ k) r
    h.reserve_nonneg (h.uniform_ties k) (i k) v (ν k) (hν k)).symm

end FCAppendix.CommonReserve
