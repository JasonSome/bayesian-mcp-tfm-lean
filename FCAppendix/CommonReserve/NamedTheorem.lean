import FCAppendix.CommonReserve.NamedEstimates
import FCAppendix.CommonReserve.MixedInterim
import FCAppendix.CommonReserve.IdentityAverage

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set Topology

variable {n : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) r Seed}
  {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
  {g ρ vstar : ℝ}

namespace SourceAssumptions

theorem mixed_limits (h : SourceAssumptions M C Γ F g ρ vstar)
    (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (Action n r))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ)
    (hv : v ≠ g + max r (vstar - g))
    (hν : ∀ k, ∀ᵐ a ∂ν k, ∀ b, (Γ k).purePayoff (i k) v b ≤
      (Γ k).purePayoff (i k) v a) :
    Tendsto (fun k => ((Γ k).mixedOutcome (i k) (ν k)).success) atTop
      (𝓝 (if g + max r (vstar - g) < v then 1 else 0)) ∧
    Tendsto (fun k => ∫ a, (Γ k).totalPayment (i k) a ∂ν k) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0)) := by
  let P : ℕ → InterimProblem (Action n r) := fun k => (Γ k).interim (i k)
  have hS k : Measurable (P k).success := (Γ k).measurable_success (i k)
  have hbr k : ∀ᵐ a ∂ν k, (P k).BestResponse v a := by
    filter_upwards [hν k] with a ha
    exact ((Γ k).interim_bestResponse (i k) v a).mpr ha
  have hU w : Tendsto (fun k => (P k).envelope w) atTop
      (𝓝 (max (w - (g + max r (vstar - g))) 0)) := by
    simpa only [P, FiniteGame.interim_envelope, sub_add_eq_sub_sub] using
      (h.utility_and_counts i).1 w
  constructor
  · have hs := InterimProblem.mixed_success_tendsto P ν hS
      (g + max r (vstar - g)) v hv hbr hU
    simpa only [P, FiniteGame.interim_success, ← FiniteGame.mixedOutcome_success] using hs
  · exact InterimProblem.mixed_cost_tendsto P ν hS
      (g + max r (vstar - g)) v hv hbr hU

omit [IsProbabilityMeasure F] [NullSingletonClass F] in
theorem ae_all_rows_optimal (h : SourceAssumptions M C Γ F g ρ vstar) :
    ∀ᵐ v ∂F, ∀ k (i : Fin (M k)), ∀ᵐ a ∂(Γ k).σ v,
      ∀ b, (Γ k).purePayoff i v b ≤ (Γ k).purePayoff i v a := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro i
  simpa only [h.law k] using h.optimal k i

theorem actual_limits (h : SourceAssumptions M C Γ F g ρ vstar) :
    ∀ᵐ v ∂F, ∀ (i : ∀ k, Fin (M k)),
      Tendsto (fun k => ((Γ k).typeOutcome (i k) v).success) atTop
        (𝓝 (if g + max r (vstar - g) < v then 1 else 0)) ∧
      Tendsto (fun k => ∫ a, (Γ k).totalPayment (i k) a ∂(Γ k).σ v) atTop
        (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0)) := by
  have hcut : ∀ᵐ v ∂F, v ≠ g + max r (vstar - g) := by
    rw [ae_iff]
    simp
  filter_upwards [h.ae_all_rows_optimal, hcut] with v hopt hv i
  exact h.mixed_limits i (fun k => (Γ k).σ v) v hv (fun k => hopt k (i k))

theorem aggregate_limits (h : SourceAssumptions M C Γ F g ρ vstar) :
    Tendsto (fun k => (Γ k).coverage) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))))) ∧
    Tendsto (fun k => (Γ k).load) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))))) ∧
    Tendsto (fun k => (Γ k).load - (Γ k).coverage) atTop (𝓝 0) := by
  have hQ : Tendsto (fun k => (Γ k).coverage) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))))) := by
    have hh := finite_average_tendsto_of_all_selections M h.users_pos
      (fun k i => ∫ v, ((Γ k).typeOutcome i v).success ∂F)
      (F.real (Ioi (g + max r (vstar - g))))
      (fun i => (h.utility_and_counts i).2.fst_nhds)
    simpa only [FiniteGame.coverage_eq_type_integrals, h.law] using hh
  have hL : Tendsto (fun k => (Γ k).load) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))))) := by
    have hh := finite_average_tendsto_of_all_selections M h.users_pos
      (fun k i => ∫ v, ((Γ k).typeOutcome i v).load ∂F)
      (F.real (Ioi (g + max r (vstar - g))))
      (fun i => (h.utility_and_counts i).2.snd_nhds.snd_nhds)
    simpa only [FiniteGame.load_eq_type_integrals, h.law] using hh
  exact ⟨hQ, hL, by simpa only [sub_self] using hL.sub hQ⟩

end SourceAssumptions

theorem common_reserve_named (h : SourceAssumptions M C Γ F g ρ vstar) :
    Conclusions M C Γ F g vstar := by
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
      (fun k => (Γ k).interim (i k)) (fun v => max (v - g - max r (vstar - g)) 0)
      (fun v => by simpa only [FiniteGame.interim_envelope] using hU i v) hK
    have he : (fun k => ((Γ k).interim (i k)).envelope) =
        (fun k v => (Γ k).envelope (i k) v) := by
      funext k v
      exact (Γ k).interim_envelope (i k) v
    rw [he] at hh
    exact hh
  · intro i v hv a hbr
    have hh := InterimProblem.bestResponse_success_tendsto
      (fun k => (Γ k).interim (i k)) (g + max r (vstar - g)) v hv a
      (fun k => ((Γ k).interim_bestResponse (i k) v (a k)).mpr (hbr k))
      (fun w => by simpa only [FiniteGame.interim_envelope, sub_add_eq_sub_sub] using hU i w)
    simpa only [FiniteGame.interim_success, NearPPI.cutoffSuccess, sub_pos] using hh
  · intro i v hv a hbr
    let ν : ℕ → Measure (Action n r) := fun k => Measure.dirac (a k)
    have hν k : ∀ᵐ b ∂ν k, ∀ d, (Γ k).purePayoff (i k) v d ≤
        (Γ k).purePayoff (i k) v b := by
      simpa only [ν, ae_dirac_eq, Filter.eventually_pure] using hbr k
    simpa only [ν, integral_dirac] using (h.mixed_limits i ν v hv hν).2
  · intro i ν _ v hv hν
    exact (h.mixed_limits i ν v hv hν).1
  · intro i ν _ v hν k
    apply (Γ k).integrable_totalPayment_of_bestResponse (i k) v (ν k)
    filter_upwards [hν k] with a ha'
    exact ((Γ k).interim_bestResponse (i k) v a).mpr ha'
  · intro i ν _ v hv hν
    exact (h.mixed_limits i ν v hv hν).2

theorem common_reserve_named_actual_payment
    (h : SourceAssumptions M C Γ F g ρ vstar)
    (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (Action n r))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ)
    (hv : v ≠ g + max r (vstar - g))
    (hν : ∀ k, ∀ᵐ a ∂ν k, ∀ b, (Γ k).purePayoff (i k) v b ≤
      (Γ k).purePayoff (i k) v a) :
    (∀ k, Integrable (fun p : Action n r × Sample (M k) n r Seed =>
      payment (FiniteGame.deviated (i k) p.1 p.2) (Γ k).policy p.2.2 (i k) +
        (Γ k).g * (Γ k).G.charge (count (FiniteGame.deviated (i k) p.1 p.2) (Γ k).policy p.2.2 (i k)))
      ((ν k).prod (Γ k).sampleLaw)) ∧
    Tendsto (fun k => ∫ p : Action n r × Sample (M k) n r Seed,
      payment (FiniteGame.deviated (i k) p.1 p.2) (Γ k).policy p.2.2 (i k) +
        (Γ k).g * (Γ k).G.charge (count (FiniteGame.deviated (i k) p.1 p.2) (Γ k).policy p.2.2 (i k))
      ∂(ν k).prod (Γ k).sampleLaw) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0)) := by
  have hbr k : ∀ᵐ a ∂ν k, ((Γ k).interim (i k)).BestResponse v a := by
    filter_upwards [hν k] with a ha
    exact ((Γ k).interim_bestResponse (i k) v a).mpr ha
  have hi k := (Γ k).integrable_mixed_payment_integrand (i k) v (ν k) (hbr k)
  refine ⟨hi, ?_⟩
  have he k : (∫ p : Action n r × Sample (M k) n r Seed,
      payment (FiniteGame.deviated (i k) p.1 p.2) (Γ k).policy p.2.2 (i k) +
        (Γ k).g * (Γ k).G.charge (count (FiniteGame.deviated (i k) p.1 p.2) (Γ k).policy p.2.2 (i k))
      ∂(ν k).prod (Γ k).sampleLaw) = ∫ a, (Γ k).totalPayment (i k) a ∂ν k :=
    integral_prod _ (hi k)
  simpa only [he] using (h.mixed_limits i ν v hv hν).2

end FCAppendix.CommonReserve
