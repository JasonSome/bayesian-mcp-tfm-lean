import FCAppendix.PayOnce.DummyInterimMean
import FCAppendix.PayOnce.InactiveSourceCentering

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_type_mean_uniform_response_error
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t in atTop, ∀ᵐ v ∂F, ∀ i : Fin (M t),
      |(typeOutcome (Γ t) i v).load/((k+1:ℕ):ℝ)-
        Limit.pStar (k+1) (bar t) (max (v-g) 0)| ≤ D*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  obtain ⟨b,_hmono,_hmeas,_hbound,heq,_hlim,D,hD,herr⟩ :=
    payOnce_inactive_uniform_response_error Γ B F g ρ h hlocal
  refine ⟨D,hD,?_⟩
  filter_upwards [herr,payOnce_inactive_eventual_type_mean Γ B F g ρ h b heq]
    with t ht hmean
  filter_upwards [ht,hmean] with v hv hm
  intro i
  rw [hm i]
  exact hv

theorem payOnce_inactive_ae_type_mean_response_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∀ᵐ v ∂F, ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i : Fin (M t),
      |sqrt (M t:ℝ)*((typeOutcome (Γ t) i v).load/((k+1:ℕ):ℝ)-
        Limit.pStar (k+1) (bar t) (max (v-g) 0))| < ε := by
  dsimp only
  obtain ⟨_hL,_hd,b,_hmono,_hmeas,_hbound,heq,hlim⟩ :=
    payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  have hmean := payOnce_inactive_eventual_type_mean Γ B F g ρ h b heq
  obtain ⟨T,hT⟩ := eventually_atTop.mp hmean
  have hall := ae_all_iff.mpr (fun t => ae_all_iff.mpr (fun ht : T ≤ t => hT t ht))
  filter_upwards [hall,payOnce_inactive_ae_response_error_sqrt Γ B F g ρ h hlocal b heq hlim]
    with v hv hlimv
  intro ε hε
  filter_upwards [eventually_ge_atTop T,(Metric.tendsto_nhds.mp hlimv) ε hε] with t ht he
  intro i
  rw [hv t ht i]
  simpa only [Real.dist_eq,sub_zero] using he

theorem payOnce_inactive_type_mean_response_sqrt_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∀ᵐ v ∂F, ∀ i : ∀ t, Fin (M t), Tendsto (fun t =>
      sqrt (M t:ℝ)*((typeOutcome (Γ t) (i t) v).load/((k+1:ℕ):ℝ)-
        Limit.pStar (k+1) (bar t) (max (v-g) 0))) atTop (𝓝 0) := by
  dsimp only
  filter_upwards [payOnce_inactive_ae_type_mean_response_sqrt Γ B F g ρ h hlocal] with v hv
  intro i
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hv ε hε] with t ht
  simpa only [Real.dist_eq,sub_zero] using ht (i t)

end FCAppendix.Bayes
