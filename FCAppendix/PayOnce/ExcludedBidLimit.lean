import FCAppendix.PayOnce.MonotoneExcludedBids

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_excluded_bid_limit
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) 1) {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀)) :
    ∃ L : ℝ, 0 < L ∧ KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
        (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
        (∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), z.2.bid = b t z.1) ∧
        ∀ᵐ v ∂F, g < v → v-g ≤ L → Tendsto (fun t => b t v) atTop (𝓝 (v-g)) := by
  obtain ⟨L,hL,_⟩ := payOnce_excluded_surplus_limit Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  choose b hmono hmeas hbound hraw heq T hTa hT using fun t =>
    exists_monotone_analytical_IC (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t, hg t] using hactive)
  have hb t v : 0 ≤ b t v ∧ b t v ≤ max (v-g) 0 := by simpa only [hg t] using hbound t v
  refine ⟨L,hL.1,hL.2.1,b,hmono,hmeas,hb,heq,?_⟩
  apply VanishingBidIC.ae_excluded_bid_limit_of_surplus_mass F b hmono (fun t v => (hb t v).2)
  intro δ hδ
  have hmass := hL.2.2 δ hδ
  apply hmass.congr
  intro t
  let E := {v : ℝ | δ ≤ v-g-b t v ∧ b t v ≤ L}
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_const ((measurable_id.sub_const g).sub (hmeas t))).inter
      (measurableSet_le (hmeas t) measurable_const)
  calc
    ((Γ t).F ⊗ₘ (Γ t).σ) {z | δ ≤ z.1-g-z.2.bid ∧ z.2.bid ≤ L} =
        ((Γ t).F ⊗ₘ (Γ t).σ) (Prod.fst ⁻¹' E) := by
      apply measure_congr
      filter_upwards [heq t] with z hz
      change (δ ≤ z.1-g-z.2.bid ∧ z.2.bid ≤ L) = (δ ≤ z.1-g-b t z.1 ∧ b t z.1 ≤ L)
      rw [hz]
    _ = F E := by rw [← Measure.fst_apply hE, Measure.fst_compProd, hF t]

end FCAppendix.Bayes
