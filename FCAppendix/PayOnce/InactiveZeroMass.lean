import FCAppendix.PayOnce.EffectiveVanishingBid

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem compactifiedBidLaw_zero_mass (Γ : FiniteGame m (k+1) c Seed)
    (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ) :
    (bidLaw Γ : Measure ENNReal) {0} = Γ.F (Iic Γ.g) := by
  rw [compactifiedBidLaw_eq_map_effectiveBidLaw,
    Measure.map_apply ENNReal.measurable_ofReal (measurableSet_singleton 0)]
  calc
    _ = (BidScaling.realBidLaw Γ : Measure ℝ) {0} := by
      apply measure_congr
      filter_upwards [ae_realEffectiveBidLaw_nonneg Γ] with b hb
      change (ENNReal.ofReal b = 0) = (b = 0)
      apply propext
      rw [ENNReal.ofReal_eq_zero]
      exact ⟨fun h => le_antisymm h hb, fun h => h.le⟩
    _ = _ := realEffectiveBidLaw_zero_mass Γ hc hcm hA hG hu B hB hsym hvalue

theorem inactive_mass_le_limit_zero_mass {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hvalue : ∀ t, PositiveValueAtomless (Γ t))
    (F : Measure ℝ) (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G)) :
    F (Iic g) ≤ (G : Measure ENNReal) {0} := by
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak (isClosed_singleton (x := (0:ENNReal)))
  have he t : (bidLaw (Γ t) : Measure ENNReal) {0} = F (Iic g) := by
    rw [compactifiedBidLaw_zero_mass (Γ t) (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t), hF t, hg t]
  simpa only [he, limsup_const] using hh

end FCAppendix.Bayes
