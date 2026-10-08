import FCAppendix.PayOnce.ActualRareSurplus
import FCAppendix.PayOnce.ZeroAtomExclusion
import FCAppendix.PayOnce.RemoveZeroCutoff

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_excluded_surplus_limit
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
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
          {z | δ ≤ z.1-g-z.2.bid ∧ z.2.bid ≤ L}) atTop (𝓝 0) := by
  obtain ⟨L,hL,huniq⟩ := payOnce_rare_surplus_limit Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak
  refine ⟨L,⟨hL.1,hL.2.1,?_⟩,?_⟩
  · intro δ hδ
    have hz := payOnce_limit_no_zero_atom Γ hk hc hcm hN hA hG hu B hB hsym hatom
      F hF hg hactive hρ hρb hweak
    have hvalue t : PositiveValueAtomless (Γ t) := by
      intro v _
      rw [hF t]
      exact measure_singleton v
    have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t, hg t] using hactive)
    have hmap t : (bidLaw (Γ t) : Measure ENNReal) =
        ((Γ t).F ⊗ₘ (Γ t).σ).map (fun z => ENNReal.ofReal z.2.bid) := by
      rw [compactifiedBidLaw_eq_map_realBidLaw (Γ t) (by omega) ((hfull t).mono fun _ hz => hz.2),
        realBidLaw_eq_action_map, Measure.map_map ENNReal.measurable_ofReal
          (show Measurable (fun z : ℝ × JointAction (k+1) => z.2.bid) from
            (measurable_bid (k+1)).comp measurable_snd)]
      rfl
    apply tendsto_defect_mass_zero_of_away_zero (fun t => (Γ t).F ⊗ₘ (Γ t).σ)
      (fun _ z => z.2.bid) (fun _ => (measurable_bid (k+1)).comp measurable_snd)
      (fun t => bidLaw (Γ t)) G₀ hmap hweak hz
      (fun _ => {z | δ ≤ z.1-g-z.2.bid ∧ z.2.bid ≤ L})
    intro ε hε
    have he : {z : ℝ × JointAction (k+1) | δ ≤ z.1-g-z.2.bid ∧ z.2.bid ≤ L} ∩
        {z | ε ≤ z.2.bid} = {z | δ ≤ z.1-g-z.2.bid ∧ z.2.bid ∈ Icc ε L} := by
      ext z
      simp only [mem_inter_iff, mem_setOf_eq, mem_Icc]
      tauto
    simp_rw [he]
    exact hL.2.2 ε δ hε hδ
  · intro T hT
    have hroot := payOnce_positive_capacity_root Γ hk hc hcm
      ((tendsto_add_atTop_nat 1).comp hN) hA hG hu B hB hsym hatom F hF hg hactive
      (by simpa only [Nat.cast_add, Nat.cast_one] using hρ) hρb hweak
    obtain ⟨_,T₀,hT₀,huni⟩ := hroot
    exact (huni T ⟨hT.1,hT.2.1⟩).trans (huni L ⟨hL.1,hL.2.1⟩).symm

end FCAppendix.Bayes
