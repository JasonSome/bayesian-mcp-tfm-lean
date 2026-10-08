import FCAppendix.PayOnce.InactiveRareSurplus
import FCAppendix.PayOnce.InactiveZeroAtomExclusion
import FCAppendix.PayOnce.RemoveFixedZeroAtom

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_excluded_surplus_limit
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀)) :
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
          {z | δ ≤ z.1-g-effectiveBid z.2 ∧ effectiveBid z.2 ≤ L}) atTop (𝓝 0) := by
  obtain ⟨L,hL,huniq⟩ := payOnce_inactive_rare_surplus_limit Γ hk hc hcm hN hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρ hρb hweak
  refine ⟨L,⟨hL.1,hL.2.1,?_⟩,?_⟩
  · intro δ hδ
    have hz := payOnce_inactive_limit_zero_atom Γ hk hc hcm hN hA hG hu B hB hsym hvalue hatom hinactive
      F hF hg hρ hρb hweak
    have hzero t : (bidLaw (Γ t) : Measure ENNReal) {0} = (G₀ : Measure ENNReal) {0} := by
      rw [hz,compactifiedBidLaw_zero_mass (Γ t) (hc t) (hcm t) (hA t) (hG t)
        (hu t) (B t) (hB t) (hsym t) (hvalue t),hF t,hg t]
    have hmap t : (bidLaw (Γ t) : Measure ENNReal) =
        ((Γ t).F ⊗ₘ (Γ t).σ).map (fun z => ENNReal.ofReal (effectiveBid z.2)) := by
      rw [compactifiedBidLaw_eq_map_effectiveBidLaw (Γ t),
        realEffectiveBidLaw_eq_action_map, Measure.map_map ENNReal.measurable_ofReal
          (show Measurable (fun z : ℝ × JointAction (k+1) => effectiveBid z.2) from
            (measurable_effectiveBid (k+1)).comp measurable_snd)]
      rfl
    refine tendsto_defect_mass_zero_of_away_zero_fixed_atom (fun t => (Γ t).F ⊗ₘ (Γ t).σ)
      (fun _ z => effectiveBid z.2) (fun _ => (measurable_effectiveBid (k+1)).comp measurable_snd)
      (fun t => bidLaw (Γ t)) G₀ hmap hweak hzero
      (fun _ => {z | δ ≤ z.1-g-effectiveBid z.2 ∧ effectiveBid z.2 ≤ L})
      ?_ ?_
    · intro t
      filter_upwards [ae_effectiveBid_participation (Γ t) (hc t) (hcm t) (hA t) (hG t)
        (hu t) (B t) (hB t) (hsym t) (hvalue t)] with z hp hz
      apply hp.1.mpr
      rw [hg t]
      have hh : δ ≤ z.1-g-effectiveBid z.2 := hz.1
      linarith [effectiveBid_nonneg z.2]
    · intro ε hε
      have he : {z : ℝ × JointAction (k+1) | δ ≤ z.1-g-effectiveBid z.2 ∧ effectiveBid z.2 ≤ L} ∩
          {z | ε ≤ effectiveBid z.2} = {z | δ ≤ z.1-g-effectiveBid z.2 ∧ effectiveBid z.2 ∈ Icc ε L} := by
        ext z
        simp only [mem_inter_iff, mem_setOf_eq, mem_Icc]
        tauto
      simp_rw [he]
      exact hL.2.2 ε δ hε hδ
  · intro T hT
    have hroot := payOnce_inactive_positive_capacity_root Γ hk hc hcm
      ((tendsto_add_atTop_nat 1).comp hN) hA hG hu B hB hsym hvalue hatom hinactive F hF hg
      (by simpa only [Nat.cast_add, Nat.cast_one] using hρ) hρb hweak
    obtain ⟨_,T₀,hT₀,huni⟩ := hroot
    exact (huni T ⟨hT.1,hT.2.1⟩).trans (huni L ⟨hL.1,hL.2.1⟩).symm

end FCAppendix.Bayes
