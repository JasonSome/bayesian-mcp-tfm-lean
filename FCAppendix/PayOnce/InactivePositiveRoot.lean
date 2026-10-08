import FCAppendix.PayOnce.PositiveRoot
import FCAppendix.PayOnce.InactiveSaturatedLimit
import FCAppendix.PayOnce.InactiveBidFloor

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce
open scoped ProbabilityTheory

theorem payOnce_inactive_positive_capacity_root
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G)) :
    ρ < (G : Measure ENNReal).real ({0}ᶜ) ∧
      ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G : Measure ENNReal) L = ρ := by
  have hm t := (hc t).trans (hcm t)
  have hinfty := CompactifiedBidLaws.equilibrium_limit_no_infinity Γ hm hc
    (fun t => posterior_isAEEquilibrium (Γ t) (hu t) (B t) (hB t)) F hF hweak
  have hne : G ≠ (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ENNReal) := by
    intro he
    exact payOnce_inactive_not_weak_zero Γ hk hc hcm hM hA hG hu B hB hsym hvalue hatom hinactive
      F hF hg hρ hρb (he ▸ hweak)
  apply KernelDemand.exists_root_of_no_saturated_tails (by omega) G hρb.1 hinfty hne
  intro L hL hD
  exact inactive_limit_saturated_tail_zero Γ hk hc hcm hM hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hweak hρ hρb.2.le hL hD

end FCAppendix.Bayes
