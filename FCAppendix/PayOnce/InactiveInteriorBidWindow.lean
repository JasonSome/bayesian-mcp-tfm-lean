import FCAppendix.PayOnce.InteriorBidBlock
import FCAppendix.PayOnce.InactiveClosedSaturatedTail
import FCAppendix.PayOnce.InactivePositiveRoot

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce

theorem payOnce_inactive_interior_bid_window
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
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G)) :
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G : Measure ENNReal) L = ρ ∧
      (G : Measure ENNReal) (Ici (ENNReal.ofReal (((k+1:ℕ):ℝ)*L))) = 0 ∧
      ∃ a b : ℝ, L < a ∧ a < b ∧ b < ((k+1:ℕ):ℝ)*L ∧
        0 < (G : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)) := by
  obtain ⟨_,L,hL,huniq⟩ := payOnce_inactive_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρ hρb hweak
  have hsat := inactive_limit_closed_saturated_tail_zero Γ hk hc hcm hM hA hG hu B hB hsym
    hvalue hatom hinactive F hF hg hweak hρ hρb.2.le hL.1 hL.2
  refine ⟨L,⟨hL.1,hL.2,hsat,?_⟩,fun T hT => huniq T ⟨hT.1,hT.2.1⟩⟩
  exact KernelDemand.exists_interior_bid_window (by omega) G hL.1 hρb.1 hL.2 hsat

end FCAppendix.Bayes
