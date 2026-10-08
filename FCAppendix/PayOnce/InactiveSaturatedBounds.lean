import FCAppendix.PayOnce.SaturatedBounds
import FCAppendix.PayOnce.DummyFirstOrder

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce PayOnce.CompactifiedBidLaws
open scoped ProbabilityTheory BigOperators
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_inactive_mean_marginal_bound {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hvalue : PositiveValueAtomless Γ) (hatom : PositiveVisibleAtomless Γ)
    (hinactive : InactiveAbstain Γ) (i : Fin m)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ε ≤ effectiveBid x.2 → x.1-Γ.g ≤ R →
      (∫ rivals, DummyKernel.allocation (k+1) c (by omega) rivals (effectiveBid x.2)
        ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) ≤
          R*((k+1:ℕ):ℝ)^2/(ε+R*((k+1:ℕ):ℝ)^2) := by
  have hfoc := ae_inactive_payOnce_weighted_first_order Γ hk hc hcm hA hG hu B hB hsym hvalue hatom hinactive i
  have hpart := ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue
  filter_upwards [hfoc,hpart] with x hx hp hxb hxR
  have hv := hp.1.mp (hε.trans_le hxb)
  have he : effectiveBid x.2 = x.2.bid := by
    simp only [effectiveBid,hp.2.2 hv,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
  obtain ⟨weight,hw,hbound,_,_,hfirst⟩ := hx hv
  rw [← he] at hfirst
  exact RareSuccessSlope.mean_marginal_le_of_firstOrder
    (Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)))
    (by omega) (DummyKernel.measurable_allocation_rivals (by omega) (hε.trans_le hxb))
    hw (fun rivals => DummyKernel.allocation_bounds (by omega) rivals (effectiveBid x.2))
    hbound hε hxb hR hxR hfirst

end FCAppendix.Bayes
