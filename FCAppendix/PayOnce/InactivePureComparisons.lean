import FCAppendix.PayOnce.EffectiveVanishingBid
import FCAppendix.PayOnce.DummyInterimTransport

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce.DummyKernel PayOnce.CompactifiedBidLaws
variable {N c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_monotone_effective_analytical_IC (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < N+1)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hvalue : PositiveValueAtomless Γ) (hinactive : InactiveAbstain Γ) :
    ∃ bid : ℝ → ℝ, Monotone bid ∧ Measurable bid ∧
      (∀ v, 0 ≤ bid v ∧ bid v ≤ max (v-Γ.g) 0) ∧
      (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) = Γ.F.map bid ∧
      (∀ᵐ z ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid z.2 = bid z.1) ∧
      ∃ T : Set ℝ, (∀ᵐ v ∂Γ.F, Γ.g < v → v ∈ T) ∧
        ∀ v ∈ T, 0 < bid v ∧ ∀ w ∈ T,
          (v-Γ.g-bid w) * coverage (k+1) c (by omega)
            (Measure.pi (fun _ : Fin N => Γ.F.map bid)) (bid w) ≤
          (v-Γ.g-bid v) * coverage (k+1) c (by omega)
            (Measure.pi (fun _ : Fin N => Γ.F.map bid)) (bid v) := by
  obtain ⟨bid,hmono,hmeas,hbound,heq,hprop⟩ := exists_monotone_effective_bid_bestResponse_all Γ hk hc hcm
    hA hG hu B hB hsym hvalue hinactive
  have hraw := realEffectiveBidLaw_eq_pure_map Γ bid hmeas heq
  have hroute := ae_positive_broadcast_or_abstain Γ hc hcm hA hG hu B hB hsym hvalue hinactive
  let i : Fin (N+1) := ⟨0,by omega⟩
  obtain ⟨S,hSm,hS,_,hagree⟩ := exists_common_dummy_agreement_set Γ hk hA B hB hsym hroute i
  rw [hraw] at hS
  have hSa : ∀ᵐ v ∂Γ.F, 0 < bid v → bid v ∈ S := ae_of_ae_map hmeas.aemeasurable hS
  let T := {v | 0 < bid v ∧ (problem Γ i).BestResponse v (safeFullBid (k+1) (bid v)) ∧ bid v ∈ S}
  have hTa : ∀ᵐ v ∂Γ.F, Γ.g < v → v ∈ T := by
    filter_upwards [hprop,hSa] with v hv hs hpos
    exact ⟨(hv hpos).1,(hv hpos).2.2.1 i,hs (hv hpos).1⟩
  have hcard : Fintype.card (Fin N) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin N ≃ Rival i := Fintype.equivOfCardEq hcard
  have hQ b : coverage (k+1) c (by omega)
      (Measure.pi (fun _ : Fin N => Γ.F.map bid)) b =
      coverage (k+1) c (by omega)
        (Measure.pi (fun _ : Rival i => (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ))) b := by
    rw [← hraw]
    exact integral_allocation_test_equiv e (by omega) (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) b
      (PayOnce.success (k+1))
  refine ⟨bid, hmono, hmeas, hbound, hraw, heq, T, hTa, ?_⟩
  intro v hv
  refine ⟨hv.1, ?_⟩
  intro w hw
  have hbval t : (safeFullBid (k+1) (bid t)).bid = bid t := max_eq_left (hbound t).1
  have hrval t : (safeFullBid (k+1) (bid t)).routeCount = k+1 := rfl
  have hqv := hagree (bid v) hv.2.2 (safeFullBid (k+1) (bid v)) (hbval v) (hrval v)
  have hqw := hagree (bid w) hw.2.2 (safeFullBid (k+1) (bid w)) (hbval w) (hrval w)
  have hic := hv.2.1 (safeFullBid (k+1) (bid w))
  rw [payoff_once Γ hA hG, payoff_once Γ hA hG, hbval, hbval, hqw, hqv, ← hQ, ← hQ] at hic
  convert hic using 1 <;> ring

end FCAppendix.Bayes
