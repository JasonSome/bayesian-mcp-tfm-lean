import FCAppendix.PayOnce.ActualScaledComparisons
import FCAppendix.PayOnce.VanishingBidIC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce.AnalyticalKernel
variable {N c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_monotone_analytical_IC (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < N+1)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hvalue : PositiveValueAtomless Γ) (hactive : ∀ᵐ v ∂Γ.F, Γ.g < v) :
    ∃ bid : ℝ → ℝ, Monotone bid ∧ Measurable bid ∧
      (∀ v, 0 ≤ bid v ∧ bid v ≤ max (v-Γ.g) 0) ∧
      realBidLaw Γ = Γ.F.map bid ∧
      (∀ᵐ z ∂(Γ.F ⊗ₘ Γ.σ), z.2.bid = bid z.1) ∧
      ∃ T : Set ℝ, (∀ᵐ v ∂Γ.F, v ∈ T) ∧
        ∀ v ∈ T, 0 < bid v ∧ ∀ w ∈ T,
          (v-Γ.g-bid w) * coverage (k+1) c (by omega) (by simpa using hcm.le)
            (Measure.pi (fun _ : Fin N => Γ.F.map bid)) (bid w) ≤
          (v-Γ.g-bid v) * coverage (k+1) c (by omega) (by simpa using hcm.le)
            (Measure.pi (fun _ : Fin N => Γ.F.map bid)) (bid v) := by
  obtain ⟨bid, hmono, hmeas, hbound, hprop⟩ := exists_monotone_bid_bestResponse_all Γ hk hc hcm
    hA hG hu B hB hsym hvalue hactive
  have hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid (k+1) (bid v) :=
    hprop.mono fun _ hv => hv.2.2.2
  have hraw := realBidLaw_eq_map_of_pure Γ bid hmeas (fun v => (hbound v).1) hpure
  have heq : ∀ᵐ z ∂(Γ.F ⊗ₘ Γ.σ), z.2.bid = bid z.1 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun ((measurable_bid (k+1)).comp measurable_snd) (hmeas.comp measurable_fst))
    filter_upwards [hpure] with v hv
    filter_upwards [hv] with a ha
    change a.bid = bid v
    rw [ha]
    exact max_eq_left (hbound v).1
  have hfull := ae_full_routes_positive_bids_of_active Γ hc hcm hA hG hu B hB hsym hvalue hactive
  let i : Fin (N+1) := ⟨0, by omega⟩
  obtain ⟨S, hSm, hS, _, hagree⟩ := exists_common_analytical_agreement_set Γ hk hcm.le hA B hB hsym
    (hfull.mono fun _ hz => hz.2) (hfull.mono fun _ hz => hz.1) i
  rw [hraw] at hS
  have hSa : ∀ᵐ v ∂Γ.F, bid v ∈ S := ae_of_ae_map hmeas.aemeasurable hS
  let T := {v | 0 < bid v ∧ (problem Γ i).BestResponse v (safeFullBid (k+1) (bid v)) ∧ bid v ∈ S}
  have hTa : ∀ᵐ v ∂Γ.F, v ∈ T := by
    filter_upwards [hprop, hSa] with v hv hs
    exact ⟨hv.1, hv.2.2.1 i, hs⟩
  have hcard : Fintype.card (Fin N) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin N ≃ Rival i := Fintype.equivOfCardEq hcard
  have hQ b : coverage (k+1) c (by omega) (by simpa using hcm.le)
      (Measure.pi (fun _ : Fin N => Γ.F.map bid)) b =
      coverage (k+1) c (by omega) (by simpa only [card_rival_add_one] using hcm.le)
        (analyticalRivalLaw Γ i) b := by
    rw [← hraw, analyticalRivalLaw_eq_pi]
    exact coverage_equiv e (by omega) _ _ (realBidLaw Γ) b
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
