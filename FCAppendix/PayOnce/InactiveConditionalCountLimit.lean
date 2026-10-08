import FCAppendix.PayOnce.InactivePureBidLimit
import FCAppendix.PayOnce.InactiveFullSequenceFocal
import FCAppendix.PayOnce.DummyFocalCountLimit
import FCAppendix.PayOnce.DummyInterimTransport

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.DummyKernel PayOnce.CompactifiedBidLaws
open scoped BigOperators
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_conditional_count_limit
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
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    ∀ᵐ v ∂F, ∀ j : ℕ,
      (∀ i : ∀ t, Fin (N t+1), Tendsto
        (fun t => (typeOutcome (Γ t) (i t) v).prob (fun r => r.val = j)) atTop
          (𝓝 (ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) j))) ∧
      Tendsto (fun t => (conditionalTypeCountLaw (Γ t) (by omega) v).prob (fun r => r.val = j)) atTop
        (𝓝 (ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) j)) := by
  dsimp only
  obtain ⟨hL,_,b,_,_,hbound,heq,hlim⟩ := payOnce_inactive_pure_bid_limit Γ hk hc hcm hN hA hG hu B hB hsym
    hvalue hatom hinactive F hF hg hρ hρb
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hroute t := ae_positive_broadcast_or_abstain (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (hinactive t)
  have hpos t : ∀ᵐ v ∂F, g < v → 0 < b t v := by
    have hh : ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), g < z.1 → 0 < b t z.1 := by
      filter_upwards [ae_effectiveBid_participation (Γ t) (hc t) (hcm t) (hA t) (hG t)
        (hu t) (B t) (hB t) (hsym t) (hvalue t),heq t] with z hz he hvg
      rw [← he]
      exact hz.1.mpr (by simpa only [hg t] using hvg)
    rw [← hF t]
    filter_upwards [Measure.ae_ae_of_ae_compProd hh] with v hv
    exact hv.exists.choose_spec
  have hcount t j := ae_typeOutcome_countMass_eq_dummy (Γ t) hk (hA t) (B t) (hB t) (hsym t)
    (hroute t) (b t) (heq t) j
  have hcountF t j := by simpa only [hF t] using hcount t j
  filter_upwards [hlim,ae_all_iff.mpr hpos,
    ae_all_iff.mpr (fun t => ae_all_iff.mpr (fun j => hcountF t j))] with v hv hbpos hvcount
  intro j
  have herror : Tendsto (fun t => ∫ r : Fin (N t) → ℝ,
      |allocation (k+1) (C t) (by omega) r (b t v)-kernel (k+1) (b t v) L|
        ∂Measure.pi (fun _ : Fin (N t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) atTop (𝓝 0) := by
    by_cases hvg : g < v
    · exact payOnce_inactive_full_sequence_focal_allocation Γ hk hc hcm hN hA hG hu B hB hsym
        hvalue hatom hinactive F hF hg hρ hρb (fun t => b t v) (fun t => hbpos t hvg)
    · have hbzero t : b t v = 0 := by
        have hh := hbound t v
        rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hvg))] at hh
        exact le_antisymm hh.2 hh.1
      have hz t (r : Fin (N t) → ℝ) : allocation (k+1) (C t) (by omega) r 0 = 0 :=
        allocation_eq_zero_of_nonpos (by omega) r le_rfl
      have hkzero : kernel (k+1) 0 L = 0 := kernel_of_le (k+1) hL.le
      simpa only [hz,hbzero,hkzero,sub_self,abs_zero,integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have ht := countMass_tendsto_of_allocation_kernel_error N C (by omega)
    (fun t => Measure.pi (fun _ : Fin (N t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    hL (fun t => b t v) hv herror j
  rw [Limit.kernel_bidStar (by omega) hL] at ht
  constructor
  · intro i
    exact ht.congr fun t => (hvcount t j (i t)).symm
  · apply ht.congr
    intro t
    rw [FiniteLaw.prob_eq_expect,conditionalTypeCountLaw,FiniteLaw.expect_uniformAverage]
    simp_rw [← FiniteLaw.prob_eq_expect,hvcount t j]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (by omega : N t+1 ≠ 0))).symm

end FCAppendix.Bayes
