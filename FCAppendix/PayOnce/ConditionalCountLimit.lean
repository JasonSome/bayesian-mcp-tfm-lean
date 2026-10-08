import FCAppendix.PayOnce.PureBidLimit
import FCAppendix.PayOnce.FullSequenceFocal
import FCAppendix.PayOnce.FocalCountLimit
import FCAppendix.PayOnce.InterimCountTransport

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.AnalyticalKernel PayOnce.CompactifiedBidLaws
open scoped BigOperators
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_conditional_count_limit
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
    (hρb : ρ ∈ Ioo (0:ℝ) 1) :
    let L := Limit.capRoot (F.map (fun v => v-g)) (k+1) ρ
    ∀ᵐ v ∂F, ∀ j : ℕ,
      (∀ i : ∀ t, Fin (N t+1), Tendsto
        (fun t => (typeOutcome (Γ t) (i t) v).prob (fun r => r.val = j)) atTop
          (𝓝 (ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (v-g)) j))) ∧
      Tendsto (fun t => (conditionalTypeCountLaw (Γ t) (by omega) v).prob (fun r => r.val = j)) atTop
        (𝓝 (ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (v-g)) j)) := by
  dsimp only
  obtain ⟨hL,_,b,_,_,_,heq,hlim⟩ := payOnce_pure_bid_limit Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb
  let L := Limit.capRoot (F.map (fun v => v-g)) (k+1) ρ
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t,hg t] using hactive)
  have hpos t : ∀ᵐ v ∂F, 0 < b t v := by
    rw [← hF t]
    exact ae_pure_bid_pos (Γ t) (b t) (heq t) ((hfull t).mono fun _ hz => hz.1)
  have hcount t j := ae_typeOutcome_countMass_eq (Γ t) hk (hcm t).le (hA t) (B t) (hB t) (hsym t)
    ((hfull t).mono fun _ hz => hz.2) ((hfull t).mono fun _ hz => hz.1) (b t) (heq t) j
  have hcountF t j := by simpa only [hF t] using hcount t j
  filter_upwards [hlim,ae_all_iff.mpr hpos,
    ae_all_iff.mpr (fun t => ae_all_iff.mpr (fun j => hcountF t j))] with v hv hbpos hvcount
  intro j
  have herror := payOnce_full_sequence_focal_allocation Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb (fun t => b t v) hbpos
  have ht := countMass_tendsto_of_allocation_kernel_error N C (by omega)
    (fun t => by simpa using (hcm t).le) (fun t => Measure.pi (fun _ : Fin (N t) => realBidLaw (Γ t)))
    hL (fun t => b t v) hbpos hv herror j
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
