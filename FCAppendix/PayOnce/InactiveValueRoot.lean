import FCAppendix.PayOnce.InactiveBidGraph
import FCAppendix.PayOnce.NonnegativeValueDemandIdentification

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.AnalyticalKernel PayOnce.AnalyticalRareSuccess PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_bid_graph_at_value_root
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
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      (∀ f : ℝ × ℝ → ℝ, Continuous f →
        (∀ w : ℝ, 0 ≤ w → f (w,Limit.bidStar (k+1) L w) = 0) →
        ∀ δ : ℝ, 0 < δ → Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
          {x | δ ≤ f (max (x.1-g) 0,effectiveBid x.2)}) atTop (𝓝 0)) ∧
      Tendsto (fun t => ∫ x,
        |kernel (k+1) (effectiveBid x.2) L-Limit.pStar (k+1) L (max (x.1-g) 0)|
        ∂((Γ t).F ⊗ₘ (Γ t).σ)) atTop (𝓝 0) := by
  obtain ⟨L,hroot,_⟩ := payOnce_inactive_bid_graph_limit Γ hk hc hcm hN hA hG hu B hB hsym
    hvalue hatom hinactive F hF hg hρ hρb hweak
  let G : ℕ → ProbabilityMeasure ℝ := fun t => PayOnce.BidScaling.realBidLaw (Γ t)
  have hraw t : scaledLaw (G t) 1 = bidLaw (Γ t) := by
    apply Subtype.ext
    change (PayOnce.BidScaling.realBidLaw (Γ t) : Measure ℝ).map
      (fun b : ℝ => ENNReal.ofReal (b/1)) = _
    simp only [div_one]
    exact (compactifiedBidLaw_eq_map_effectiveBidLaw (Γ t)).symm
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀) := by
    simpa only [hraw] using hweak
  let P := fun t => (Γ t).F ⊗ₘ (Γ t).σ
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hmapw t : μW = (P t).map (fun x => max (x.1-g) 0) := by
    dsimp only [μW]
    rw [← hF t,← Measure.fst_compProd (Γ t).F (Γ t).σ]
    change (Measure.map Prod.fst (P t)).map (fun v => max (v-g) 0) = _
    rw [Measure.map_map hnet measurable_fst]
    rfl
  have hd : Limit.demand μW (k+1) L = ρ :=
    value_demand_eq_of_graph_limit_nonneg P (fun _ x => effectiveBid x.2)
      (fun _ x => max (x.1-g) 0)
      (fun _ => (measurable_effectiveBid (k+1)).comp measurable_snd)
      (fun _ => (measurable_fst.sub_const g).max measurable_const)
      G (fun t => realEffectiveBidLaw_eq_action_map (Γ t))
      (fun t => ae_realEffectiveBidLaw_nonneg (Γ t)) μW hmapw hweakRaw
      (by omega) hroot.1 hroot.2.1 hroot.2.2
  have heq : Limit.capRoot μW (k+1) ρ = L :=
    Limit.capRoot_eq μW (by omega) hρb.1 hroot.1 hd
  change 0 < Limit.capRoot μW (k+1) ρ ∧ _
  rw [heq]
  refine ⟨hroot.1,hd,hroot.2.1,hroot.2.2,?_⟩
  exact kernel_error_tendsto_zero_of_graph_limit P (fun _ x => effectiveBid x.2)
    (fun _ x => max (x.1-g) 0)
    (fun _ => (measurable_effectiveBid (k+1)).comp measurable_snd)
    (fun _ => (measurable_fst.sub_const g).max measurable_const)
    (by omega) hroot.1 hroot.2.2

end FCAppendix.Bayes
