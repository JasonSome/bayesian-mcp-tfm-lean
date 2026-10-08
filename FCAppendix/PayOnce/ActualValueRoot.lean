import FCAppendix.PayOnce.ActualBidGraph
import FCAppendix.PayOnce.ValueDemandIdentification

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.AnalyticalKernel PayOnce.AnalyticalRareSuccess PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_bid_graph_at_value_root
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
    let μW := F.map (fun v => v-g)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      (∀ f : ℝ × ℝ → ℝ, Continuous f →
        (∀ w : ℝ, 0 ≤ w → f (w,Limit.bidStar (k+1) L w) = 0) →
        ∀ δ : ℝ, 0 < δ → Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
          {x | δ ≤ f (x.1-g,x.2.bid)}) atTop (𝓝 0)) ∧
      Tendsto (fun t => ∫ x, |kernel (k+1) x.2.bid L-Limit.pStar (k+1) L (x.1-g)|
        ∂((Γ t).F ⊗ₘ (Γ t).σ)) atTop (𝓝 0) := by
  obtain ⟨L,hroot,_⟩ := payOnce_bid_graph_limit Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t,hg t] using hactive)
  have hroute t := (hfull t).mono fun _ hz => hz.2
  have hbid t := (hfull t).mono fun _ hz => hz.1
  let G : ℕ → ProbabilityMeasure ℝ := fun t => ⟨realBidLaw (Γ t),inferInstance⟩
  have hraw t : scaledLaw (G t) 1 = bidLaw (Γ t) := by
    apply Subtype.ext
    change (realBidLaw (Γ t)).map (fun b : ℝ => ENNReal.ofReal (b/1)) = _
    simp only [div_one]
    exact (compactifiedBidLaw_eq_map_realBidLaw (Γ t) (by omega) (hroute t)).symm
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀) := by
    simpa only [hraw] using hweak
  let P := fun t => (Γ t).F ⊗ₘ (Γ t).σ
  let μW := F.map (fun v => v-g)
  have hnet : Measurable (fun v : ℝ => v-g) := measurable_id.sub_const g
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hmapw t : μW = (P t).map (fun x => x.1-g) := by
    dsimp only [μW]
    rw [← hF t,← Measure.fst_compProd (Γ t).F (Γ t).σ]
    change (Measure.map Prod.fst (P t)).map (fun v => v-g) = _
    rw [Measure.map_map hnet measurable_fst]
    rfl
  have hd : Limit.demand μW (k+1) L = ρ :=
    value_demand_eq_of_graph_limit P (fun _ x => x.2.bid) (fun _ x => x.1-g)
      (fun _ => (measurable_bid (k+1)).comp measurable_snd)
      (fun _ => measurable_fst.sub_const g) G (fun t => realBidLaw_eq_action_map (Γ t))
      (fun t => ae_realBidLaw_pos (Γ t) (hbid t)) μW hmapw hweakRaw
      (by omega) hroot.1 hroot.2.1 hroot.2.2
  have heq : Limit.capRoot μW (k+1) ρ = L :=
    Limit.capRoot_eq μW (by omega) hρb.1 hroot.1 hd
  change 0 < Limit.capRoot μW (k+1) ρ ∧ _
  rw [heq]
  refine ⟨hroot.1,hd,hroot.2.1,hroot.2.2,?_⟩
  exact kernel_error_tendsto_zero_of_graph_limit P (fun _ x => x.2.bid) (fun _ x => x.1-g)
    (fun _ => (measurable_bid (k+1)).comp measurable_snd) (fun _ => measurable_fst.sub_const g)
    (by omega) hroot.1 hroot.2.2

end FCAppendix.Bayes
