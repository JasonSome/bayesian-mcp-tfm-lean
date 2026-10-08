import FCAppendix.PayOnce.InactiveValueRoot

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_full_sequence_bid_graph
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
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      (∀ f : ℝ × ℝ → ℝ, Continuous f →
        (∀ w : ℝ, 0 ≤ w → f (w,Limit.bidStar (k+1) L w) = 0) →
        ∀ δ : ℝ, 0 < δ → Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
          {x | δ ≤ f (max (x.1-g) 0,effectiveBid x.2)}) atTop (𝓝 0)) ∧
      Tendsto (fun t => ∫ x, |kernel (k+1) (effectiveBid x.2) L-Limit.pStar (k+1) L (max (x.1-g) 0)|
        ∂((Γ t).F ⊗ₘ (Γ t).σ)) atTop (𝓝 0) := by
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  have hsub (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) :
      ∃ φ : ℕ → ℕ, 0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
        (∀ f : ℝ × ℝ → ℝ, Continuous f →
          (∀ w : ℝ, 0 ≤ w → f (w,Limit.bidStar (k+1) L w) = 0) →
          ∀ δ : ℝ, 0 < δ → Tendsto (fun t => ((Γ (ψ (φ t))).F ⊗ₘ (Γ (ψ (φ t))).σ)
            {x | δ ≤ f (max (x.1-g) 0,effectiveBid x.2)}) atTop (𝓝 0)) ∧
        Tendsto (fun t => ∫ x, |kernel (k+1) (effectiveBid x.2) L-Limit.pStar (k+1) L (max (x.1-g) 0)|
          ∂((Γ (ψ (φ t))).F ⊗ₘ (Γ (ψ (φ t))).σ)) atTop (𝓝 0) := by
    obtain ⟨G₀,φ,hφ,hw⟩ := CompactSpace.tendsto_subseq (fun t => bidLaw (Γ (ψ t)))
    have hh := payOnce_inactive_bid_graph_at_value_root (fun t => Γ (ψ (φ t))) hk
      (fun t => hc (ψ (φ t))) (fun t => hcm (ψ (φ t))) (hN.comp (hψ.comp hφ.tendsto_atTop))
      (fun t => hA (ψ (φ t))) (fun t => hG (ψ (φ t))) (fun t => hu (ψ (φ t)))
      (fun t => B (ψ (φ t))) (fun t => hB (ψ (φ t))) (fun t => hsym (ψ (φ t)))
      (fun t => hvalue (ψ (φ t))) (fun t => hatom (ψ (φ t)))
      (fun t => hinactive (ψ (φ t))) F (fun t => hF (ψ (φ t))) (fun t => hg (ψ (φ t)))
      (hρ.comp (hψ.comp hφ.tendsto_atTop)) hρb hw
    exact ⟨φ,hh.1,hh.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
  obtain ⟨_,hL,hd,_⟩ := hsub id tendsto_id
  refine ⟨hL,hd,?_,?_⟩
  · intro f hf hgraph δ hδ
    apply tendsto_of_subseq_tendsto
    intro ψ hψ
    obtain ⟨φ,_,_,hh,_⟩ := hsub ψ hψ
    exact ⟨φ,hh f hf hgraph δ hδ⟩
  · apply tendsto_of_subseq_tendsto
    intro ψ hψ
    obtain ⟨φ,_,_,_,hh⟩ := hsub ψ hψ
    exact ⟨φ,hh⟩

end FCAppendix.Bayes
