import FCAppendix.PayOnce.FullSequenceBidGraph
import FCAppendix.PayOnce.ActualFocalAllocation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.AnalyticalKernel PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_full_sequence_focal_allocation
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
    ∀ x : ℕ → ℝ, (∀ t, 0 < x t) →
      Tendsto (fun t => ∫ r : Fin (N t) → ℝ,
        |allocation (k+1) (C t) (by omega) (by simpa using (hcm t).le) r (x t)-kernel (k+1) (x t) L|
          ∂Measure.pi (fun _ : Fin (N t) => realBidLaw (Γ t))) atTop (𝓝 0) := by
  dsimp only
  let L := Limit.capRoot (F.map (fun v => v-g)) (k+1) ρ
  intro x hx
  apply tendsto_of_subseq_tendsto
  intro ψ hψ
  obtain ⟨G₀,φ,hφ,hw⟩ := CompactSpace.tendsto_subseq (fun t => bidLaw (Γ (ψ t)))
  have hindex := hψ.comp hφ.tendsto_atTop
  let η := fun t => ψ (φ t)
  have hN' : Tendsto (fun t => N (η t)) atTop atTop := hN.comp hindex
  have hM : Tendsto (fun t => N (η t)+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN'
  have hρM : Tendsto (fun t => (C (η t):ℝ)/((N (η t)+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add,Nat.cast_one,η,Function.comp_def] using hρ.comp hindex
  have hvalue := payOnce_bid_graph_at_value_root (fun t => Γ (η t)) hk
    (fun t => hc (η t)) (fun t => hcm (η t)) hN'
    (fun t => hA (η t)) (fun t => hG (η t)) (fun t => hu (η t))
    (fun t => B (η t)) (fun t => hB (η t)) (fun t => hsym (η t))
    (fun t => hatom (η t)) F (fun t => hF (η t)) (fun t => hg (η t))
    hactive (hρ.comp hindex) hρb hw
  obtain ⟨L',hfocal,_⟩ := payOnce_focal_allocation_limit (fun t => Γ (η t)) hk
    (fun t => hc (η t)) (fun t => hcm (η t)) hN'
    (fun t => hA (η t)) (fun t => hG (η t)) (fun t => hu (η t))
    (fun t => B (η t)) (fun t => hB (η t)) (fun t => hsym (η t))
    (fun t => hatom (η t)) F (fun t => hF (η t)) (fun t => hg (η t))
    hactive (hρ.comp hindex) hρb hw
  obtain ⟨_,U,_,hunique⟩ := payOnce_positive_capacity_root (fun t => Γ (η t)) hk
    (fun t => hc (η t)) (fun t => hcm (η t)) hM
    (fun t => hA (η t)) (fun t => hG (η t)) (fun t => hu (η t))
    (fun t => B (η t)) (fun t => hB (η t)) (fun t => hsym (η t))
    (fun t => hatom (η t)) F (fun t => hF (η t)) (fun t => hg (η t))
    hactive hρM hρb hw
  have heq : L' = L := (hunique L' ⟨hfocal.1,hfocal.2.1⟩).trans
    (hunique L ⟨hvalue.1,hvalue.2.2.1⟩).symm
  rw [heq] at hfocal
  exact ⟨φ,hfocal.2.2 (fun t => x (η t)) (fun t => hx (η t))⟩

end FCAppendix.Bayes
