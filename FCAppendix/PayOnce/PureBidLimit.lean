import FCAppendix.PayOnce.FullSequenceBidGraph
import FCAppendix.PayOnce.MonotoneGraphLimit

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_pure_bid_limit
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
    let μW := F.map (fun v => v-g)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
        (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
        (∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), z.2.bid = b t z.1) ∧
        ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop (𝓝 (Limit.bidStar (k+1) L (v-g))) := by
  obtain ⟨hL,hd,hgraph,_⟩ := payOnce_full_sequence_bid_graph Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb
  let L := Limit.capRoot (F.map (fun v => v-g)) (k+1) ρ
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  choose b hmono hmeas hbound hraw heq T hTa hT using fun t =>
    exists_monotone_analytical_IC (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t,hg t] using hactive)
  have hb t v : 0 ≤ b t v ∧ b t v ≤ max (v-g) 0 := by simpa only [hg t] using hbound t v
  refine ⟨hL,hd,b,hmono,hmeas,hb,heq,?_⟩
  have hf : Continuous (fun v => Limit.bidStar (k+1) L (v-g)) :=
    (Limit.continuous_bidStar (by omega) hL).comp (continuous_id.sub continuous_const)
  apply VanishingBidIC.ae_monotone_limit_of_defect_mass F b hmono _ hf
  intro δ hδ
  have hcf : Continuous (fun x : ℝ × ℝ => |x.2-Limit.bidStar (k+1) L x.1|) :=
    (continuous_snd.sub ((Limit.continuous_bidStar (by omega) hL).comp continuous_fst)).abs
  have hmass := hgraph _ hcf (fun _ _ => by simp only [L,sub_self,abs_zero]) δ hδ
  apply hmass.congr
  intro t
  let E := {v : ℝ | δ ≤ |b t v-Limit.bidStar (k+1) L (v-g)|}
  have hE : MeasurableSet E := measurableSet_le measurable_const ((hmeas t).sub hf.measurable).abs
  calc
    ((Γ t).F ⊗ₘ (Γ t).σ) {z | δ ≤ |z.2.bid-Limit.bidStar (k+1) L (z.1-g)|} =
        ((Γ t).F ⊗ₘ (Γ t).σ) (Prod.fst ⁻¹' E) := by
      apply measure_congr
      filter_upwards [heq t] with z hz
      change (δ ≤ |z.2.bid-Limit.bidStar (k+1) L (z.1-g)|) =
        (δ ≤ |b t z.1-Limit.bidStar (k+1) L (z.1-g)|)
      rw [hz]
    _ = F E := by rw [← Measure.fst_apply hE,Measure.fst_compProd,hF t]

end FCAppendix.Bayes
