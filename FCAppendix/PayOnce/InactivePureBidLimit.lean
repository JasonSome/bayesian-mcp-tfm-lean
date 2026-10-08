import FCAppendix.PayOnce.InactiveFullSequenceBidGraph
import FCAppendix.PayOnce.PositiveMonotoneGraphLimit

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_pure_bid_limit
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
      ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
        (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
        (∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) ∧
        ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop (𝓝 (Limit.bidStar (k+1) L (max (v-g) 0))) := by
  obtain ⟨hL,hd,hgraph,_⟩ := payOnce_inactive_full_sequence_bid_graph Γ hk hc hcm hN hA hG hu B hB hsym
    hvalue hatom hinactive F hF hg hρ hρb
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  choose b hmono hmeas hbound heq hprop using fun t =>
    exists_monotone_effective_bid_bestResponse_all (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (hinactive t)
  have hb t v : 0 ≤ b t v ∧ b t v ≤ max (v-g) 0 := by simpa only [hg t] using hbound t v
  have hvalueF : ∀ v : ℝ, g < v → F {v} = 0 := by
    simpa only [PositiveValueAtomless,hF 0,hg 0] using hvalue 0
  refine ⟨hL,hd,b,hmono,hmeas,hb,heq,?_⟩
  have hf : Continuous (fun v => Limit.bidStar (k+1) L (max (v-g) 0)) :=
    (Limit.continuous_bidStar (by omega) hL).comp
      ((continuous_id.sub continuous_const).max continuous_const)
  have hpositive : ∀ᵐ v ∂F, g < v →
      Tendsto (fun t => b t v) atTop (𝓝 (Limit.bidStar (k+1) L (max (v-g) 0))) := by
    apply VanishingBidIC.ae_positive_monotone_limit_of_defect_mass F hvalueF b hmono _ hf
    intro δ hδ
    have hcf : Continuous (fun x : ℝ × ℝ => |x.2-Limit.bidStar (k+1) L x.1|) :=
      (continuous_snd.sub ((Limit.continuous_bidStar (by omega) hL).comp continuous_fst)).abs
    have hmass := hgraph _ hcf (fun _ _ => by simp only [L,sub_self,abs_zero]) δ hδ
    apply hmass.congr
    intro t
    let E := {v : ℝ | δ ≤ |b t v-Limit.bidStar (k+1) L (max (v-g) 0)|}
    have hE : MeasurableSet E := measurableSet_le measurable_const ((hmeas t).sub hf.measurable).abs
    calc
      ((Γ t).F ⊗ₘ (Γ t).σ) {z | δ ≤ |effectiveBid z.2-Limit.bidStar (k+1) L (max (z.1-g) 0)|} =
          ((Γ t).F ⊗ₘ (Γ t).σ) (Prod.fst ⁻¹' E) := by
        apply measure_congr
        filter_upwards [heq t] with z hz
        change (δ ≤ |effectiveBid z.2-Limit.bidStar (k+1) L (max (z.1-g) 0)|) =
          (δ ≤ |b t z.1-Limit.bidStar (k+1) L (max (z.1-g) 0)|)
        rw [hz]
      _ = F E := by rw [← Measure.fst_apply hE,Measure.fst_compProd,hF t]
  filter_upwards [hpositive] with v hv
  by_cases hvg : g < v
  · exact hv hvg
  · have hw : max (v-g) 0 = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_gt hvg))
    have hbzero t : b t v = 0 := by
      have hh := hb t v
      rw [hw] at hh
      exact le_antisymm hh.2 hh.1
    simpa only [hbzero,hw,Limit.bidStar_of_le hL.le,max_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end FCAppendix.Bayes
