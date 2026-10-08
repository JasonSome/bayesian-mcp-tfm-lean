import FCAppendix.PayOnce.InactiveEventualPureBids
import FCAppendix.PayOnce.InactiveEventualConditionalCounts
import FCAppendix.PayOnce.BidFormulaCorrespondence

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_endpoint
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (hm : ∀ t, 0 < M t) (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      (∀ T : ℝ, 0 < T → Limit.demand μW (k+1) T = ρ → T = L) ∧
      InactivePopulationLimits Γ F g ρ ∧
      (∀ t, 0 < C t → C t < M t → ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ),
        g < z.1 → z.2.routeCount = k+1) ∧
      ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
        (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
        (∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) ∧
        (∀ᶠ t in atTop, ∀ᵐ v ∂F, g < v → ∀ᵐ a ∂(Γ t).σ v,
          a.bid = b t v ∧ a.routeCount = k+1) ∧
        ∀ᵐ v ∂F,
          Tendsto (fun t => b t v) atTop (𝓝 (Limit.bidStar (k+1) L (max (v-g) 0))) ∧
          ∀ j : ℕ,
            (∀ i : ∀ t, Fin (M t), Tendsto
              (fun t => (typeOutcome (Γ t) (i t) v).prob (fun r => r.val = j)) atTop
                (𝓝 (ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) j))) ∧
            Tendsto (fun t => (conditionalTypeCountLaw (Γ t) (hm t) v).prob (fun r => r.val = j)) atTop
              (𝓝 (ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) j)) := by
  obtain ⟨hL,hd,b,hmono,hmeas,hbound,heq,hlim⟩ :=
    payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  have hcounts := payOnce_inactive_conditional_count_limits Γ B F g ρ hm h
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  letI : IsProbabilityMeasure μW :=
    Measure.isProbabilityMeasure_map ((measurable_id.sub_const g).max measurable_const).aemeasurable
  have hpart t (hc : 0 < C t) (hcm : C t < M t) :=
    ae_effectiveBid_participation (Γ t) hc hcm (h.action_schedule t) (h.base_schedule t)
      (h.users t) (B t) (h.proposers t) (h.symmetry t) (h.positive_values_atomless t)
  have hraw : ∀ᶠ t in atTop, ∀ᵐ v ∂F, g < v → ∀ᵐ a ∂(Γ t).σ v,
      a.bid = b t v ∧ a.routeCount = k+1 := by
    filter_upwards [h.eventually_scarce,heq] with t ht he
    have hh : ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), g < z.1 →
        z.2.bid = b t z.1 ∧ z.2.routeCount = k+1 := by
      filter_upwards [hpart t ht.1 ht.2,he] with z hp hz hv
      have hr := hp.2.2 (by simpa only [h.common_fee t] using hv)
      have hb : effectiveBid z.2 = z.2.bid := by
        simp only [effectiveBid,hr,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
      exact ⟨hb.symm.trans hz,hr⟩
    have ha := Measure.ae_ae_of_ae_compProd hh
    rw [h.common_values t] at ha
    filter_upwards [ha] with v hv hvg
    exact hv.mono fun _ ha => ha hvg
  refine ⟨hL,hd,?_,payOnce_inactive_population_limits Γ B F g ρ h,?_,
    b,hmono,hmeas,hbound,heq,hraw,?_⟩
  · intro T hT hD
    exact (Limit.capRoot_eq μW (by have := h.proposers_two; omega) h.capacity_bounds.1 hT hD).symm
  · intro t hc hcm
    filter_upwards [hpart t hc hcm] with z hz hv
    exact hz.2.2 (by simpa only [h.common_fee t] using hv)
  · filter_upwards [hlim,hcounts] with v hv hc
    exact ⟨hv,hc⟩

end FCAppendix.Bayes
