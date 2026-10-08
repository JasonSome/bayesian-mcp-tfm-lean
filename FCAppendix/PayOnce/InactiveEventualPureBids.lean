import FCAppendix.PayOnce.InactivePureBidLimit
import FCAppendix.PayOnce.InactiveEventualPopulation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_pure_bid_limit_of_scarce
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
        (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
        (∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) ∧
        ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop (𝓝 (Limit.bidStar (k+1) L (max (v-g) 0))) := by
  obtain ⟨N,hN,rfl⟩ := exists_successor_population h.population_grows
    (fun t => (hc t).trans (hcm t))
  exact payOnce_inactive_pure_bid_limit Γ h.proposers_two hc hcm hN
    h.action_schedule h.base_schedule h.users B h.proposers h.symmetry
    h.positive_values_atomless h.visible_atomless h.inactive_abstain F h.common_values h.common_fee
    (by simpa only [Nat.cast_add,Nat.cast_one] using h.capacity_ratio) h.capacity_bounds

theorem payOnce_inactive_eventual_pure_bid_limit
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
      ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
        (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
        (∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) ∧
        ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop (𝓝 (Limit.bidStar (k+1) L (max (v-g) 0))) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp h.eventually_scarce
  obtain ⟨hL,hd,b,hmono,hmeas,hbound,heq,hlim⟩ :=
    payOnce_inactive_pure_bid_limit_of_scarce (fun t => Γ (t+T)) (fun t => B (t+T)) F g ρ
      (h.along (fun t => t+T) (tendsto_add_atTop_nat T))
      (fun t => (hT (t+T) (by omega)).1) (fun t => (hT (t+T) (by omega)).2)
  let b₀ : ℕ → ℝ → ℝ := fun t v => if t < T then 0 else b (t-T) v
  refine ⟨hL,hd,b₀,?_,?_,?_,?_,?_⟩
  · intro t
    by_cases ht : t < T
    · simpa only [b₀,if_pos ht] using (monotone_const : Monotone (fun _ : ℝ => (0:ℝ)))
    · simpa only [b₀,if_neg ht] using hmono (t-T)
  · intro t
    by_cases ht : t < T
    · simpa only [b₀,if_pos ht] using (measurable_const : Measurable (fun _ : ℝ => (0:ℝ)))
    · simpa only [b₀,if_neg ht] using hmeas (t-T)
  · intro t v
    by_cases ht : t < T
    · simp only [b₀,if_pos ht]
      exact ⟨le_rfl,le_max_right _ _⟩
    · simpa only [b₀,if_neg ht] using hbound (t-T) v
  · filter_upwards [eventually_ge_atTop T] with t ht
    have hh := heq (t-T)
    rw [Nat.sub_add_cancel ht] at hh
    simpa only [b₀,if_neg (not_lt_of_ge ht)] using hh
  · filter_upwards [hlim] with v hv
    apply (tendsto_add_atTop_iff_nat T).mp
    apply hv.congr
    intro t
    simp only [b₀,if_neg (by omega : ¬ t+T<T),Nat.add_sub_cancel]

end FCAppendix.Bayes
