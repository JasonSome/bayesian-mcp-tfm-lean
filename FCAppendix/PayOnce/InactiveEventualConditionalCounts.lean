import FCAppendix.PayOnce.InactiveConditionalCountLimit
import FCAppendix.PayOnce.InactiveEventualPopulation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def InactiveConditionalCountLimits
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed) (F : Measure ℝ) (g ρ : ℝ)
    (hm : ∀ t, 0 < M t) : Prop :=
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  ∀ᵐ v ∂F, ∀ j : ℕ,
    (∀ i : ∀ t, Fin (M t), Tendsto
      (fun t => (typeOutcome (Γ t) (i t) v).prob (fun r => r.val = j)) atTop
        (𝓝 (ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) j))) ∧
    Tendsto (fun t => (conditionalTypeCountLaw (Γ t) (hm t) v).prob (fun r => r.val = j)) atTop
      (𝓝 (ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) j))

theorem inactiveConditionalCountLimits_of_shift
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed) (F : Measure ℝ) (g ρ : ℝ)
    (hm : ∀ t, 0 < M t) (T : ℕ)
    (h : InactiveConditionalCountLimits (fun t => Γ (t+T)) F g ρ (fun t => hm (t+T))) :
    InactiveConditionalCountLimits Γ F g ρ hm := by
  filter_upwards [h] with v hv
  intro j
  constructor
  · intro i
    exact (tendsto_add_atTop_iff_nat T).mp ((hv j).1 (fun t => i (t+T)))
  · exact (tendsto_add_atTop_iff_nat T).mp (hv j).2

theorem payOnce_inactive_conditional_count_limits_of_scarce
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (hm : ∀ t, 0 < M t) (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t) :
    InactiveConditionalCountLimits Γ F g ρ hm := by
  obtain ⟨N,hN,rfl⟩ := exists_successor_population h.population_grows hm
  have hratio : Tendsto (fun t => (C t:ℝ)/(N t+1)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using h.capacity_ratio
  exact payOnce_inactive_conditional_count_limit Γ h.proposers_two hc hcm hN
    h.action_schedule h.base_schedule h.users B h.proposers h.symmetry
    h.positive_values_atomless h.visible_atomless h.inactive_abstain F h.common_values h.common_fee
    hratio h.capacity_bounds

theorem payOnce_inactive_conditional_count_limits
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (hm : ∀ t, 0 < M t) (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    InactiveConditionalCountLimits Γ F g ρ hm := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp h.eventually_scarce
  apply inactiveConditionalCountLimits_of_shift Γ F g ρ hm T
  exact payOnce_inactive_conditional_count_limits_of_scarce
    (fun t => Γ (t+T)) (fun t => B (t+T)) F g ρ (fun t => hm (t+T))
    (h.along (fun t => t+T) (tendsto_add_atTop_nat T))
    (fun t => (hT (t+T) (by omega)).1) (fun t => (hT (t+T) (by omega)).2)

end FCAppendix.Bayes
