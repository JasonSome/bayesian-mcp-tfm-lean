import FCAppendix.PayOnce.InactiveAggregateLimit
import FCAppendix.PayOnce.InactiveSampledCountLimit

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CovarianceConcentration
open scoped BigOperators
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure InactiveSequenceAssumptions
    (M C : ℕ → ℕ) (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) (g ρ : ℝ) : Prop where
  proposers_two : 1 ≤ k
  population_grows : Tendsto M atTop atTop
  capacity_ratio : Tendsto (fun t => (C t:ℝ)/(M t)) atTop (𝓝 ρ)
  capacity_bounds : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))
  action_schedule : ∀ t, (Γ t).A = Schedule.once (k+1)
  base_schedule : ∀ t, (Γ t).G = Schedule.once (k+1)
  users : ∀ t, UsersOptimal (Γ t)
  proposers : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t)
  symmetry : ∀ t, SymmetricProposersOnPath (Γ t)
  positive_values_atomless : ∀ t, PositiveValueAtomless (Γ t)
  visible_atomless : ∀ t, PositiveVisibleAtomless (Γ t)
  inactive_abstain : ∀ t, InactiveAbstain (Γ t)
  common_values : ∀ t, (Γ t).F = F
  common_fee : ∀ t, (Γ t).g = g

namespace InactiveSequenceAssumptions
variable {Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g ρ : ℝ}

theorem along (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    InactiveSequenceAssumptions (M ∘ φ) (C ∘ φ) (fun t => Γ (φ t))
      (fun t => B (φ t)) F g ρ where
  proposers_two := h.proposers_two
  population_grows := h.population_grows.comp hφ
  capacity_ratio := h.capacity_ratio.comp hφ
  capacity_bounds := h.capacity_bounds
  action_schedule := fun t => h.action_schedule (φ t)
  base_schedule := fun t => h.base_schedule (φ t)
  users := fun t => h.users (φ t)
  proposers := fun t => h.proposers (φ t)
  symmetry := fun t => h.symmetry (φ t)
  positive_values_atomless := fun t => h.positive_values_atomless (φ t)
  visible_atomless := fun t => h.visible_atomless (φ t)
  inactive_abstain := fun t => h.inactive_abstain (φ t)
  common_values := fun t => h.common_values (φ t)
  common_fee := fun t => h.common_fee (φ t)

theorem eventually_scarce [IsProbabilityMeasure F]
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∀ᶠ t in atTop, 0 < C t ∧ C t < M t := by
  have hρ1 : ρ < 1 := h.capacity_bounds.2.trans_le measureReal_le_one
  filter_upwards [h.population_grows.eventually_gt_atTop 0,
    (tendsto_order.mp h.capacity_ratio).1 0 h.capacity_bounds.1,
    (tendsto_order.mp h.capacity_ratio).2 1 hρ1] with t hm hc hcm
  have hmR : (0:ℝ) < M t := Nat.cast_pos.mpr hm
  constructor
  · by_contra hn
    have hz : C t = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hz,Nat.cast_zero,zero_div,lt_self_iff_false] at hc
  · exact_mod_cast (div_lt_one hmR).mp hcm

end InactiveSequenceAssumptions

theorem exists_successor_population (hM : Tendsto M atTop atTop)
    (hpos : ∀ t, 0 < M t) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧ M = fun t => N t+1 := by
  refine ⟨fun t => M t-1,(tendsto_sub_atTop_nat 1).comp hM,funext fun t => ?_⟩
  exact (Nat.sub_add_cancel (hpos t)).symm

def InactivePopulationLimits
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed) (F : Measure ℝ) (g ρ : ℝ) : Prop :=
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  0 < L ∧ Limit.demand μW (k+1) L = ρ ∧
    0 < Limit.coverage μW (k+1) L ∧
    Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (Limit.coverage μW (k+1) L)) ∧
    Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (((k+1:ℕ):ℝ)*ρ)) ∧
    Tendsto (fun t => finiteMultiplicity (Γ t)) atTop
      (𝓝 (((k+1:ℕ):ℝ)*ρ/Limit.coverage μW (k+1) L)) ∧
    1 < ((k+1:ℕ):ℝ)*ρ/Limit.coverage μW (k+1) L ∧
    ∀ j : ℕ, Tendsto (fun t => ∫ d, populationMean (fun i =>
      (profileCountLaw (Γ t) d i).prob (fun r => r.val = j)) ∂userProfileLaw (Γ t)) atTop
        (𝓝 (∫ v, ManyProposers.binomialMass (k+1) (Limit.pStar (k+1) L (max (v-g) 0)) j ∂F))

theorem inactivePopulationLimits_of_shift
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed) (F : Measure ℝ) (g ρ : ℝ) (T : ℕ)
    (h : InactivePopulationLimits (fun t => Γ (t+T)) F g ρ) :
    InactivePopulationLimits Γ F g ρ := by
  obtain ⟨hL,hd,hQ,hcoverage,hload,hmult,hstrict,hcounts⟩ := h
  exact ⟨hL,hd,hQ,(tendsto_add_atTop_iff_nat T).mp hcoverage,
    (tendsto_add_atTop_iff_nat T).mp hload,(tendsto_add_atTop_iff_nat T).mp hmult,hstrict,
    fun j => (tendsto_add_atTop_iff_nat T).mp (hcounts j)⟩

theorem payOnce_inactive_population_limits_of_scarce
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t) :
    InactivePopulationLimits Γ F g ρ := by
  obtain ⟨N,hN,rfl⟩ := exists_successor_population h.population_grows
    (fun t => (hc t).trans (hcm t))
  have hratio : Tendsto (fun t => (C t:ℝ)/(N t+1)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using h.capacity_ratio
  have ha := payOnce_inactive_aggregate_limit Γ h.proposers_two hc hcm hN
    h.action_schedule h.base_schedule h.users B h.proposers h.symmetry
    h.positive_values_atomless h.visible_atomless h.inactive_abstain F h.common_values h.common_fee
    hratio h.capacity_bounds
  have hs := payOnce_inactive_sampled_count_limit Γ h.proposers_two hc hcm hN
    h.action_schedule h.base_schedule h.users B h.proposers h.symmetry
    h.positive_values_atomless h.visible_atomless h.inactive_abstain F h.common_values h.common_fee
    hratio h.capacity_bounds
  exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1,ha.2.2.2.2.2.1,ha.2.2.2.2.2.2,hs.2.2⟩

theorem payOnce_inactive_population_limits
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    InactivePopulationLimits Γ F g ρ := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp h.eventually_scarce
  apply inactivePopulationLimits_of_shift Γ F g ρ T
  exact payOnce_inactive_population_limits_of_scarce (fun t => Γ (t+T)) (fun t => B (t+T)) F g ρ
    (h.along (fun t => t+T) (tendsto_add_atTop_nat T))
    (fun t => (hT (t+T) (by omega)).1) (fun t => (hT (t+T) (by omega)).2)

end FCAppendix.Bayes
