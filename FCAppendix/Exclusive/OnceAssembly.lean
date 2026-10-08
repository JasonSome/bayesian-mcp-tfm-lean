import FCAppendix.Exclusive.OnceRouting
import FCAppendix.Exclusive.LimitBounds

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped BigOperators ProbabilityTheory

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exclusive_routed_positive_of_visibleAtomless (Γ : FiniteGame m n c Seed)
    (hatom : VisibleAtomless Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.routeCount → 0 < x.2.bid := by
  have hdraw : ∀ᵐ d ∂userLaw Γ, 0 < d.1.2.routeCount → 0 < d.1.2.bid := by
    have hz : ∀ᵐ d ∂userLaw Γ, ∀ j : Fin n,
        ¬ (j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid = 0) :=
      ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp (hatom j 0)
    filter_upwards [hz] with d hd hk
    have hcard : 0 < (firstK d.2 d.1.2.routeCount).card := by
      rwa [card_firstK _ _ d.1.2.routeCount_le]
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
    exact lt_of_le_of_ne d.1.2.bid_nonneg (fun he => hd j ⟨hj, he.symm⟩)
  have h := Measure.ae_ae_of_ae_prod hdraw
  filter_upwards [h] with x hx
  obtain ⟨_, hτ⟩ := hx.exists
  exact hτ

theorem exclusive_once_positive_broadcast_or_abstain (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hvisible : VisibleAtomless Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = n) := by
  have hroute := exclusive_once_routing_of_feasible_optimal Γ hc hcm hA hG hu B hB hsym hvalue
  have hmeas : MeasurableSet {x : ℝ × JointAction n |
      0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount = n} := by
    have hb : MeasurableSet {x : ℝ × JointAction n | 0 < x.2.bid} :=
      measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd)
    have hk : MeasurableSet {x : ℝ × JointAction n | 0 < x.2.routeCount} :=
      measurableSet_lt measurable_const ((measurable_routeCount n).comp measurable_snd)
    have hn : MeasurableSet {x : ℝ × JointAction n | x.2.routeCount = n} :=
      measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const
    simpa only [imp_iff_not_or, Set.setOf_or, Set.compl_setOf] using hb.compl.union (hk.compl.union hn)
  have hr := Measure.ae_compProd_of_ae_ae hmeas hroute
  filter_upwards [hr, exclusive_routed_positive_of_visibleAtomless Γ hvisible] with x hx hp
  by_cases hz : x.2.routeCount = 0
  · exact Or.inl hz
  · have hk : 0 < x.2.routeCount := Nat.pos_of_ne_zero hz
    exact Or.inr ⟨hp hk, hx (hp hk) hk⟩

theorem exclusive_once_finite_classification (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k + 1)) (hG : Γ.G = Schedule.once (k + 1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hvisible : VisibleAtomless Γ) (hinactive : InactiveAbstain Γ)
    (hh : 0 < Γ.F.real (Ioi Γ.g)) :
    finiteCoverage Γ ≤ Γ.F.real (Ioi Γ.g) * PayOnce.success (k + 1)
        (min ((c : ℝ) / ((m : ℝ) * Γ.F.real (Ioi Γ.g))) 1) ∧
      (((k + 1 : ℕ) : ℝ) - 1) * (finiteCoverage Γ) ^ 2 /
        ((((k + 1 : ℕ) : ℝ) ^ 2) * Γ.F.real (Ioi Γ.g)) ≤ finiteLoad Γ - finiteCoverage Γ := by
  apply finite_exclusive_bounds Γ hk (hc.trans hcm) B
    (exclusiveOptimalOnPath_of_feasible Γ B hB) hsym
    (exclusive_once_positive_broadcast_or_abstain Γ hc hcm hA hG hu B hB hsym hvalue hvisible)
    (Ioi Γ.g) measurableSet_Ioi hh
  filter_upwards [hinactive] with x hx hnot
  exact hx (le_of_not_gt hnot)

theorem prop_exclusive_once_existing
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) (k + 1) (C t) Seed)
    (hk : 1 ≤ k) (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k + 1))
    (hG : ∀ t, (Γ t).G = Schedule.once (k + 1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, ExclusivePosteriorOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hvisible : ∀ t, VisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) (hF : ∀ t, (Γ t).F = F) {g rho Q D : ℝ}
    (hg : ∀ t, (Γ t).g = g)
    (hrho : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 rho))
    (hrho0 : 0 < rho) (hrhoh : rho < F.real (Ioi g))
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q))
    (hD : Tendsto (fun t => finiteLoad (Γ t) - finiteCoverage (Γ t)) atTop (𝓝 D)) :
    Q ≤ F.real (Ioi g) * PayOnce.success (k + 1) (rho / F.real (Ioi g)) ∧
      F.real (Ioi g) * PayOnce.success (k + 1) (rho / F.real (Ioi g)) <
        min (((k + 1 : ℕ) : ℝ) * rho) (F.real (Ioi g)) ∧
      (((k + 1 : ℕ) : ℝ) - 1) * Q ^ 2 /
        ((((k + 1 : ℕ) : ℝ) ^ 2) * F.real (Ioi g)) ≤ D ∧ (0 < Q → 0 < D) := by
  have hmass1 : F.real (Ioi g) ≤ 1 := by
    rw [← hF 0]
    exact measureReal_le_one
  have hguards := exclusive_eventual_capacity_guards hM hrho hrho0 (hrhoh.trans_le hmass1)
  have hr : ∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k + 1) := by
    filter_upwards [hguards] with t ht
    exact exclusive_once_positive_broadcast_or_abstain (Γ t) ht.1 ht.2
      (hA t) (hG t) (hu t) (B t) (hB t) (hsym t) (hvalue t) (hvisible t)
  apply exclusive_existing_limit_bounds Γ hk hM B
    (fun t => exclusiveOptimalOnPath_of_feasible (Γ t) (B t) (hB t)) hsym hr
    (Ioi g) measurableSet_Ioi _ (fun t => by rw [hF t]) hrho hrho0 hrhoh hQ hD
  intro t
  filter_upwards [hinactive t] with x hx hnot
  apply hx
  rw [hg t]
  exact le_of_not_gt hnot

end FCAppendix.Bayes
