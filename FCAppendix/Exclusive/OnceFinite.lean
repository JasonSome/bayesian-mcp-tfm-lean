import FCAppendix.Exclusive.OnceRewards
import FCAppendix.Exclusive.OnceActual
import FCAppendix.Exclusive.OnceMixture

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure ExclusiveOnceEquilibrium (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) : Prop where
  bid_once : Γ.A = Schedule.once n
  base_once : Γ.G = Schedule.once n
  users : UsersOptimal Γ
  proposers : ExclusiveProposersBestRespond Γ B
  symmetric : SymmetricProposersOnPath Γ
  values_atomless : ∀ v : ℝ, Γ.F {v} = 0
  visible_atomless : VisibleAtomless Γ

structure ExclusiveOnceActualConclusion (Γ : FiniteGame m n c Seed) (j : Fin n) : Prop where
  routing : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
    0 < a.bid → 0 < a.routeCount → a.routeCount = n
  zero_or_full : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ x.2.routeCount = n
  common_lists : ∀ᵐ d ∂userProfileLaw Γ,
    ∀ l, observe (drawsRealization d) l = observe (drawsRealization d) j
  count_law : ∀ᵐ d ∂userProfileLaw Γ, ∀ i, profileCountLaw Γ d i =
    IndependentCounts.binomial n (exclusiveMarginal Γ j d i)
      (exclusiveMarginal_bounds Γ j d i).1 (exclusiveMarginal_bounds Γ j d i).2
  capacity : ∀ d, (∑ i, exclusiveMarginal Γ j d i) ≤ (c : ℝ)
  inactive_count : ∀ i, ∀ᵐ ω ∂backgroundLaw Γ,
    (ω.1 i).1.1 ≤ Γ.g → playedCount Γ i ω = 0
  inactive_marginal : ∀ᵐ d ∂userProfileLaw Γ, ∀ i,
    (d i).1.1 ≤ Γ.g → exclusiveMarginal Γ j d i = 0
  coverage_identity : finiteCoverage Γ =
    ∫ z, PayOnce.success n (exclusivePopulationMarginal Γ j z) ∂exclusivePopulationLaw Γ
  load_identity : finiteLoad Γ =
    (n : ℝ) * ∫ z, exclusivePopulationMarginal Γ j z ∂exclusivePopulationLaw Γ
  duplicates_identity : finiteExclusiveDuplicates Γ = finiteLoad Γ - finiteCoverage Γ

structure ExclusiveOnceContributionBounds (Γ : FiniteGame m n c Seed) (j : Fin n) : Prop where
  coverage : finiteCoverage Γ ≤ exclusiveActiveMass Γ *
    (1 - (1 - min ((c : ℝ) / ((m : ℝ) * exclusiveActiveMass Γ)) 1) ^ n)
  duplicates_second_moment :
    ((n : ℝ) - 1) * (∫ z, exclusivePopulationMarginal Γ j z ^ 2 ∂exclusivePopulationLaw Γ) ≤
      finiteLoad Γ - finiteCoverage Γ
  active_cauchy_schwarz :
    ((n : ℝ) - 1) / exclusiveActiveMass Γ *
      (∫ z, exclusivePopulationMarginal Γ j z ∂exclusivePopulationLaw Γ) ^ 2 ≤
    ((n : ℝ) - 1) * (∫ z, exclusivePopulationMarginal Γ j z ^ 2 ∂exclusivePopulationLaw Γ)
  duplicates_coverage :
    ((n : ℝ) - 1) * finiteCoverage Γ ^ 2 / ((n : ℝ) ^ 2 * exclusiveActiveMass Γ) ≤
      finiteLoad Γ - finiteCoverage Γ

theorem exclusive_once_routing_bayes (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusiveProposersBestRespond Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, 0 < a.bid → 0 < a.routeCount → a.routeCount = n :=
  exclusive_once_routing Γ hc hcm hA hG hu B
    (ExclusiveProposersBestRespond.to_receipt_optimal_onPath Γ B hB) hsym hatom

theorem exclusive_once_actual (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ)
    (h : ExclusiveOnceEquilibrium Γ B) (j : Fin n) :
    ExclusiveOnceActualConclusion Γ j := by
  have hB := ExclusiveProposersBestRespond.to_receipt_optimal_onPath Γ B h.proposers
  have hatom : PositiveValueAtomless Γ := fun v _ => h.values_atomless v
  have hrx : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount = n := by
    filter_upwards [exclusive_ae_partial_strict_surplus Γ hc hcm h.bid_once h.base_once
        h.users B hB h.symmetric hatom,
      exclusive_ae_positive_surplus_broadcast Γ hc hcm h.bid_once h.base_once
        h.users B hB h.symmetric] with x hs hr hb hk
    by_contra hnot
    have hlt : x.2.routeCount < n := lt_of_le_of_ne x.2.routeCount_le hnot
    exact hnot (hr hb (hs hb hk hlt) hk)
  have hfull := exclusive_ae_zero_or_full_routes Γ h.visible_atomless hrx
  have hid := exclusive_actual_moment_identities Γ hfull h.symmetric j
  exact
    { routing := Measure.ae_ae_of_ae_compProd hrx
      zero_or_full := hfull
      common_lists := ae_commonLists_of_zero_or_full_routes Γ hfull j
      count_law := exclusive_ae_profile_binomial Γ hfull h.symmetric j
      capacity := exclusiveMarginal_capacity Γ j
      inactive_count := exclusive_ae_inactive_count_zero Γ h.users h.visible_atomless
      inactive_marginal := exclusive_ae_inactive_marginal_zero Γ h.users h.visible_atomless j
      coverage_identity := hid.1
      load_identity := hid.2
      duplicates_identity := finiteExclusiveDuplicates_eq_load_sub_coverage Γ }

theorem exclusive_once_posterior (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ)
    (h : ExclusiveOnceEquilibrium Γ B) (j : Fin n) :
    ∀ᵐ ℓ ∂observedListLaw Γ j,
      (∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ) ∧
      (∀ i, noOtherProb Γ B j ℓ i =
        (1 - Proposer.marginal (seedLottery Γ j ℓ) i) ^ (n - 1)) ∧
      (∀ i, exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i =
        exclusiveListedBid ℓ i * (1 - Proposer.marginal (seedLottery Γ j ℓ) i) ^ (n - 1)) ∧
      (∀ᵐ s ∂Γ.seedLaw, Finite.Optimal c
        (fun i => exclusiveListedBid ℓ i *
          (1 - Proposer.marginal (seedLottery Γ j ℓ) i) ^ (n - 1))
        (Γ.policy j ℓ s).val) := by
  have ha := exclusive_once_actual Γ hc hcm B h j
  have hb := ExclusiveProposersBestRespond.to_receipt_optimal_onPath Γ B h.proposers
  filter_upwards [B.ae_commonLists Γ j ha.common_lists, h.symmetric j, hb j]
    with ℓ hcommon hsym hopt
  have hnop (i : Fin m) := noOtherProb_commonList Γ B j ℓ hcommon _ hsym i
  have hscore (i : Fin m) : exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i =
      exclusiveListedBid ℓ i * (1 - Proposer.marginal (seedLottery Γ j ℓ) i) ^ (n - 1) := by
    rw [exclusiveReceipts_eq_listedBid_mul_noOther, hnop]
  refine ⟨hcommon, hnop, hscore, ?_⟩
  have he := funext hscore
  simpa only [he] using hopt

theorem exclusive_once_posterior_count (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ)
    (h : ExclusiveOnceEquilibrium Γ B) (j : Fin n) :
    ∀ᵐ ℓ ∂observedListLaw Γ j, ∀ i,
      exclusivePosteriorPlayedCountLaw Γ B j ℓ i =
        IndependentCounts.binomial n (Proposer.marginal (seedLottery Γ j ℓ) i)
          (CommonList.marginal_nonneg (seedLottery Γ j ℓ) i)
          (CommonList.marginal_le_one (seedLottery Γ j ℓ) i) := by
  have ha := exclusive_once_actual Γ hc hcm B h j
  filter_upwards [B.ae_commonLists Γ j ha.common_lists, h.symmetric j]
    with ℓ hcommon hsym i
  exact exclusivePosteriorPlayedCountLaw_binomial Γ B j ℓ hcommon _ hsym i

theorem exclusive_once_contribution_bounds (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ)
    (h : ExclusiveOnceEquilibrium Γ B) (j : Fin n) (hh : 0 < exclusiveActiveMass Γ) :
    ExclusiveOnceContributionBounds Γ j := by
  have hm : 0 < m := lt_trans hc hcm
  letI : NeZero m := ⟨hm.ne'⟩
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have ha := exclusive_once_actual Γ hc hcm B h j
  have he := exclusiveActiveEvent_mass Γ hm
  have hp := measurable_exclusivePopulationMarginal Γ j
  have hp0 (z : UserProfile m n × Fin m) : 0 ≤ exclusivePopulationMarginal Γ j z :=
    (exclusiveMarginal_bounds Γ j z.1 z.2).1
  have hp1 (z : UserProfile m n × Fin m) : exclusivePopulationMarginal Γ j z ≤ 1 :=
    (exclusiveMarginal_bounds Γ j z.1 z.2).2
  have hb := Exclusive.supported_binomial_mixture_bounds (exclusivePopulationLaw Γ)
    (exclusivePopulationMarginal Γ j) hp hp0 hp1 (exclusiveActiveEvent Γ)
    (measurableSet_exclusiveActiveEvent Γ)
    (exclusivePopulationMarginal_supported Γ hm h.users h.visible_atomless j)
    (he.symm ▸ hh) n hn ((c : ℝ) / m) (exclusivePopulationMarginal_capacity Γ hm j)
  simp only [he, ← ha.coverage_identity, ← ha.load_identity] at hb
  have hratio : ((c : ℝ) / m) / exclusiveActiveMass Γ =
      (c : ℝ) / ((m : ℝ) * exclusiveActiveMass Γ) := div_div _ _ _
  exact
    { coverage := by simpa only [hratio, PayOnce.success] using hb.1
      duplicates_second_moment := hb.2.1
      active_cauchy_schwarz := hb.2.2.1
      duplicates_coverage := hb.2.2.2 }

theorem exclusive_once_zero_active_mass (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ)
    (h : ExclusiveOnceEquilibrium Γ B) (j : Fin n) (hh : exclusiveActiveMass Γ = 0) :
    finiteCoverage Γ = 0 ∧ finiteLoad Γ = 0 := by
  have hm : 0 < m := lt_trans hc hcm
  letI : NeZero m := ⟨hm.ne'⟩
  have ha := exclusive_once_actual Γ hc hcm B h j
  have hz := Exclusive.supported_binomial_mixture_zero (exclusivePopulationLaw Γ)
    (exclusivePopulationMarginal Γ j) (exclusiveActiveEvent Γ)
    ((exclusiveActiveEvent_mass Γ hm).trans hh)
    (exclusivePopulationMarginal_supported Γ hm h.users h.visible_atomless j) n
  rw [ha.coverage_identity, ha.load_identity, hz.2.1, hz.2.2, mul_zero]
  exact ⟨rfl, rfl⟩

theorem exclusive_once_finite (Γ : FiniteGame m n c Seed)
    (_hn : 2 ≤ n) (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ)
    (h : ExclusiveOnceEquilibrium Γ B) :
    ∀ j : Fin n, ExclusiveOnceActualConclusion Γ j ∧
      (0 < exclusiveActiveMass Γ → ExclusiveOnceContributionBounds Γ j) ∧
      (exclusiveActiveMass Γ = 0 → finiteCoverage Γ = 0 ∧ finiteLoad Γ = 0) := by
  intro j
  exact ⟨exclusive_once_actual Γ hc hcm B h j,
    exclusive_once_contribution_bounds Γ hc hcm B h j,
    exclusive_once_zero_active_mass Γ hc hcm B h j⟩

theorem exclusive_once_duplicates_pos (Γ : FiniteGame m n c Seed)
    (hn : 2 ≤ n) (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ)
    (h : ExclusiveOnceEquilibrium Γ B) (hh : 0 < exclusiveActiveMass Γ)
    (hQ : 0 < finiteCoverage Γ) : 0 < finiteLoad Γ - finiteCoverage Γ := by
  let j : Fin n := ⟨0, by omega⟩
  have hb := (exclusive_once_contribution_bounds Γ hc hcm B h j hh).duplicates_coverage
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < ((n : ℝ) - 1) * finiteCoverage Γ ^ 2 /
      ((n : ℝ) ^ 2 * exclusiveActiveMass Γ) := by
    apply div_pos
    · exact mul_pos (by linarith) (sq_pos_of_pos hQ)
    · exact mul_pos (sq_pos_of_pos (by linarith)) hh
  exact hpos.trans_le hb

theorem exclusive_once_coverage_strict (Γ : FiniteGame m n c Seed)
    (hn : 2 ≤ n) (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ)
    (h : ExclusiveOnceEquilibrium Γ B) (hh : 0 < exclusiveActiveMass Γ)
    (hscarce : (c : ℝ) / m < exclusiveActiveMass Γ) :
    finiteCoverage Γ < min ((n : ℝ) * ((c : ℝ) / m)) (exclusiveActiveMass Γ) := by
  let j : Fin n := ⟨0, by omega⟩
  have hb := (exclusive_once_contribution_bounds Γ hc hcm B h j hh).coverage
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_trans hc hcm)
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hratio : (c : ℝ) / ((m : ℝ) * exclusiveActiveMass Γ) =
      ((c : ℝ) / m) / exclusiveActiveMass Γ := (div_div _ _ _).symm
  rw [hratio, min_eq_left ((div_lt_one hh).mpr hscarce).le] at hb
  exact hb.trans_lt (Exclusive.once_coverage_cap_strict n hn (exclusiveActiveMass Γ)
    ((c : ℝ) / m) hh (div_pos hcR hmR) hscarce)

end FCAppendix.Bayes
