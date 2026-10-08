import FCAppendix.Exclusive.OnceBayes
import FCAppendix.Exclusive.Kernel

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def exclusiveListedBid (ℓ : LocalList m) (i : Fin m) : ℝ :=
  match ℓ i with
  | none => 0
  | some b => b

noncomputable def exclusiveItemReward (Γ : FiniteGame m n c Seed)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m) (ω : Background m n Seed) : ℝ :=
  exclusiveListedBid ℓ i * if (otherInclusionCount Γ j i ω).val = 0 then 1 else 0

theorem exclusive_playedCount_eq_other_add (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (ω : Background m n Seed) :
    (playedCount Γ i ω).val = (otherInclusionCount Γ j i ω).val +
      if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then 1 else 0 := by
  classical
  change inclusionCount (drawsRealization ω.1) Γ.policy ω.2 i = _
  rw [inclusionCount_eq_sum, otherInclusionCount_eq_sum]
  exact (Finset.sum_erase_add Finset.univ
    (fun l => if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 l then (1 : ℕ) else 0)
    (Finset.mem_univ j)).symm

noncomputable def exclusiveRealizedReward (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (ω : Background m n Seed) : ℝ :=
  if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j ∧
      (playedCount Γ i ω).val = 1 then (ω.1 i).1.2.bid else 0

theorem exclusiveRealizedReward_eq_item (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (ω : Background m n Seed) :
    exclusiveRealizedReward Γ j i ω =
      if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then
        exclusiveItemReward Γ j (observe (drawsRealization ω.1) j) i ω else 0 := by
  classical
  by_cases hi : i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j
  · have hr : j ∈ firstK (ω.1 i).2 (ω.1 i).1.2.routeCount := by
      exact accepted_subset_recipients (drawsRealization ω.1) Γ.policy ω.2 i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hi⟩)
    have hc := exclusive_playedCount_eq_other_add Γ j i ω
    simp only [if_pos hi] at hc
    have he : (playedCount Γ i ω).val = 1 ↔ (otherInclusionCount Γ j i ω).val = 0 := by
      omega
    have hentry : observe (drawsRealization ω.1) j i = some (ω.1 i).1.2.bid := by
      simp only [observe, drawsRealization, hr, if_true]
    have hb : exclusiveListedBid (observe (drawsRealization ω.1) j) i = (ω.1 i).1.2.bid := by
      simp only [exclusiveListedBid, hentry]
    simp only [exclusiveRealizedReward, hi, true_and, he, if_true, exclusiveItemReward, hb]
    split <;> simp
  · simp only [exclusiveRealizedReward, hi, false_and, if_false]

noncomputable def exclusivePosteriorRevenue (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (S : Finset (Fin m)) : ℝ :=
  ∫ ω, ∑ i ∈ S, exclusiveItemReward Γ j ℓ i ω ∂posteriorBackground Γ B j ℓ

theorem integrable_exclusiveItemReward (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (i : Fin m) :
    Integrable (exclusiveItemReward Γ j ℓ i) (posteriorBackground Γ B j ℓ) := by
  have hm : Measurable (fun ω : Background m n Seed =>
      if (otherInclusionCount Γ j i ω).val = 0 then (1 : ℝ) else 0) :=
    (measurable_of_countable (fun r : Fin n => if r.val = 0 then (1 : ℝ) else 0)).comp
      (measurable_otherInclusionCount Γ j i)
  have hi : Integrable (fun ω : Background m n Seed =>
      if (otherInclusionCount Γ j i ω).val = 0 then (1 : ℝ) else 0)
      (posteriorBackground Γ B j ℓ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall fun ω => by split <;> norm_num
  exact hi.const_mul (exclusiveListedBid ℓ i)

theorem exclusiveItemReward_update_seed (Γ : FiniteGame m n c Seed)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m)
    (d : UserProfile m n) (s : Fin n → Seed) (u : Seed) :
    exclusiveItemReward Γ j ℓ i (d, Function.update s j u) =
      exclusiveItemReward Γ j ℓ i (d, s) := by
  simp only [exclusiveItemReward, otherInclusionCount_update_seed]

theorem integral_exclusiveItemReward (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (i : Fin m) :
    (∫ ω, exclusiveItemReward Γ j ℓ i ω ∂posteriorBackground Γ B j ℓ) =
      exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i := by
  unfold exclusiveItemReward
  rw [integral_const_mul, ← noOtherProb_eq_integral]
  cases hi : ℓ i <;> simp [exclusiveListedBid, exclusiveReceipts, hi, noOtherProb]

theorem exclusivePosteriorRevenue_eq_sum (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (S : Finset (Fin m)) :
    exclusivePosteriorRevenue Γ B j ℓ S =
      ∑ i ∈ S, exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i := by
  unfold exclusivePosteriorRevenue
  rw [integral_finsetSum S (fun i _ => integrable_exclusiveItemReward Γ B j ℓ i)]
  exact Finset.sum_congr rfl fun i _ => integral_exclusiveItemReward Γ B j ℓ i

def ExclusiveProposersOptimalAE (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) : Prop :=
  ∀ j ℓ, FeasibleObservedList j ℓ → ∀ᵐ s ∂Γ.seedLaw,
    ∀ T : Finset (Fin m), T.card ≤ c → (∀ i ∈ T, ℓ i ≠ none) →
      exclusivePosteriorRevenue Γ B j ℓ T ≤
        exclusivePosteriorRevenue Γ B j ℓ (Γ.policy j ℓ s).val

theorem exclusiveReceipts_sum_filter (belief : Fin m → FiniteLaw (Fin n))
    (ℓ : LocalList m) (T : Finset (Fin m)) :
    (∑ i ∈ T.filter (fun i => ℓ i ≠ none), exclusiveReceipts belief ℓ i) =
      ∑ i ∈ T, exclusiveReceipts belief ℓ i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ℓ i = none
  · simp [h, exclusiveReceipts_none belief ℓ i h]
  · simp [h]

theorem ExclusiveProposersOptimalAE.to_receipt_optimal
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (h : ExclusiveProposersOptimalAE Γ B) : ExclusivePosteriorOptimalAE Γ B := by
  classical
  intro j ℓ hℓ
  filter_upwards [h j ℓ hℓ] with s hs
  refine ⟨(Γ.policy j ℓ s).property.1, ?_⟩
  intro T hT
  have ht := hs (T.filter fun i => ℓ i ≠ none)
    ((Finset.card_filter_le _ _).trans hT)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  simpa only [exclusivePosteriorRevenue_eq_sum, exclusiveReceipts_sum_filter] using ht

theorem ExclusivePosteriorOptimalAE.to_primitive
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (h : ExclusivePosteriorOptimalAE Γ B) : ExclusiveProposersOptimalAE Γ B := by
  intro j ℓ hℓ
  filter_upwards [h j ℓ hℓ] with s hs T hT _
  simpa only [exclusivePosteriorRevenue_eq_sum] using hs.2 T hT

theorem exclusiveProposersOptimalAE_iff_receipt_optimal
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) :
    ExclusiveProposersOptimalAE Γ B ↔ ExclusivePosteriorOptimalAE Γ B :=
  ⟨ExclusiveProposersOptimalAE.to_receipt_optimal Γ B,
    ExclusivePosteriorOptimalAE.to_primitive Γ B⟩

def ExclusiveProposersBestRespond (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) : Prop :=
  ∀ j, ∀ᵐ ℓ ∂observedListLaw Γ j,
    ∀ T : Finset (Fin m), T.card ≤ c → (∀ i ∈ T, ℓ i ≠ none) →
      exclusivePosteriorRevenue Γ B j ℓ T ≤
        (seedLottery Γ j ℓ).expect (exclusivePosteriorRevenue Γ B j ℓ)

theorem exclusive_policyRevenue_eq_integral (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) :
    (seedLottery Γ j ℓ).expect (exclusivePosteriorRevenue Γ B j ℓ) =
      ∫ s, exclusivePosteriorRevenue Γ B j ℓ (Γ.policy j ℓ s).val ∂Γ.seedLaw := by
  rw [seedLottery, FiniteLaw.expect_ofMeasure]

theorem exclusive_seedLottery_ae_support (Γ : FiniteGame m n c Seed)
    (j : Fin n) (ℓ : LocalList m) :
    ∀ᵐ s ∂Γ.seedLaw, (seedLottery Γ j ℓ).mass (Γ.policy j ℓ s).val ≠ 0 := by
  classical
  have hz (S : Finset (Fin m)) (hS : (seedLottery Γ j ℓ).mass S = 0) :
      Γ.seedLaw {s | (Γ.policy j ℓ s).val = S} = 0 := by
    have hreal : (Γ.seedLaw {s | (Γ.policy j ℓ s).val = S}).toReal = 0 := by
      simpa only [seedLottery, FiniteLaw.ofMeasure_mass] using hS
    exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right (measure_ne_top _ _)
  have hall : ∀ᵐ s ∂Γ.seedLaw, ∀ S : Finset (Fin m),
      (seedLottery Γ j ℓ).mass S = 0 → (Γ.policy j ℓ s).val ≠ S := by
    apply ae_all_iff.mpr
    intro S
    by_cases hS : (seedLottery Γ j ℓ).mass S = 0
    · exact (measure_eq_zero_iff_ae_notMem.mp (hz S hS)).mono fun _ hs _ => hs
    · exact Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hall] with s hs hzero
  exact hs _ hzero rfl

theorem exclusive_seedLottery_support_exists_ae (Γ : FiniteGame m n c Seed)
    (j : Fin n) (ℓ : LocalList m) (S : Finset (Fin m))
    (hS : (seedLottery Γ j ℓ).mass S ≠ 0) (P : Seed → Prop)
    (hP : ∀ᵐ s ∂Γ.seedLaw, P s) :
    ∃ s, (Γ.policy j ℓ s).val = S ∧ P s := by
  have hm : Γ.seedLaw {s | (Γ.policy j ℓ s).val = S} ≠ 0 := by
    intro hzero
    apply hS
    rw [seedLottery, FiniteLaw.ofMeasure_mass, hzero, ENNReal.toReal_zero]
  obtain ⟨s, hs, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hP)
  exact ⟨s, hs, hp⟩

theorem ExclusiveProposersBestRespond.to_receipt_optimal_onPath
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (h : ExclusiveProposersBestRespond Γ B) : ExclusivePosteriorOptimalOnPath Γ B := by
  classical
  intro j
  filter_upwards [h j] with ℓ hℓ
  let r := exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ
  let μ := seedLottery Γ j ℓ
  have hmean : μ.expect (exclusivePosteriorRevenue Γ B j ℓ) = Proposer.revenue μ r := by
    change μ.expect (exclusivePosteriorRevenue Γ B j ℓ) =
      μ.expect (fun S => ∑ i ∈ S, r i)
    apply μ.expect_congr
    intro S
    exact exclusivePosteriorRevenue_eq_sum Γ B j ℓ S
  have hpure (T : Finset (Fin m)) (hT : T.card ≤ c) :
      (∑ i ∈ T, r i) ≤ Proposer.revenue μ r := by
    have ht := hℓ (T.filter fun i => ℓ i ≠ none)
      ((Finset.card_filter_le _ _).trans hT)
      (fun i hi => (Finset.mem_filter.mp hi).2)
    change exclusivePosteriorRevenue Γ B j ℓ (T.filter fun i => ℓ i ≠ none) ≤
      μ.expect (exclusivePosteriorRevenue Γ B j ℓ) at ht
    rw [hmean, exclusivePosteriorRevenue_eq_sum, exclusiveReceipts_sum_filter] at ht
    exact ht
  have hbr (ν : FiniteLaw (Finset (Fin m))) (hν : CommonList.Feasible c ν) :
      Proposer.revenue ν r ≤ Proposer.revenue μ r := by
    exact ν.expect_le_const_of_support _ _ (fun T hT => hpure T (hν T hT))
  have hsupp := CommonList.support_optimal c r μ (seedLottery_feasible Γ j ℓ) hbr
  filter_upwards [exclusive_seedLottery_ae_support Γ j ℓ] with s hs
  exact hsupp _ hs

theorem ExclusivePosteriorOptimalOnPath.to_mixed_bestRespond
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (h : ExclusivePosteriorOptimalOnPath Γ B) : ExclusiveProposersBestRespond Γ B := by
  intro j
  filter_upwards [h j] with ℓ hℓ T hT _
  apply FiniteLaw.const_le_expect_of_support
  intro S hS
  obtain ⟨s, hs, ho⟩ := exclusive_seedLottery_support_exists_ae Γ j ℓ S hS _ hℓ
  rw [← hs]
  simpa only [exclusivePosteriorRevenue_eq_sum] using ho.2 T hT

theorem exclusiveProposersBestRespond_iff_receipt_optimal_onPath
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) :
    ExclusiveProposersBestRespond Γ B ↔ ExclusivePosteriorOptimalOnPath Γ B :=
  ⟨ExclusiveProposersBestRespond.to_receipt_optimal_onPath Γ B,
    ExclusivePosteriorOptimalOnPath.to_mixed_bestRespond Γ B⟩

theorem exclusive_mixed_deviation_le (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (s : Seed)
    (hs : Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ)
      (Γ.policy j ℓ s).val)
    (ν : FiniteLaw (Finset (Fin m))) (hν : CommonList.Feasible c ν) :
    ν.expect (exclusivePosteriorRevenue Γ B j ℓ) ≤
      exclusivePosteriorRevenue Γ B j ℓ (Γ.policy j ℓ s).val := by
  apply FiniteLaw.expect_le_const_of_support
  intro T hT
  simpa only [exclusivePosteriorRevenue_eq_sum] using hs.2 T (hν T hT)

theorem integral_weighted_exclusive_eq_posterior
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) (j : Fin n) (i : Fin m)
    (w : LocalList m → ℝ) (hw : Measurable w) (R : ℝ) (hR : ∀ ℓ, ‖w ℓ‖ ≤ R) :
    (∫ ω : Background m n Seed,
      (if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then
        w (observe (drawsRealization ω.1) j) else 0) *
          (if (otherInclusionCount Γ j i ω).val = 0 then 1 else 0) ∂backgroundLaw Γ) =
    ∫ ℓ, ∫ s, (if i ∈ (Γ.policy j ℓ s).val then w ℓ else 0) * noOtherProb Γ B j ℓ i
        ∂Γ.seedLaw ∂observedListLaw Γ j := by
  classical
  let f : LocalList m × Seed → ℝ := fun z =>
    if i ∈ (Γ.policy j z.1 z.2).val then w z.1 else 0
  let g : (LocalList m × UserProfile m n) × (Fin n → Seed) → ℝ := fun z =>
    if (otherInclusionCount Γ j i (z.1.2, z.2)).val = 0 then 1 else 0
  have hf : Measurable f := Measurable.ite
    ((Γ.policy_measurable j) (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
    (hw.comp measurable_fst) measurable_const
  have hg : Measurable g := ((measurable_of_countable
    (fun r : Fin n => if r.val = 0 then (1 : ℝ) else 0)).comp
      (measurable_otherInclusionCount Γ j i)).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hfb : ∀ z, ‖f z‖ ≤ R := by
    intro z
    dsimp only [f]
    split
    · exact hR z.1
    · simpa only [norm_zero] using (norm_nonneg (w z.1)).trans (hR z.1)
  have hgb : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    dsimp only [g]
    split <;> norm_num
  have heq := ConditionalAveraging.integral_observation_private_seed
    (userProfileLaw Γ) (observedListLaw Γ j) Γ.seedLaw
    (fun d => observe (drawsRealization d) j) (measurable_observe_draws j)
    (B.posterior j) (B.on_path j) j f g hf hg R 1 hfb hgb
    (fun _ d s u => by dsimp only [g]; rw [otherInclusionCount_update_seed])
  calc
    _ = ∫ ℓ, (∫ s, f (ℓ, s) ∂Γ.seedLaw) *
        (∫ ω : Background m n Seed,
          (if (otherInclusionCount Γ j i ω).val = 0 then 1 else 0)
            ∂posteriorBackground Γ B j ℓ) ∂observedListLaw Γ j := heq
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ℓ
      dsimp only
      rw [noOtherProb_eq_integral]
      exact (integral_mul_const _ _).symm

theorem posterior_exclusive_receipts_of_visible {k : ℕ} (Γ : FiniteGame m (k + 1) c Seed)
    (B : PosteriorSystem Γ) (j : Fin (k + 1)) (ℓ : LocalList m)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ)
    (i : Fin m) (b : ℝ) (hi : ℓ i = some b) :
    exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i =
      b * (1 - Proposer.marginal μ i) ^ k := by
  rw [exclusiveReceipts_some _ _ i b hi,
    posteriorCountBelief_binomial Γ B j ℓ hcommon μ hμ i]
  exact Exclusive.exclusive_receipt k (Proposer.marginal μ i) b
    (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i)

theorem noOtherProb_commonList (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) (i : Fin m) :
    noOtherProb Γ B j ℓ i = (1 - Proposer.marginal μ i) ^ (n - 1) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ k =>
    rw [noOtherProb, posteriorCountBelief_binomial Γ B j ℓ hcommon μ hμ i]
    simpa only [one_mul, Nat.succ_sub_one] using
      (Exclusive.exclusive_receipt k (Proposer.marginal μ i) 1
        (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i))

theorem exclusiveReceipts_eq_listedBid_mul_noOther (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (i : Fin m) :
    exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i =
      exclusiveListedBid ℓ i * noOtherProb Γ B j ℓ i := by
  cases hi : ℓ i <;> simp only [exclusiveReceipts, exclusiveListedBid, hi, noOtherProb, zero_mul]

theorem integral_exclusive_selected_item (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (i : Fin m) :
    (∫ ω : Background m n Seed,
      (if i ∈ (Γ.policy j ℓ (ω.2 j)).val then exclusiveItemReward Γ j ℓ i ω else 0)
        ∂posteriorBackground Γ B j ℓ) =
    ∫ u, (if i ∈ (Γ.policy j ℓ u).val then
      exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i else 0) ∂Γ.seedLaw := by
  classical
  let f : Seed → ℝ := fun u =>
    if i ∈ (Γ.policy j ℓ u).val then exclusiveListedBid ℓ i else 0
  let g : Background m n Seed → ℝ := fun ω =>
    if (otherInclusionCount Γ j i ω).val = 0 then 1 else 0
  have hf : Measurable f := Measurable.ite
    ((measurable_policy_at_list Γ j ℓ)
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
    measurable_const measurable_const
  have hg : Measurable g :=
    (measurable_of_countable (fun r : Fin n => if r.val = 0 then (1 : ℝ) else 0)).comp
      (measurable_otherInclusionCount Γ j i)
  have hfb : ∀ u, ‖f u‖ ≤ ‖exclusiveListedBid ℓ i‖ := by
    intro u
    dsimp only [f]
    split <;> simp
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := by
    intro ω
    dsimp only [g]
    split <;> norm_num
  have he := Resample.integral_mul_coordinate_prod_of_invariant
    (B.posterior j ℓ) Γ.seedLaw j f g hf hg
    ‖exclusiveListedBid ℓ i‖ 1 hfb hgb
    (fun d s u => by dsimp only [g]; rw [otherInclusionCount_update_seed])
  calc
    _ = ∫ ω : Background m n Seed, f (ω.2 j) * g ω ∂posteriorBackground Γ B j ℓ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        simp only [f, g, exclusiveItemReward, ite_mul, zero_mul]
    _ = (∫ u, f u ∂Γ.seedLaw) * noOtherProb Γ B j ℓ i := by
      rw [noOtherProb_eq_integral]
      exact he
    _ = ∫ u, f u * noOtherProb Γ B j ℓ i ∂Γ.seedLaw := (integral_mul_const _ _).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        simp only [exclusiveReceipts_eq_listedBid_mul_noOther, f, ite_mul, zero_mul]

theorem exclusive_policyRevenue_eq_joint_integral (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) :
    (seedLottery Γ j ℓ).expect (exclusivePosteriorRevenue Γ B j ℓ) =
      ∫ ω : Background m n Seed,
        ∑ i ∈ (Γ.policy j ℓ (ω.2 j)).val, exclusiveItemReward Γ j ℓ i ω
          ∂posteriorBackground Γ B j ℓ := by
  classical
  have hfinite (S : Finset (Fin m)) (r : Fin m → ℝ) :
      (∑ i ∈ S, r i) = ∑ i, if i ∈ S then r i else 0 := by
    rw [← Finset.sum_filter]
    simp
  have hleft (i : Fin m) : Integrable (fun u =>
      if i ∈ (Γ.policy j ℓ u).val then
        exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i else (0 : ℝ)) Γ.seedLaw := by
    have hm : Measurable (fun u => if i ∈ (Γ.policy j ℓ u).val then
        exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i else (0 : ℝ)) :=
      Measurable.ite ((measurable_policy_at_list Γ j ℓ)
        (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
        measurable_const measurable_const
    apply Integrable.of_bound hm.aestronglyMeasurable
      ‖exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i‖
    exact Eventually.of_forall fun u => by split <;> simp
  have hright (i : Fin m) : Integrable (fun ω : Background m n Seed =>
      if i ∈ (Γ.policy j ℓ (ω.2 j)).val then exclusiveItemReward Γ j ℓ i ω else 0)
        (posteriorBackground Γ B j ℓ) := by
    have hm : MeasurableSet {ω : Background m n Seed | i ∈ (Γ.policy j ℓ (ω.2 j)).val} :=
      ((measurable_policy_at_list Γ j ℓ).comp
        ((measurable_pi_apply j).comp measurable_snd))
        (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
    apply ((integrable_exclusiveItemReward Γ B j ℓ i).indicator hm).congr
    exact Eventually.of_forall fun ω => by
      by_cases h : i ∈ (Γ.policy j ℓ (ω.2 j)).val <;> simp [Set.indicator, h]
  have hseed (u : Seed) :
      (∑ i ∈ (Γ.policy j ℓ u).val, exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i) =
      ∑ i, if i ∈ (Γ.policy j ℓ u).val then
        exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ i else 0 := hfinite _ _
  have hplayed (ω : Background m n Seed) :
      (∑ i ∈ (Γ.policy j ℓ (ω.2 j)).val, exclusiveItemReward Γ j ℓ i ω) =
      ∑ i, if i ∈ (Γ.policy j ℓ (ω.2 j)).val then exclusiveItemReward Γ j ℓ i ω else 0 :=
    hfinite _ _
  rw [exclusive_policyRevenue_eq_integral]
  simp_rw [exclusivePosteriorRevenue_eq_sum, hseed, hplayed]
  rw [integral_finsetSum _ (fun i _ => hleft i),
    integral_finsetSum _ (fun i _ => hright i)]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_exclusive_selected_item Γ B j ℓ i).symm

theorem exclusive_policyRevenue_eq_realized_onPath (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) :
    ∀ᵐ ℓ ∂observedListLaw Γ j,
      (seedLottery Γ j ℓ).expect (exclusivePosteriorRevenue Γ B j ℓ) =
        ∫ ω, ∑ i, exclusiveRealizedReward Γ j i ω ∂posteriorBackground Γ B j ℓ := by
  classical
  filter_upwards [B.ae_observation Γ j] with ℓ hℓ
  rw [exclusive_policyRevenue_eq_joint_integral]
  have hobs := (measurePreserving_fst (μ := B.posterior j ℓ)
    (ν := Measure.pi fun _ : Fin n => Γ.seedLaw)).quasiMeasurePreserving.ae hℓ
  apply integral_congr_ae
  filter_upwards [hobs] with ω hω
  have hfinite (S : Finset (Fin m)) (r : Fin m → ℝ) :
      (∑ i ∈ S, r i) = ∑ i, if i ∈ S then r i else 0 := by
    rw [← Finset.sum_filter]
    simp
  calc
    _ = ∑ i, if i ∈ (Γ.policy j ℓ (ω.2 j)).val then
        exclusiveItemReward Γ j ℓ i ω else 0 := hfinite _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [exclusiveRealizedReward_eq_item, allocation, hω]
      rw [hω]

theorem exclusive_realizedRevenue_integrable_onPath (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) :
    ∀ᵐ ℓ ∂observedListLaw Γ j,
      Integrable (fun ω => ∑ i, exclusiveRealizedReward Γ j i ω)
        (posteriorBackground Γ B j ℓ) := by
  classical
  filter_upwards [B.ae_observation Γ j] with ℓ hℓ
  have hobs := (measurePreserving_fst (μ := B.posterior j ℓ)
    (ν := Measure.pi fun _ : Fin n => Γ.seedLaw)).quasiMeasurePreserving.ae hℓ
  apply integrable_finsetSum
  intro i _
  have hm : MeasurableSet {ω : Background m n Seed | i ∈ (Γ.policy j ℓ (ω.2 j)).val} :=
    ((measurable_policy_at_list Γ j ℓ).comp
      ((measurable_pi_apply j).comp measurable_snd))
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
  have hi := (integrable_exclusiveItemReward Γ B j ℓ i).indicator hm
  apply hi.congr
  filter_upwards [hobs] with ω hω
  simp only [Set.indicator, Set.mem_setOf_eq, exclusiveRealizedReward_eq_item, allocation, hω]
  rw [hω]
  split_ifs <;> rfl

theorem exclusiveProposersBestRespond_iff_actual_revenue
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) :
    ExclusiveProposersBestRespond Γ B ↔
      ∀ j, ∀ᵐ ℓ ∂observedListLaw Γ j,
        ∀ T : Finset (Fin m), T.card ≤ c → (∀ i ∈ T, ℓ i ≠ none) →
          exclusivePosteriorRevenue Γ B j ℓ T ≤
            ∫ ω, ∑ i, exclusiveRealizedReward Γ j i ω ∂posteriorBackground Γ B j ℓ := by
  constructor
  · intro h j
    filter_upwards [h j, exclusive_policyRevenue_eq_realized_onPath Γ B j] with ℓ hℓ he
    simpa only [he] using hℓ
  · intro h j
    filter_upwards [h j, exclusive_policyRevenue_eq_realized_onPath Γ B j] with ℓ hℓ he
    simpa only [he] using hℓ

end FCAppendix.Bayes
