import FCAppendix.Game.PosteriorBeliefs
import FCAppendix.Proposer.CommonListGame

namespace FCAppendix

open MeasureTheory
open scoped BigOperators

namespace FiniteLaw

theorem ofMeasure_pi_eq_iid {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ)
    (f : Fin k → Ω → α) (hf : ∀ j, Measurable (f j)) (ν : FiniteLaw α)
    (hν : ∀ j, ofMeasure μ (f j) (hf j) = ν) :
    ofMeasure (Measure.pi fun _ : Fin k => μ) (fun s j => f j (s j))
      (measurable_pi_lambda _ fun j => (hf j).comp (measurable_pi_apply j)) =
        CommonList.iid ν k := by
  classical
  apply FiniteLaw.ext
  intro t
  rw [ofMeasure_mass]
  have he : {s : Fin k → Ω | (fun j => f j (s j)) = t} =
      Set.univ.pi (fun j => {x | f j x = t j}) := by
    ext s
    simp [funext_iff]
  rw [he, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ j, _) = ∏ j, ν.mass (t j)
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← ofMeasure_mass μ (f j) (hf j), hν j]

end FiniteLaw

namespace Bayes

open Game

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_policy_at_list (Γ : FiniteGame m n c Seed) (j : Fin n)
    (ℓ : LocalList m) : Measurable (fun s => (Γ.policy j ℓ s).val) :=
  (Γ.policy_measurable j).comp (measurable_const.prodMk measurable_id)

noncomputable def seedLottery (Γ : FiniteGame m n c Seed) (j : Fin n)
    (ℓ : LocalList m) : FiniteLaw (Finset (Fin m)) :=
  FiniteLaw.ofMeasure Γ.seedLaw (fun s => (Γ.policy j ℓ s).val)
    (measurable_policy_at_list Γ j ℓ)

theorem seedLottery_feasible (Γ : FiniteGame m n c Seed) (j : Fin n) (ℓ : LocalList m) :
    CommonList.Feasible c (seedLottery Γ j ℓ) := by
  classical
  intro S hS
  by_contra hc
  have hnone : ∀ s, (Γ.policy j ℓ s).val ≠ S := by
    intro s hs
    exact hc (hs ▸ (Γ.policy j ℓ s).property.1)
  have hz : (seedLottery Γ j ℓ).mass S = 0 := by
    simp [seedLottery, FiniteLaw.ofMeasure, hnone]
  exact hS hz

theorem seedLottery_support_exists (Γ : FiniteGame m n c Seed) (j : Fin n)
    (ℓ : LocalList m) (S : Finset (Fin m)) (hS : (seedLottery Γ j ℓ).mass S ≠ 0) :
    ∃ s, (Γ.policy j ℓ s).val = S := by
  classical
  by_contra h
  push Not at h
  exact hS (by simp [seedLottery, FiniteLaw.ofMeasure, h])

def SymmetricAtList (Γ : FiniteGame m n c Seed) (ℓ : LocalList m)
    (μ : FiniteLaw (Finset (Fin m))) : Prop :=
  ∀ j, seedLottery Γ j ℓ = μ

noncomputable def commonSeedAllocations (Γ : FiniteGame m n c Seed) (ℓ : LocalList m)
    (s : Fin n → Seed) : Fin n → Finset (Fin m) := fun j => (Γ.policy j ℓ (s j)).val

theorem measurable_commonSeedAllocations (Γ : FiniteGame m n c Seed) (ℓ : LocalList m) :
    Measurable (commonSeedAllocations Γ ℓ) :=
  measurable_pi_lambda _ fun j => (measurable_policy_at_list Γ j ℓ).comp
    (measurable_pi_apply j)

theorem commonSeedAllocations_law (Γ : FiniteGame m n c Seed) (ℓ : LocalList m)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    FiniteLaw.ofMeasure (Measure.pi fun _ : Fin n => Γ.seedLaw)
      (commonSeedAllocations Γ ℓ) (measurable_commonSeedAllocations Γ ℓ) =
        CommonList.iid μ n :=
  FiniteLaw.ofMeasure_pi_eq_iid Γ.seedLaw n (fun j s => (Γ.policy j ℓ s).val)
    (fun j => measurable_policy_at_list Γ j ℓ) μ hμ

noncomputable def commonSeedCount (Γ : FiniteGame m n c Seed) (ℓ : LocalList m)
    (i : Fin m) (s : Fin n → Seed) : Fin (n + 1) :=
  CommonList.includersCount i (commonSeedAllocations Γ ℓ s)

theorem measurable_commonSeedCount (Γ : FiniteGame m n c Seed) (ℓ : LocalList m)
    (i : Fin m) : Measurable (commonSeedCount Γ ℓ i) :=
  (measurable_of_countable (CommonList.includersCount i)).comp
    (measurable_commonSeedAllocations Γ ℓ)

theorem commonSeedCount_binomial (Γ : FiniteGame m n c Seed) (ℓ : LocalList m)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) (i : Fin m) :
    FiniteLaw.ofMeasure (Measure.pi fun _ : Fin n => Γ.seedLaw)
      (commonSeedCount Γ ℓ i) (measurable_commonSeedCount Γ ℓ i) =
      IndependentCounts.binomial n (Proposer.marginal μ i)
        (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i) := by
  change FiniteLaw.ofMeasure _ (CommonList.includersCount i ∘
    commonSeedAllocations Γ ℓ) _ = _
  rw [← FiniteLaw.ofMeasure_map _ _ (measurable_commonSeedAllocations Γ ℓ)
    _ (measurable_of_countable _), commonSeedAllocations_law Γ ℓ μ hμ]
  exact CommonList.iid_includers_law μ i n

theorem boundedCount_eq_commonSeedCount (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (ℓ : LocalList m)
    (hd : ∀ j, observe (drawsRealization d) j = ℓ) (i : Fin m) (s : Fin n → Seed) :
    boundedCount (drawsRealization d) Γ.policy s i = commonSeedCount Γ ℓ i s := by
  apply Fin.ext
  simp only [boundedCount, inclusionCount_eq_sum, commonSeedCount,
    CommonList.includersCount, CommonList.includers]
  apply Finset.sum_congr rfl
  intro j _
  have he : allocation (drawsRealization d) Γ.policy s j =
      commonSeedAllocations Γ ℓ s j :=
    congrArg (fun L => (Γ.policy j L (s j)).val) (hd j)
  split_ifs <;> simp_all

section OtherProposers

variable {k : ℕ}

theorem measurePreserving_otherSeeds (μ : Measure Seed) [IsProbabilityMeasure μ]
    (j : Fin (k + 1)) :
    MeasurePreserving (fun s : Fin (k + 1) → Seed => fun l => s (j.succAbove l))
      (Measure.pi fun _ : Fin (k + 1) => μ) (Measure.pi fun _ : Fin k => μ) := by
  exact (measurePreserving_snd (μ := μ) (ν := Measure.pi fun _ : Fin k => μ)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) j)

noncomputable def otherSeedAllocations (Γ : FiniteGame m (k + 1) c Seed)
    (j : Fin (k + 1)) (ℓ : LocalList m) (s : Fin k → Seed) : Fin k → Finset (Fin m) :=
  fun l => (Γ.policy (j.succAbove l) ℓ (s l)).val

theorem measurable_otherSeedAllocations (Γ : FiniteGame m (k + 1) c Seed)
    (j : Fin (k + 1)) (ℓ : LocalList m) : Measurable (otherSeedAllocations Γ j ℓ) :=
  measurable_pi_lambda _ fun l =>
    (measurable_policy_at_list Γ (j.succAbove l) ℓ).comp (measurable_pi_apply l)

noncomputable def otherSeedCount (Γ : FiniteGame m (k + 1) c Seed)
    (j : Fin (k + 1)) (ℓ : LocalList m) (i : Fin m) (s : Fin k → Seed) : Fin (k + 1) :=
  CommonList.includersCount i (otherSeedAllocations Γ j ℓ s)

theorem measurable_otherSeedCount (Γ : FiniteGame m (k + 1) c Seed)
    (j : Fin (k + 1)) (ℓ : LocalList m) (i : Fin m) : Measurable (otherSeedCount Γ j ℓ i) :=
  (measurable_of_countable (CommonList.includersCount i)).comp
    (measurable_otherSeedAllocations Γ j ℓ)

theorem otherSeedCount_binomial (Γ : FiniteGame m (k + 1) c Seed)
    (j : Fin (k + 1)) (ℓ : LocalList m) (μ : FiniteLaw (Finset (Fin m)))
    (hμ : SymmetricAtList Γ ℓ μ) (i : Fin m) :
    FiniteLaw.ofMeasure (Measure.pi fun _ : Fin k => Γ.seedLaw)
      (otherSeedCount Γ j ℓ i) (measurable_otherSeedCount Γ j ℓ i) =
      IndependentCounts.binomial k (Proposer.marginal μ i)
        (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i) := by
  have halloc := FiniteLaw.ofMeasure_pi_eq_iid Γ.seedLaw k
    (fun l s => (Γ.policy (j.succAbove l) ℓ s).val)
    (fun l => measurable_policy_at_list Γ (j.succAbove l) ℓ) μ (fun l => hμ (j.succAbove l))
  change FiniteLaw.ofMeasure _ (otherSeedAllocations Γ j ℓ)
    (measurable_otherSeedAllocations Γ j ℓ) = CommonList.iid μ k at halloc
  change FiniteLaw.ofMeasure _ (CommonList.includersCount i ∘
    otherSeedAllocations Γ j ℓ) _ = _
  rw [← FiniteLaw.ofMeasure_map _ _ (measurable_otherSeedAllocations Γ j ℓ)
    _ (measurable_of_countable _), halloc]
  exact CommonList.iid_includers_law μ i k

theorem otherInclusionCount_eq_otherSeedCount (Γ : FiniteGame m (k + 1) c Seed)
    (j : Fin (k + 1)) (d : UserProfile m (k + 1)) (ℓ : LocalList m)
    (hd : ∀ l, observe (drawsRealization d) l = ℓ) (i : Fin m)
    (s : Fin (k + 1) → Seed) :
    otherInclusionCount Γ j i (d, s) =
      otherSeedCount Γ j ℓ i (fun l => s (j.succAbove l)) := by
  classical
  apply Fin.ext
  rw [otherInclusionCount_eq_sum]
  let f : Fin (k + 1) → ℕ := fun l =>
    if i ∈ allocation (drawsRealization d) Γ.policy s l then 1 else 0
  have herase := Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)
  have hsum := Fin.sum_univ_succAbove f j
  have he : (∑ l ∈ Finset.univ.erase j, f l) = ∑ l : Fin k, f (j.succAbove l) := by
    omega
  change (∑ l ∈ Finset.univ.erase j, f l) = _
  rw [he]
  change (∑ l : Fin k, f (j.succAbove l)) = ∑ l : Fin k, _
  apply Finset.sum_congr rfl
  intro l _
  have ha : allocation (drawsRealization d) Γ.policy s (j.succAbove l) =
      otherSeedAllocations Γ j ℓ (fun l => s (j.succAbove l)) l :=
    congrArg (fun L => (Γ.policy (j.succAbove l) L (s (j.succAbove l))).val)
      (hd (j.succAbove l))
  dsimp only [f]
  split_ifs <;> simp_all

theorem posteriorCountBelief_binomial (Γ : FiniteGame m (k + 1) c Seed)
    (B : PosteriorSystem Γ) (j : Fin (k + 1)) (ℓ : LocalList m)
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) (i : Fin m) :
    posteriorCountBelief Γ B j ℓ i = IndependentCounts.binomial k (Proposer.marginal μ i)
      (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i) := by
  let T : Background m (k + 1) Seed → (Fin k → Seed) :=
    fun ω l => ω.2 (j.succAbove l)
  have hT : MeasurePreserving T (posteriorBackground Γ B j ℓ)
      (Measure.pi fun _ : Fin k => Γ.seedLaw) :=
    (measurePreserving_otherSeeds Γ.seedLaw j).comp
      (measurePreserving_snd (μ := B.posterior j ℓ)
        (ν := Measure.pi fun _ : Fin (k + 1) => Γ.seedLaw))
  have hfirst : ∀ᵐ ω ∂posteriorBackground Γ B j ℓ,
      ∀ l, observe (drawsRealization ω.1) l = ℓ :=
    (measurePreserving_fst (μ := B.posterior j ℓ)
      (ν := Measure.pi fun _ : Fin (k + 1) => Γ.seedLaw)).quasiMeasurePreserving.ae hcommon
  have he : otherInclusionCount Γ j i =ᵐ[posteriorBackground Γ B j ℓ]
      otherSeedCount Γ j ℓ i ∘ T := by
    filter_upwards [hfirst] with ω hω
    exact otherInclusionCount_eq_otherSeedCount Γ j ω.1 ℓ hω i ω.2
  unfold posteriorCountBelief
  rw [FiniteLaw.ofMeasure_congr_ae _ _ _ _ ((measurable_otherSeedCount Γ j ℓ i).comp
    hT.measurable) he, FiniteLaw.ofMeasure_comp_measurePreserving _ _ T hT]
  exact otherSeedCount_binomial Γ j ℓ μ hμ i

end OtherProposers

end Bayes
end FCAppendix
