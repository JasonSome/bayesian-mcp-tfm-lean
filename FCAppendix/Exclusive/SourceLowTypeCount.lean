import FCAppendix.Exclusive.MarkerConstructionSource
import FCAppendix.Exclusive.CanonicalPolicy
import FCAppendix.Exclusive.NarrowInterimBridge
import FCAppendix.Exclusive.LowTypeDeterrence

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource

open MeasureTheory ProbabilityTheory Game Exclusive Set
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def recipientEquiv (R : Finset (Fin n)) : Fin R.card ≃ R :=
  Fintype.equivOfCardEq (by simp)

def recipientSeeds (R : Finset (Fin n)) (s : Fin n → Seed) : Fin R.card → Seed :=
  fun j => s (recipientEquiv R j)

theorem measurePreserving_recipientSeeds (μ : Measure Seed) [IsProbabilityMeasure μ]
    (R : Finset (Fin n)) :
    MeasurePreserving (recipientSeeds (Seed := Seed) R)
      (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin R.card => μ) := by
  classical
  letI : Fintype R := Subtype.fintype (fun j : Fin n => j ∈ R)
  have hrestrict := (measurePreserving_fst
    (μ := Measure.pi fun _ : R => μ)
    (ν := Measure.pi fun _ : {j : Fin n // j ∉ R} => μ)).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ) (fun j => j ∈ R))
  have hreindex := measurePreserving_piCongrLeft (fun _ : Fin R.card => μ)
    (recipientEquiv R).symm
  convert hreindex.comp hrestrict using 1
  funext s j
  simp [recipientSeeds, Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.piEquivPiSubtypeProd]

def recipientAllocations (Γ : FiniteGame m n c Seed) (R : Finset (Fin n))
    (ℓ : LocalList m) (s : Fin R.card → Seed) : Fin R.card → Finset (Fin m) :=
  fun j => (Γ.policy (recipientEquiv R j) ℓ (s j)).val

theorem measurable_recipientAllocations (Γ : FiniteGame m n c Seed)
    (R : Finset (Fin n)) (ℓ : LocalList m) :
    Measurable (recipientAllocations Γ R ℓ) :=
  measurable_pi_lambda _ fun j =>
    (measurable_policy_at_list Γ (recipientEquiv R j) ℓ).comp (measurable_pi_apply j)

theorem recipientAllocations_law (Γ : FiniteGame m n c Seed)
    (R : Finset (Fin n)) (ℓ : LocalList m) (μ : FiniteLaw (Finset (Fin m)))
    (hμ : SymmetricAtList Γ ℓ μ) :
    FiniteLaw.ofMeasure (Measure.pi fun _ : Fin R.card => Γ.seedLaw)
      (recipientAllocations Γ R ℓ) (measurable_recipientAllocations Γ R ℓ) =
        CommonList.iid μ R.card :=
  FiniteLaw.ofMeasure_pi_eq_iid Γ.seedLaw R.card
    (fun j s => (Γ.policy (recipientEquiv R j) ℓ s).val)
    (fun j => measurable_policy_at_list Γ (recipientEquiv R j) ℓ)
    μ (fun j => hμ (recipientEquiv R j))

theorem actual_count_eq_recipient_count (Γ : FiniteGame m n c Seed)
    (x : Realization m n) (i : Fin m) (ℓ : LocalList m)
    (hℓ : ∀ j ∈ x.recipients i, observe x j = ℓ) (s : Fin n → Seed) :
    (boundedCount x Γ.policy s i).val =
      (CommonList.includersCount i
        (recipientAllocations Γ (x.recipients i) ℓ
          (recipientSeeds (x.recipients i) s))).val := by
  classical
  change inclusionCount x Γ.policy s i = _
  rw [inclusionCount_eq_sum]
  change _ = ∑ j : Fin (x.recipients i).card,
    if i ∈ (Γ.policy (recipientEquiv (x.recipients i) j) ℓ
      (s (recipientEquiv (x.recipients i) j))).val then 1 else 0
  rw [(recipientEquiv (x.recipients i)).sum_comp (fun j : x.recipients i =>
    if i ∈ (Γ.policy j ℓ (s j)).val then (1 : ℕ) else 0)]
  rw [← Finset.sum_subtype (x.recipients i) (fun _ => Iff.rfl)
    (fun j => if i ∈ (Γ.policy j ℓ (s j)).val then (1 : ℕ) else 0)]
  symm
  calc
    _ = ∑ j ∈ x.recipients i, if i ∈ allocation x Γ.policy s j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have he := congrArg (fun L => (Γ.policy j L (s j)).val) (hℓ j hj)
      change (if i ∈ (Γ.policy j ℓ (s j)).val then (1 : ℕ) else 0) = _
      rw [← he]
      rfl
    _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
    have hnot : i ∉ allocation x Γ.policy s j := by
      intro hi
      exact hj ((accepted_subset_recipients x Γ.policy s i)
        (by simpa [accepted] using hi))
    simp [hnot])

theorem profile_test_of_recipient_common_list (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (i : Fin m) (ℓ : LocalList m)
    (hℓ : ∀ j ∈ (drawsRealization d).recipients i,
      observe (drawsRealization d) j = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ)
    (f : ℕ → ℝ) :
    (profileCountLaw Γ d i).expect (fun r => f r.val) =
      Exclusive.Narrow.binomialPolynomial ((drawsRealization d).recipients i).card
        f (Proposer.marginal μ i) := by
  let R := (drawsRealization d).recipients i
  let z : (Fin R.card → Seed) → Fin (R.card+1) :=
    fun s => CommonList.includersCount i (recipientAllocations Γ R ℓ s)
  have hz : Measurable z := (measurable_of_countable (CommonList.includersCount i)).comp
    (measurable_recipientAllocations Γ R ℓ)
  have hlaw : FiniteLaw.ofMeasure (Measure.pi fun _ : Fin R.card => Γ.seedLaw) z hz =
      IndependentCounts.binomial R.card (Proposer.marginal μ i)
        (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i) := by
    change FiniteLaw.ofMeasure _ (CommonList.includersCount i ∘
      recipientAllocations Γ R ℓ) _ = _
    rw [← FiniteLaw.ofMeasure_map _ _ (measurable_recipientAllocations Γ R ℓ)
      _ (measurable_of_countable _), recipientAllocations_law Γ R ℓ μ hμ]
    exact CommonList.iid_includers_law μ i R.card
  unfold profileCountLaw
  rw [CountLaw.expect_ofMeasure]
  change (∫ s : Fin n → Seed, f (boundedCount (drawsRealization d) Γ.policy s i).val
    ∂Measure.pi fun _ : Fin n => Γ.seedLaw) = _
  have he : (fun s : Fin n → Seed =>
      f (boundedCount (drawsRealization d) Γ.policy s i).val) =
      (fun s => f (z s).val) ∘ recipientSeeds R := by
    funext s
    exact congrArg f (actual_count_eq_recipient_count Γ (drawsRealization d) i ℓ hℓ s)
  have hmp := measurePreserving_recipientSeeds Γ.seedLaw R
  rw [he]
  have hmap := integral_map (μ := Measure.pi fun _ : Fin n => Γ.seedLaw)
    (f := fun s => f (z s).val) hmp.measurable.aemeasurable
    (((measurable_of_countable (fun r : Fin (R.card+1) => f r.val)).comp hz).aestronglyMeasurable)
  change (∫ s, f (z (recipientSeeds R s)).val ∂Measure.pi fun _ : Fin n => Γ.seedLaw) = _
  rw [← hmap, hmp.map_eq]
  rw [← FiniteLaw.expect_ofMeasure (Measure.pi fun _ : Fin R.card => Γ.seedLaw)
    z hz (fun r => f r.val), hlaw,
    ← Exclusive.Narrow.binomialPolynomial_eq_expect]

end FCAppendix.Bayes.ExclusiveSource
