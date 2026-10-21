import FCAppendix.Affine.Hybrid.OwnerLaw
import FCAppendix.Affine.Hybrid.SelectorSampling
import FCAppendix.Affine.Hybrid.ActivePatternGuards
import FCAppendix.Affine.Hybrid.GuardedPayoff
import FCAppendix.Affine.Hybrid.FavoredPayoffContinuity
import FCAppendix.Affine.Hybrid.PrivateSeedPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02

open MeasureTheory ProbabilityTheory Game Set Classical
open scoped BigOperators

variable {ι : Type*}

lemma finiteLaw_expect_indicator {Ω : Type*} [Fintype Ω]
    (Q : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    Q.expect (fun x => if E x then (1:ℝ) else 0) = Q.prob E := by
  rw [FiniteLaw.prob_eq_expect]

def embedSelection (A : Finset ι) (S : Finset A) : Finset ι :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] lemma embedSelection_card (A : Finset ι) (S : Finset A) :
    (embedSelection A S).card = S.card := by
  simp [embedSelection]

lemma embedSelection_subset (A : Finset ι) (S : Finset A) :
    embedSelection A S ⊆ A := by
  intro i hi
  rcases Finset.mem_map.mp hi with ⟨a, _, rfl⟩
  exact a.property

@[simp] lemma mem_embedSelection (A : Finset ι) (S : Finset A) (a : A) :
    (a : ι) ∈ embedSelection A S ↔ a ∈ S := by
  simp [embedSelection]

lemma embedSelection_disjoint (A : Finset ι) (S T : Finset A)
    (h : Disjoint S T) : Disjoint (embedSelection A S) (embedSelection A T) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rcases Finset.mem_map.mp hi with ⟨a, ha, hai⟩
  rcases Finset.mem_map.mp hj with ⟨b, hb, hbi⟩
  have hab : a = b := Subtype.ext (hai.trans hbi.symm)
  subst b
  exact Finset.disjoint_left.mp h ha hb

def embedOwnerPair (A : Finset ι) (P : Finset A × Finset A) :
    Finset ι × Finset ι := (embedSelection A P.1, embedSelection A P.2)

private lemma nonempty_subset_of_two_le (A : Finset ι) (h : 2 ≤ A.card) : Nonempty A := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  exact ⟨⟨a, ha⟩⟩

variable [Fintype ι] [DecidableEq ι]

def ownerLawOnSubset (A : Finset ι) (K₁ K₂ : ℕ) (b : ι → ℝ) :
    FiniteLaw (Finset ι × Finset ι) :=
  if h : 2 ≤ A.card ∧ K₁ + K₂ ≤ A.card then
    letI : Nonempty A := nonempty_subset_of_two_le A h.1
    (sourceOwnersLaw (fun a : A => b a) K₁ K₂).map (embedOwnerPair A)
  else FiniteLaw.dirac (∅, ∅)

lemma ownerLawOnSubset_valid (A : Finset ι) (K₁ K₂ : ℕ) (b : ι → ℝ)
    (hN : 2 ≤ A.card) (hK : K₁ + K₂ ≤ A.card) :
    ownerLawOnSubset A K₁ K₂ b =
      letI : Nonempty A := nonempty_subset_of_two_le A hN
      (sourceOwnersLaw (fun a : A => b a) K₁ K₂).map (embedOwnerPair A) := by
  simp only [ownerLawOnSubset, dif_pos (show 2 ≤ A.card ∧ K₁ + K₂ ≤ A.card from ⟨hN,hK⟩)]

lemma ownerLawOnSubset_small (A : Finset ι) (K₁ K₂ : ℕ) (b : ι → ℝ)
    (hN : A.card ≤ 1) : ownerLawOnSubset A K₁ K₂ b = FiniteLaw.dirac (∅, ∅) := by
  have hn : ¬(2 ≤ A.card ∧ K₁ + K₂ ≤ A.card) := by omega
  simp only [ownerLawOnSubset, dif_neg hn]

lemma finiteMap_support {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (x : Ξ)
    (hx : (μ.map f).mass x ≠ 0) : ∃ y, μ.mass y ≠ 0 ∧ f y = x := by
  by_contra hn
  apply hx
  change (∑ y, if f y = x then μ.mass y else 0) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases he : f y = x
  · have hz : μ.mass y = 0 := by
      by_contra hp
      exact hn ⟨y, hp, he⟩
    simp only [he, if_true, hz]
  · simp only [he, if_false]

theorem ownerLawOnSubset_support (A : Finset ι) (K₁ K₂ : ℕ) (b : ι → ℝ)
    (hN : 2 ≤ A.card) (hK : K₁ + K₂ ≤ A.card)
    (P : Finset ι × Finset ι) (hP : (ownerLawOnSubset A K₁ K₂ b).mass P ≠ 0) :
    P.1.card = K₁ ∧ P.2.card = K₂ ∧ Disjoint P.1 P.2 ∧ P.1 ⊆ A ∧ P.2 ⊆ A := by
  letI : Nonempty A := nonempty_subset_of_two_le A hN
  rw [ownerLawOnSubset_valid A K₁ K₂ b hN hK] at hP
  obtain ⟨Q, hQ, rfl⟩ := finiteMap_support
    (sourceOwnersLaw (fun a : A => b a) K₁ K₂) (embedOwnerPair A) P hP
  obtain ⟨h₁, h₂, hd⟩ := sourceOwnersLaw_support (fun a : A => b a) K₁ K₂
    (by simpa using hN) (by simpa using hK) Q.1 Q.2 hQ
  exact ⟨by simpa [embedOwnerPair] using h₁,
    by simpa [embedOwnerPair] using h₂,
    embedSelection_disjoint A Q.1 Q.2 hd,
    embedSelection_subset A Q.1, embedSelection_subset A Q.2⟩

lemma measurable_ownerLawOnSubset_mass_fixed (A : Finset ι) (K₁ K₂ : ℕ)
    (P : Finset ι × Finset ι) :
    Measurable (fun b : ι → ℝ => (ownerLawOnSubset A K₁ K₂ b).mass P) := by
  unfold ownerLawOnSubset
  split_ifs with h
  · letI : Nonempty A := nonempty_subset_of_two_le A h.1
    change Measurable (fun b : ι → ℝ =>
      (FiniteLaw.map (sourceOwnersLaw (fun a : A => b a) K₁ K₂) (embedOwnerPair A)).mass P)
    simp only [FiniteLaw.map]
    apply Finset.measurable_sum
    intro Q _
    by_cases he : embedOwnerPair A Q = P
    · simp only [if_pos he]
      exact (measurable_sourceOwnersLaw_mass K₁ K₂ Q).comp
        (measurable_pi_lambda _ (fun a : A => measurable_pi_apply (a : ι)))
    · simp only [if_neg he]
      exact measurable_const
  · exact measurable_const

lemma measurable_ownerLawOnSubset_mass (P : Finset ι × Finset ι) :
    Measurable (fun x : (Finset ι × ℕ × ℕ) × (ι → ℝ) =>
      (ownerLawOnSubset x.1.1 x.1.2.1 x.1.2.2 x.2).mass P) :=
  measurable_from_prod_countable_right (fun t =>
    measurable_ownerLawOnSubset_mass_fixed t.1 t.2.1 t.2.2 P)

private def subsetOwnerSampler :
    ((Finset ι × ℕ × ℕ) × (ι → ℝ)) → unitInterval → Finset ι × Finset ι :=
  Classical.choose (exists_support_sampler
    (fun x : (Finset ι × ℕ × ℕ) × (ι → ℝ) =>
      ownerLawOnSubset x.1.1 x.1.2.1 x.1.2.2 x.2)
    measurable_ownerLawOnSubset_mass)

private theorem subsetOwnerSampler_spec :
    Measurable (Function.uncurry (subsetOwnerSampler (ι := ι))) ∧
    (∀ (x : (Finset ι × ℕ × ℕ) × (ι → ℝ)) u,
      0 < (ownerLawOnSubset x.1.1 x.1.2.1 x.1.2.2 x.2).mass
      (subsetOwnerSampler x u)) ∧
    ∀ (x : (Finset ι × ℕ × ℕ) × (ι → ℝ)),
      (volume : Measure unitInterval).map (subsetOwnerSampler x) =
      FiniteLaw.probabilityMeasure (ownerLawOnSubset x.1.1 x.1.2.1 x.1.2.2 x.2) :=
  Classical.choose_spec (exists_support_sampler
    (fun x : (Finset ι × ℕ × ℕ) × (ι → ℝ) =>
      ownerLawOnSubset x.1.1 x.1.2.1 x.1.2.2 x.2)
    measurable_ownerLawOnSubset_mass)

def ownerPairOnSubset (A : Finset ι) (K₁ K₂ : ℕ) (b : ι → ℝ)
    (u : unitInterval) : Finset ι × Finset ι :=
  subsetOwnerSampler ((A, K₁, K₂), b) u

theorem measurable_ownerPairOnSubset :
    Measurable (fun x : ((Finset ι × ℕ × ℕ) × (ι → ℝ)) × unitInterval =>
      ownerPairOnSubset x.1.1.1 x.1.1.2.1 x.1.1.2.2 x.1.2 x.2) :=
  subsetOwnerSampler_spec.1

theorem ownerPairOnSubset_positive (A : Finset ι) (K₁ K₂ : ℕ)
    (b : ι → ℝ) (u : unitInterval) :
    0 < (ownerLawOnSubset A K₁ K₂ b).mass (ownerPairOnSubset A K₁ K₂ b u) :=
  (subsetOwnerSampler_spec (ι:=ι)).2.1 ((A,K₁,K₂),b) u

theorem ownerPairOnSubset_law (A : Finset ι) (K₁ K₂ : ℕ) (b : ι → ℝ) :
    (volume : Measure unitInterval).map (ownerPairOnSubset A K₁ K₂ b) =
      FiniteLaw.probabilityMeasure (ownerLawOnSubset A K₁ K₂ b) :=
  subsetOwnerSampler_spec.2.2 _

theorem ownerPairOnSubset_support (A : Finset ι) (K₁ K₂ : ℕ) (b : ι → ℝ)
    (u : unitInterval) (hN : 2 ≤ A.card) (hK : K₁ + K₂ ≤ A.card) :
    let P := ownerPairOnSubset A K₁ K₂ b u
    P.1.card = K₁ ∧ P.2.card = K₂ ∧ Disjoint P.1 P.2 ∧ P.1 ⊆ A ∧ P.2 ⊆ A :=
  ownerLawOnSubset_support A K₁ K₂ b hN hK _
    (ownerPairOnSubset_positive A K₁ K₂ b u).ne'

theorem ownerPairOnSubset_small (A : Finset ι) (K₁ K₂ : ℕ) (b : ι → ℝ)
    (u : unitInterval) (hN : A.card ≤ 1) :
    ownerPairOnSubset A K₁ K₂ b u = (∅, ∅) := by
  have hp := ownerPairOnSubset_positive A K₁ K₂ b u
  rw [ownerLawOnSubset_small A K₁ K₂ b hN] at hp
  by_contra hn
  simp [FiniteLaw.dirac, hn] at hp

theorem ownerLawOnSubset_zero (A : Finset ι) (b : ι → ℝ) :
    ownerLawOnSubset A 0 0 b = FiniteLaw.dirac (∅, ∅) := by
  unfold ownerLawOnSubset
  split_ifs with h
  · letI : Nonempty A := nonempty_subset_of_two_le A h.1
    apply FiniteLaw.ext_expect
    intro f
    simp [FiniteLaw.expect_map, sourceOwnersLaw,
      FiniteLaw.expect_dirac, embedOwnerPair, embedSelection]
  · rfl

theorem ownerPairOnSubset_zero (A : Finset ι) (b : ι → ℝ) (u : unitInterval) :
    ownerPairOnSubset A 0 0 b u = (∅, ∅) := by
  have hp := ownerPairOnSubset_positive A 0 0 b u
  rw [ownerLawOnSubset_zero] at hp
  by_contra hn
  simp [FiniteLaw.dirac, hn] at hp

structure PrivateSamplerPair (ι : Type*) [Fintype ι] [DecidableEq ι] where
  first : GuardedData ι → unitInterval → Finset ι
  second : GuardedData ι → unitInterval → Finset ι
  first_measurable : Measurable (Function.uncurry first)
  second_measurable : Measurable (Function.uncurry second)
  first_support : ∀ (G : GuardedData ι) u, 0 < G.law₁.mass (first G u)
  second_support : ∀ (G : GuardedData ι) u, 0 < G.law₂.mass (second G u)
  first_law : ∀ G, volume.map (first G) = FiniteLaw.probabilityMeasure G.law₁
  second_law : ∀ G, volume.map (second G) = FiniteLaw.probabilityMeasure G.law₂
  pair_law : ∀ G,
    ((volume : Measure unitInterval).prod volume).map
      (fun u => (first G u.1, second G u.2)) =
    (FiniteLaw.probabilityMeasure G.law₁).prod (FiniteLaw.probabilityMeasure G.law₂)

private theorem privateSamplerPair_nonempty : Nonempty (PrivateSamplerPair ι) := by
  obtain ⟨f₁, f₂, hf₁, hf₂, hp₁, hp₂, hl₁, hl₂, hl⟩ :=
    GuardedData.exists_private_samplers (ι := ι)
  exact ⟨⟨f₁, f₂, hf₁, hf₂, hp₁, hp₂, hl₁, hl₂, hl⟩⟩

def guardedPrivateSamplers : PrivateSamplerPair ι :=
  Classical.choice privateSamplerPair_nonempty

def guardedSelect (G : GuardedData ι) (j : Fin 2) (u : unitInterval) : Finset ι :=
  if j = 0 then guardedPrivateSamplers.first G u else guardedPrivateSamplers.second G u

def guardedLaw (G : GuardedData ι) (j : Fin 2) : FiniteLaw (Finset ι) :=
  if j = 0 then G.law₁ else G.law₂

def guardedCapacity (G : GuardedData ι) (j : Fin 2) : ℕ :=
  (if j = 0 then G.owner₁.card else G.owner₂.card) + G.residual

def guardedReceipt (G : GuardedData ι) (j : Fin 2) : ι → ℝ :=
  if j = 0 then G.receipt₁ else G.receipt₂

lemma measurable_guardedSelect (j : Fin 2) :
    Measurable (fun x : GuardedData ι × unitInterval => guardedSelect x.1 j x.2) := by
  by_cases hj : j = 0
  · simpa only [guardedSelect, if_pos hj, Function.uncurry_def] using guardedPrivateSamplers.first_measurable (ι := ι)
  · simpa only [guardedSelect, if_neg hj, Function.uncurry_def] using guardedPrivateSamplers.second_measurable (ι := ι)

theorem guardedSelect_support (G : GuardedData ι) (j : Fin 2) (u : unitInterval) :
    0 < (guardedLaw G j).mass (guardedSelect G j u) := by
  by_cases hj : j = 0
  · simpa only [guardedLaw, guardedSelect, if_pos hj] using
      guardedPrivateSamplers.first_support G u
  · simpa only [guardedLaw, guardedSelect, if_neg hj] using
      guardedPrivateSamplers.second_support G u

theorem guardedSelect_law (G : GuardedData ι) (j : Fin 2) :
    (volume : Measure unitInterval).map (guardedSelect G j) =
      FiniteLaw.probabilityMeasure (guardedLaw G j) := by
  by_cases hj : j = 0
  · have hfun : guardedSelect G j = guardedPrivateSamplers.first G := by
      funext u
      exact if_pos hj
    rw [hfun,guardedLaw,if_pos hj]
    exact guardedPrivateSamplers.first_law G
  · have hfun : guardedSelect G j = guardedPrivateSamplers.second G := by
      funext u
      exact if_neg hj
    rw [hfun,guardedLaw,if_neg hj]
    exact guardedPrivateSamplers.second_law G

theorem guardedSelect_card (G : GuardedData ι) (j : Fin 2) (u : unitInterval) :
    (guardedSelect G j u).card = guardedCapacity G j := by
  have hp := (guardedSelect_support G j u).ne'
  by_cases hj : j = 0
  · simp only [guardedLaw, if_pos hj] at hp
    simpa only [guardedCapacity, if_pos hj] using (G.law₁_support _ hp).1
  · simp only [guardedLaw, if_neg hj] at hp
    simpa only [guardedCapacity, if_neg hj] using (G.law₂_support _ hp).1

theorem guardedSelect_numerical_BR (G : GuardedData ι) (j : Fin 2) (u : unitInterval) :
    Finite.Optimal (guardedCapacity G j) (guardedReceipt G j) (guardedSelect G j u) := by
  refine ⟨(guardedSelect_card G j u).le, ?_⟩
  intro T hT
  have hp := (guardedSelect_support G j u).ne'
  by_cases hj : j = 0
  · simp only [guardedLaw, if_pos hj] at hp
    simp only [guardedCapacity, if_pos hj] at hT
    simpa only [guardedReceipt, if_pos hj] using
      G.law₁_support_best_response (guardedSelect G j u) hp T hT
  · simp only [guardedLaw, if_neg hj] at hp
    simp only [guardedCapacity, if_neg hj] at hT
    simpa only [guardedReceipt, if_neg hj] using
      G.law₂_support_best_response (guardedSelect G j u) hp T hT

theorem guardedLaw_support_threshold (G : GuardedData ι) (j : Fin 2)
    (S : Finset ι) (hS : (guardedLaw G j).mass S ≠ 0) :
    S.card = guardedCapacity G j ∧
      (∀ i ∈ S, G.multiplier ≤ guardedReceipt G j i) ∧
      (∀ i ∉ S, guardedReceipt G j i ≤ G.multiplier) := by
  by_cases hj : j = 0
  · simp only [guardedLaw, if_pos hj] at hS
    obtain ⟨hc, ho, hd⟩ := G.law₁_support S hS
    refine ⟨by simpa only [guardedCapacity, if_pos hj] using hc, ?_, ?_⟩
    · intro i hi
      simp only [guardedReceipt, if_pos hj]
      by_cases h₁ : i ∈ G.owner₁
      · rw [G.receipt₁_owner i h₁]
        exact (G.upper_guard i).le
      · have h₂ : i ∉ G.owner₂ := fun h => Finset.disjoint_left.mp hd hi h
        rw [G.receipt₁_mixed i ((G.mixed_iff i).mpr ⟨h₁, h₂⟩)]
    · intro i hi
      simp only [guardedReceipt, if_pos hj]
      have h₁ : i ∉ G.owner₁ := fun h => hi (ho h)
      by_cases h₂ : i ∈ G.owner₂
      · rw [G.receipt₁_other i h₂]
        exact (G.lower_guard i).le
      · rw [G.receipt₁_mixed i ((G.mixed_iff i).mpr ⟨h₁, h₂⟩)]
  · simp only [guardedLaw, if_neg hj] at hS
    obtain ⟨hc, ho, hd⟩ := G.law₂_support S hS
    refine ⟨by simpa only [guardedCapacity, if_neg hj] using hc, ?_, ?_⟩
    · intro i hi
      simp only [guardedReceipt, if_neg hj]
      by_cases h₂ : i ∈ G.owner₂
      · rw [G.receipt₂_owner i h₂]
        exact (G.upper_guard i).le
      · have h₁ : i ∉ G.owner₁ := fun h => Finset.disjoint_left.mp hd hi h
        rw [G.receipt₂_mixed i ((G.mixed_iff i).mpr ⟨h₁, h₂⟩)]
    · intro i hi
      simp only [guardedReceipt, if_neg hj]
      have h₂ : i ∉ G.owner₂ := fun h => hi (ho h)
      by_cases h₁ : i ∈ G.owner₁
      · rw [G.receipt₂_other i h₁]
        exact (G.lower_guard i).le
      · rw [G.receipt₂_mixed i ((G.mixed_iff i).mpr ⟨h₁, h₂⟩)]

theorem guardedSelect_finiteLaw (G : GuardedData ι) (j : Fin 2) :
    FiniteLaw.ofMeasure volume (guardedSelect G j)
      ((measurable_guardedSelect j).comp ((measurable_const : Measurable (fun _ : unitInterval => G)).prodMk measurable_id)) =
      guardedLaw G j :=
  FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ _ _ _ (guardedSelect_law G j)

theorem guardedSelect_expect (G : GuardedData ι) (j : Fin 2) (f : Finset ι → ℝ) :
    (∫ u : unitInterval, f (guardedSelect G j u) ∂volume) =
      (guardedLaw G j).expect f := by
  have h := FiniteLaw.expect_ofMeasure (volume : Measure unitInterval) (guardedSelect G j)
    ((measurable_guardedSelect j).comp ((measurable_const : Measurable (fun _ : unitInterval => G)).prodMk measurable_id)) f
  rw [guardedSelect_finiteLaw] at h
  exact h.symm

theorem guardedSelect_marginal (G : GuardedData ι) (j : Fin 2) (i : ι) :
    (∫ u : unitInterval, (if i ∈ guardedSelect G j u then (1 : ℝ) else 0) ∂volume) =
      if j = 0 then G.p₁ i else G.p₂ i := by
  rw [guardedSelect_expect G j (fun S => if i ∈ S then (1:ℝ) else 0)]
  rw [finiteLaw_expect_indicator]
  by_cases hj : j = 0
  · simpa only [guardedLaw, if_pos hj] using G.law₁_implements.2 i
  · simpa only [guardedLaw, if_neg hj] using G.law₂_implements.2 i

theorem guardedSelect_receipt₁ (G : GuardedData ι) (i : ι) :
    (∫ u : unitInterval,
      G.bid i * (1 - G.xi * (if i ∈ guardedSelect G 1 u then (1 : ℝ) else 0)) ∂volume) =
      G.receipt₁ i := by
  rw [guardedSelect_expect G 1
    (fun S => G.bid i*(1-G.xi*(if i∈ S then (1:ℝ) else 0)))]
  simp only [guardedLaw, show (1 : Fin 2) ≠ 0 by decide, if_false]
  rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sub, FiniteLaw.expect_const,
    FiniteLaw.expect_const_mul]
  rw [finiteLaw_expect_indicator]
  rw [G.law₂_implements.2]
  rfl

theorem guardedSelect_receipt₂ (G : GuardedData ι) (i : ι) :
    (∫ u : unitInterval,
      G.bid i * (1 - G.xi * (if i ∈ guardedSelect G 0 u then (1 : ℝ) else 0)) ∂volume) =
      G.receipt₂ i := by
  rw [guardedSelect_expect G 0
    (fun S => G.bid i*(1-G.xi*(if i∈ S then (1:ℝ) else 0)))]
  simp only [guardedLaw, ite_true]
  rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sub, FiniteLaw.expect_const,
    FiniteLaw.expect_const_mul]
  rw [finiteLaw_expect_indicator]
  rw [G.law₁_implements.2]
  rfl

lemma probabilityMeasure_prod {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) :
    FiniteLaw.probabilityMeasure (μ.prod ν) =
      (FiniteLaw.probabilityMeasure μ).prod (FiniteLaw.probabilityMeasure ν) := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [FiniteLaw.probabilityMeasure_singleton]
  have hs : ({(a, b)} : Set (α × β)) = ({a} : Set α) ×ˢ ({b} : Set β) := by
    ext x
    simp
  rw [hs, Measure.prod_prod, FiniteLaw.probabilityMeasure_singleton,
    FiniteLaw.probabilityMeasure_singleton]
  exact ENNReal.ofReal_mul (μ.nonneg a)

theorem guardedSelect_jointLaw (G : GuardedData ι) :
    ((volume : Measure unitInterval).prod volume).map
      (fun u => (guardedSelect G 0 u.1, guardedSelect G 1 u.2)) =
      FiniteLaw.probabilityMeasure G.jointLaw := by
  simpa only [guardedSelect, if_pos rfl,ite_true,show (1 : Fin 2) ≠ 0 by decide,
    if_false, GuardedData.jointLaw, probabilityMeasure_prod] using
      guardedPrivateSamplers.pair_law G

theorem guardedSelect_joint_finiteLaw (G : GuardedData ι) :
    FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod volume)
      (fun u => (guardedSelect G 0 u.1, guardedSelect G 1 u.2))
      ((((measurable_guardedSelect 0).comp ((measurable_const : Measurable (fun _ : unitInterval => G)).prodMk measurable_id)).comp
          measurable_fst).prodMk
        (((measurable_guardedSelect 1).comp ((measurable_const : Measurable (fun _ : unitInterval => G)).prodMk measurable_id)).comp
          measurable_snd)) = G.jointLaw :=
  FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ _ _ _ (guardedSelect_jointLaw G)

theorem guardedSelect_expected_broadcastPayoff (G : GuardedData ι)
    (eta v : ℝ) (i : ι) :
    (∫ u : unitInterval × unitInterval,
      broadcastPayoff eta v (G.bid i) i (guardedSelect G 0 u.1, guardedSelect G 1 u.2)
      ∂((volume : Measure unitInterval).prod volume)) =
      ownerSetPayoff G.xi eta v G.bid G.residual i (G.owner₁ ∪ G.owner₂) := by
  have hmeas : Measurable (fun u : unitInterval × unitInterval =>
      (guardedSelect G 0 u.1, guardedSelect G 1 u.2)) :=
    ((((measurable_guardedSelect 0).comp ((measurable_const : Measurable (fun _ : unitInterval => G)).prodMk measurable_id)).comp
        measurable_fst).prodMk
      (((measurable_guardedSelect 1).comp ((measurable_const : Measurable (fun _ : unitInterval => G)).prodMk measurable_id)).comp
        measurable_snd))
  have h := FiniteLaw.expect_ofMeasure ((volume : Measure unitInterval).prod volume)
    (fun u => (guardedSelect G 0 u.1, guardedSelect G 1 u.2)) hmeas
    (broadcastPayoff eta v (G.bid i) i)
  rw [guardedSelect_joint_finiteLaw] at h
  rw [←h]
  exact G.expected_broadcastPayoff eta v i

def restrictSelection (A T : Finset ι) : Finset A :=
  Finset.univ.filter (fun a : A => (a : ι) ∈ T)

omit [Fintype ι] in
lemma embed_restrictSelection (A T : Finset ι) :
    embedSelection A (restrictSelection A T) = T ∩ A := by
  ext i
  simp only [embedSelection, restrictSelection, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_inter, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.property⟩
  · rintro ⟨hi, hA⟩
    exact ⟨⟨i, hA⟩, hi, rfl⟩

omit [Fintype ι] in
lemma restrictSelection_card_le (A T : Finset ι) :
    (restrictSelection A T).card ≤ T.card := by
  rw [←embedSelection_card A (restrictSelection A T), embed_restrictSelection]
  exact Finset.card_le_card Finset.inter_subset_left

def extendReceipt (A : Finset ι) (w : A → ℝ) (i : ι) : ℝ :=
  if hi : i ∈ A then w ⟨i, hi⟩ else 0

omit [Fintype ι] in
lemma sum_extendReceipt_embed (A : Finset ι) (w : A → ℝ) (S : Finset A) :
    (∑ i ∈ embedSelection A S, extendReceipt A w i) = ∑ a ∈ S, w a := by
  simp [embedSelection, extendReceipt]

omit [Fintype ι] in
lemma sum_extendReceipt (A T : Finset ι) (w : A → ℝ) :
    (∑ i ∈ T, extendReceipt A w i) = ∑ a ∈ restrictSelection A T, w a := by
  calc
    _ = ∑ i ∈ embedSelection A (restrictSelection A T), extendReceipt A w i := by
      symm
      apply Finset.sum_subset
      · rw [embed_restrictSelection]
        exact Finset.inter_subset_left
      · intro i hi hn
        have hA : i ∉ A := by
          intro hA
          apply hn
          rw [embed_restrictSelection]
          exact Finset.mem_inter.mpr ⟨hi, hA⟩
        simp only [extendReceipt, dif_neg hA]
    _ = _ := sum_extendReceipt_embed A w _

omit [Fintype ι] in

theorem embedSelection_optimal (A : Finset ι) (w : A → ℝ) (k : ℕ)
    (S : Finset A) (hS : Finite.Optimal k w S) :
    Finite.Optimal k (extendReceipt A w) (embedSelection A S) := by
  refine ⟨by simpa only [embedSelection_card] using hS.1, ?_⟩
  intro T hT
  rw [sum_extendReceipt, sum_extendReceipt_embed]
  exact hS.2 (restrictSelection A T) ((restrictSelection_card_le A T).trans hT)

omit [Fintype ι] in
theorem guardedSelect_onSubset_optimal (A : Finset ι) (G : GuardedData A)
    (j : Fin 2) (u : unitInterval) :
    Finite.Optimal (guardedCapacity G j) (extendReceipt A (guardedReceipt G j))
      (embedSelection A (guardedSelect G j u)) :=
  embedSelection_optimal A _ _ _ (guardedSelect_numerical_BR G j u)

theorem guardedSelect_onSubset_locallyFeasible {m c : ℕ} (A : Finset (Fin m))
    (G : GuardedData A) (j : Fin 2) (u : unitInterval) (L : LocalList m)
    (hcap : guardedCapacity G j ≤ c) (hvisible : ∀ i ∈ A, L i ≠ none) :
    LocallyFeasible L c (embedSelection A (guardedSelect G j u)) := by
  refine ⟨?_, ?_⟩
  · simpa only [embedSelection_card, guardedSelect_card] using hcap
  · intro i hi
    exact hvisible i (embedSelection_subset A _ hi)

theorem activePatternGuarded_capacity_lt {N : ℕ} {xi L U : ℝ} (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : activePatternGuarded xi L U c z kind) :
    ∀ j : Fin 2, activePatternCapacity c kind j < Fintype.card (ActivePatternIndex kind) := by
  let A := Fintype.card (ActivePatternIndex kind)
  let s := activePatternSmall c kind
  let ell := activePatternQuota z kind
  let gap := activePatternGap c kind
  have hm : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hreg : NormalizedGuardRegion xi L U (finiteCountPoint (N+1) A s ell gap) :=
    hg.2.2.2.2.1
  have hR : normalizedResidual (finiteCountPoint (N+1) A s ell gap) =
      ((s : ℝ) - ell) / (N + 1 : ℕ) := by
    dsimp [normalizedResidual, finiteCountPoint]
    ring
  have hD : normalizedMixed (finiteCountPoint (N+1) A s ell gap) =
      ((A : ℝ) - 2*ell - gap) / (N + 1 : ℕ) := by
    dsimp [normalizedMixed, finiteCountPoint]
    ring
  have hRD := hreg.2.2.1
  rw [hR, hD] at hRD
  have hnum := (div_lt_div_iff_of_pos_right hm).mp hRD
  have hnat : s + ell + gap < A := by
    exact_mod_cast (show ((s + ell + gap : ℕ) : ℝ) < A by push_cast; linarith)
  have hsg : s + gap = max (activePatternCapacity c kind 0) (activePatternCapacity c kind 1) := by
    dsimp [s, gap, activePatternSmall, activePatternGap, residualDifference]
    omega
  intro j
  fin_cases j
  · change activePatternCapacity c kind 0 < A
    omega
  · change activePatternCapacity c kind 1 < A
    omega

def typicalCountTest {N : ℕ} (xi L U : ℝ) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) : Prop := activePatternGuarded xi L U c z kind

theorem typicalCountTest_rejects_low {N : ℕ} {xi L U : ℝ} (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind) :
    0 < LowBody.classCount 0 (LowBody.patternRow kind) ∧
      ∀ j : Fin 2, activePatternCapacity c kind j < Fintype.card (ActivePatternIndex kind) :=
  ⟨hg.2.2.2.2.2, activePatternGuarded_capacity_lt c z kind hg⟩

section SourceSampler
variable [Nonempty ι]

def sourceOwnerPair (K₁ K₂ : ℕ) : (ι → ℝ) → unitInterval → Finset ι × Finset ι :=
  Classical.choose (exists_sourceOwners_sampler (ι := ι) K₁ K₂)

theorem sourceOwnerPair_spec (K₁ K₂ : ℕ) :
    Measurable (Function.uncurry (sourceOwnerPair (ι := ι) K₁ K₂)) ∧
    (∀ (b : ι → ℝ) u, 0 < (sourceOwnersLaw b K₁ K₂).mass (sourceOwnerPair K₁ K₂ b u)) ∧
    ∀ (b : ι → ℝ), (volume : Measure unitInterval).map (sourceOwnerPair K₁ K₂ b) =
      FiniteLaw.probabilityMeasure (sourceOwnersLaw b K₁ K₂) :=
  Classical.choose_spec (exists_sourceOwners_sampler (ι := ι) K₁ K₂)

theorem sourceOwnerPair_expect (K₁ K₂ : ℕ) (b : ι → ℝ)
    (f : Finset ι × Finset ι → ℝ) :
    (∫ u : unitInterval, f (sourceOwnerPair K₁ K₂ b u) ∂volume) =
      (sourceOwnersLaw b K₁ K₂).expect f := by
  have hm := (sourceOwnerPair_spec (ι := ι) K₁ K₂).1.comp
    ((measurable_const : Measurable (fun _ : unitInterval => b)).prodMk measurable_id)
  have hl := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure
    (volume : Measure unitInterval) (sourceOwnerPair K₁ K₂ b) hm
    (sourceOwnersLaw b K₁ K₂) ((sourceOwnerPair_spec K₁ K₂).2.2 b)
  have he := FiniteLaw.expect_ofMeasure (volume : Measure unitInterval)
    (sourceOwnerPair K₁ K₂ b) hm f
  rw [hl] at he
  exact he.symm

end SourceSampler

abbrev PatternOwnerInput {N : ℕ} (L U : ℝ) (c : ℕ) (z : ℝ) (kind : Fin N → Fin 4) :=
  {x : (ActivePatternIndex kind → ℝ) ×
      (Finset (ActivePatternIndex kind) × Finset (ActivePatternIndex kind)) //
    (∀ i, x.1 i ∈ Icc L U) ∧
      (sourceOwnersLaw x.1 (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1)).mass x.2 ≠ 0}

def guardedDataFromActualCounts {N : ℕ} {xi L U : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind)
    (x : PatternOwnerInput L U c z kind) : GuardedData (ActivePatternIndex kind) :=
  Classical.choose (activePattern_guardedData hxi hxi1 hL c z kind hg
    x.val.1 x.property.1 x.val.2.1 x.val.2.2 x.property.2)

theorem guardedDataFromActualCounts_spec {N : ℕ} {xi L U : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind)
    (x : PatternOwnerInput L U c z kind) :
    let G := guardedDataFromActualCounts hxi hxi1 hL c z kind hg x
    G.xi = xi ∧ G.bid = x.val.1 ∧ G.owner₁ = x.val.2.1 ∧ G.owner₂ = x.val.2.2 ∧
      G.residual = activePatternResidual c z kind ∧
      G.owner₁.card + G.residual = activePatternCapacity c kind 0 ∧
      G.owner₂.card + G.residual = activePatternCapacity c kind 1 :=
  Classical.choose_spec (activePattern_guardedData hxi hxi1 hL c z kind hg
    x.val.1 x.property.1 x.val.2.1 x.val.2.2 x.property.2)

theorem measurable_guardedDataFromActualCounts {N : ℕ} {xi L U : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind) :
    Measurable (guardedDataFromActualCounts hxi hxi1 hL c z kind hg) := by
  apply measurable_comap_iff.mpr
  have he : GuardedData.observable ∘ guardedDataFromActualCounts hxi hxi1 hL c z kind hg =
      fun x : PatternOwnerInput L U c z kind =>
        (xi, x.val.1, x.val.2.1, x.val.2.2, activePatternResidual c z kind) := by
    funext x
    obtain ⟨hx, hb, ho₁, ho₂, hr, _, _⟩ :=
      guardedDataFromActualCounts_spec hxi hxi1 hL c z kind hg x
    simp only [Function.comp_apply, GuardedData.observable, hx, hb, ho₁, ho₂, hr]
  rw [he]
  exact measurable_const.prodMk
    (measurable_subtype_coe.fst.prodMk
      (measurable_subtype_coe.snd.fst.prodMk
        (measurable_subtype_coe.snd.snd.prodMk measurable_const)))

abbrev PatternBox {N : ℕ} (L U : ℝ) (kind : Fin N → Fin 4) :=
  {b : ActivePatternIndex kind → ℝ // ∀ i, b i ∈ Icc L U}

def patternOwnerInput {N : ℕ} {L U : ℝ} (c : ℕ) (z : ℝ) (kind : Fin N → Fin 4)
    (b : PatternBox L U kind) (u : unitInterval) : PatternOwnerInput L U c z kind :=
  ⟨(b.val, sourceOwnerPair (activePatternOwner c z kind 0)
    (activePatternOwner c z kind 1) b.val u), b.property,
    ((sourceOwnerPair_spec _ _).2.1 b.val u).ne'⟩

lemma measurable_patternOwnerInput {N : ℕ} {L U : ℝ} (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) :
    Measurable (fun x : PatternBox L U kind × unitInterval =>
      patternOwnerInput c z kind x.1 x.2) := by
  apply Measurable.subtype_mk
  exact (measurable_subtype_coe.comp measurable_fst).prodMk
    ((sourceOwnerPair_spec _ _).1.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))

def patternGuardedData {N : ℕ} {xi L U : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind)
    (b : PatternBox L U kind) (u : unitInterval) : GuardedData (ActivePatternIndex kind) :=
  guardedDataFromActualCounts hxi hxi1 hL c z kind hg (patternOwnerInput c z kind b u)

theorem measurable_patternGuardedData {N : ℕ} {xi L U : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind) :
    Measurable (fun x : PatternBox L U kind × unitInterval =>
      patternGuardedData hxi hxi1 hL c z kind hg x.1 x.2) :=
  (measurable_guardedDataFromActualCounts hxi hxi1 hL c z kind hg).comp
    (measurable_patternOwnerInput c z kind)

def patternGuardedSelect {N : ℕ} {xi L U : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind)
    (b : PatternBox L U kind) (u : unitInterval) (j : Fin 2) (s : unitInterval) :
    Finset (ActivePatternIndex kind) :=
  guardedSelect (patternGuardedData hxi hxi1 hL c z kind hg b u) j s

theorem patternGuardedSelect_numerical_BR {N : ℕ} {xi L U : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind)
    (b : PatternBox L U kind) (u : unitInterval) (j : Fin 2) (s : unitInterval) :
    Finite.Optimal (activePatternCapacity c kind j)
      (guardedReceipt (patternGuardedData hxi hxi1 hL c z kind hg b u) j)
      (patternGuardedSelect hxi hxi1 hL c z kind hg b u j s) := by
  have hspec := guardedDataFromActualCounts_spec hxi hxi1 hL c z kind hg
    (patternOwnerInput c z kind b u)
  have hcap : guardedCapacity (patternGuardedData hxi hxi1 hL c z kind hg b u) j =
      activePatternCapacity c kind j := by
    by_cases hj : j=0
    · subst j
      simpa only [guardedCapacity,ite_true,patternGuardedData] using hspec.2.2.2.2.2.1
    · have hj1 : j=1 := Fin.ext (by have h:=j.isLt; omega)
      subst j
      simpa only [guardedCapacity,patternGuardedData,show (1 : Fin 2) ≠ 0 by decide,if_false] using
        hspec.2.2.2.2.2.2
  rw [←hcap]
  exact guardedSelect_numerical_BR _ j s

theorem patternGuardedSelect_expected_payoff {N : ℕ} {xi L U : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind)
    (b : PatternBox L U kind) (eta v : ℝ) (i : ActivePatternIndex kind) :
    (∫ u : unitInterval, ∫ s : unitInterval × unitInterval,
      broadcastPayoff eta v (b.val i) i
        (patternGuardedSelect hxi hxi1 hL c z kind hg b u 0 s.1,
          patternGuardedSelect hxi hxi1 hL c z kind hg b u 1 s.2)
      ∂((volume : Measure unitInterval).prod volume) ∂volume) =
      sourceOwnerPayoff xi eta v b.val (activePatternResidual c z kind)
        (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) i := by
  have hp (u : unitInterval) :
      (∫ s : unitInterval × unitInterval,
        broadcastPayoff eta v (b.val i) i
          (patternGuardedSelect hxi hxi1 hL c z kind hg b u 0 s.1,
            patternGuardedSelect hxi hxi1 hL c z kind hg b u 1 s.2)
        ∂((volume : Measure unitInterval).prod volume)) =
      ownerSetPayoff xi eta v b.val (activePatternResidual c z kind) i
        ((sourceOwnerPair (activePatternOwner c z kind 0)
          (activePatternOwner c z kind 1) b.val u).1 ∪
         (sourceOwnerPair (activePatternOwner c z kind 0)
          (activePatternOwner c z kind 1) b.val u).2) := by
    have hspec := guardedDataFromActualCounts_spec hxi hxi1 hL c z kind hg
      (patternOwnerInput c z kind b u)
    have he := guardedSelect_expected_broadcastPayoff
      (patternGuardedData hxi hxi1 hL c z kind hg b u) eta v i
    dsimp only [patternGuardedData] at he
    rw [hspec.1,hspec.2.1,hspec.2.2.1,hspec.2.2.2.1,hspec.2.2.2.2.1] at he
    simpa only [patternGuardedSelect,patternGuardedData,patternOwnerInput] using he
  simp_rw [hp]
  exact sourceOwnerPair_expect _ _ b.val
    (fun P => ownerSetPayoff xi eta v b.val (activePatternResidual c z kind) i (P.1 ∪ P.2))

end FCAppendix.Affine.Hybrid.Native02
