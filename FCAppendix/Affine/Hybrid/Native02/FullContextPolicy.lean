import FCAppendix.Affine.Hybrid.Native02.ObservedSeed
import FCAppendix.Affine.Hybrid.Native02.ExceptionalClipped
import FCAppendix.Affine.Hybrid.NativeContinuation
import FCAppendix.Affine.Hybrid.NativeActivePriority
import FCAppendix.Affine.Hybrid.SingletonPayoff

set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 1000
noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
namespace FullContext

open MeasureTheory ProbabilityTheory Bayes Game Set Classical
open scoped BigOperators

variable {m c : ℕ}

def activeSet (d : ℝ) (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => L i ≠ none ∧ d < entryBid (L i))

def boxSet (L U : ℝ) (X : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => X i ≠ none ∧ entryBid (X i) ∈ Icc L U)

private lemma measurable_filter_ids {X : Type*} [MeasurableSpace X]
    (p : X → Fin m → Prop) (hp : ∀ i, MeasurableSet {x | p x i}) :
    Measurable (fun x => Finset.univ.filter (p x)) := by
  apply measurable_to_countable'
  intro A
  have he : (fun x => Finset.univ.filter (p x)) ⁻¹' {A} =
      ⋂ i : Fin m, {x | (i ∈ A ↔ p x i)} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_setOf_eq]
    exact ⟨fun h i => by rw [←h]; simp,
      fun h => Finset.ext (fun i => by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (h i).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ A
  · simpa only [hi, true_iff] using hp i
  · simpa only [hi, false_iff, Set.compl_setOf] using (hp i).compl

lemma measurable_activeSet (d : ℝ) : Measurable (activeSet (m := m) d) := by
  unfold activeSet
  have hm := measurable_filter_ids (m := m) (fun X : LocalList m => fun i => X i ≠ none ∧ d < entryBid (X i)) (by
    intro i
    exact (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).compl.inter
      (measurableSet_lt measurable_const (measurable_entryBid.comp (measurable_pi_apply i))))
  convert! hm using 1
  funext X
  ext i
  simp

lemma measurable_boxSet (L U : ℝ) : Measurable (boxSet (m := m) L U) := by
  unfold boxSet
  have hm := measurable_filter_ids (m := m) (fun X : LocalList m => fun i => X i ≠ none ∧ entryBid (X i) ∈ Icc L U) (by
    intro i
    exact (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).compl.inter
      ((measurable_entryBid.comp (measurable_pi_apply i)) measurableSet_Icc))
  convert! hm using 1
  funext X
  ext i
  simp

def capacity (c : ℕ) (A : Finset (Fin m)) (H : ℕ) : ℕ := min A.card (c - H)

def ownerCount (z : ℝ) (A : Finset (Fin m)) (d₀ d₁ : ℕ) (j : Fin 2) : ℕ :=
  exclusiveQuota z A.card +
    if (if j = 0 then d₁ else d₀) < (if j = 0 then d₀ else d₁)
    then residualDifference d₀ d₁ else 0

abbrev TableIndex (m : ℕ) := Finset (Fin m) × Finset (Fin m) × ℕ × ℕ × ℕ

def tableIndex (d L U z : ℝ) (c : ℕ) (X : ClassifiedContext m) : TableIndex m :=
  let A := activeSet d X.1
  let d₀ := capacity c A X.2.1
  let d₁ := capacity c A X.2.2
  (A, boxSet L U X.1 ∩ A, ownerCount z A d₀ d₁ 0, ownerCount z A d₀ d₁ 1,
    min d₀ d₁ - exclusiveQuota z A.card)

lemma measurable_tableIndex (d L U z : ℝ) (c : ℕ) :
    Measurable (tableIndex (m := m) d L U z c) := by
  let f : (Finset (Fin m) × Finset (Fin m)) × (ℕ × ℕ) → TableIndex m := fun q =>
    let A := q.1.1
    let d₀ := capacity c A q.2.1
    let d₁ := capacity c A q.2.2
    (A, q.1.2 ∩ A, ownerCount z A d₀ d₁ 0, ownerCount z A d₀ d₁ 1,
      min d₀ d₁ - exclusiveQuota z A.card)
  exact (measurable_of_countable f).comp
    ((((measurable_activeSet d).comp measurable_fst).prodMk
      ((measurable_boxSet L U).comp measurable_fst)).prodMk measurable_snd)

def eligibleOn (A B : Finset (Fin m)) : Finset A :=
  Finset.univ.filter (fun a : A => (a : Fin m) ∈ B)

def tableOwners (A B : Finset (Fin m)) (K₀ K₁ : ℕ)
    (b : Fin m → ℝ) (u : unitInterval) : Finset A × Finset A :=
  if h : 2 ≤ A.card then
    letI : Nonempty A := by
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
      exact ⟨⟨a, ha⟩⟩
    if B = A then sourceOwnerPair K₀ K₁ (fun a : A => b a) u
    else ownerPairOnSubset (eligibleOn A B) K₀ K₁ (fun a : A => b a) u
  else (∅, ∅)

lemma measurable_tableOwners (A B : Finset (Fin m)) (K₀ K₁ : ℕ) :
    Measurable (fun x : (Fin m → ℝ) × unitInterval => tableOwners A B K₀ K₁ x.1 x.2) := by
  unfold tableOwners
  split_ifs with h hBA
  · letI : Nonempty A := by
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
      exact ⟨⟨a, ha⟩⟩
    have hb : Measurable (fun x : (Fin m → ℝ) × unitInterval => (fun a : A => x.1 a)) :=
      measurable_pi_lambda _ (fun a : A => (measurable_pi_apply (a : Fin m)).comp measurable_fst)
    simpa only [Function.comp_def, Function.uncurry_def,id_eq] using (sourceOwnerPair_spec K₀ K₁).1.comp (hb.prodMk measurable_snd)
  · have hb : Measurable (fun x : (Fin m → ℝ) × unitInterval => (fun a : A => x.1 a)) :=
      measurable_pi_lambda _ (fun a : A => (measurable_pi_apply (a : Fin m)).comp measurable_fst)
    simpa only [Function.comp_def, Function.uncurry_def,id_eq] using measurable_ownerPairOnSubset.comp
      (((measurable_const (a := (eligibleOn A B, K₀, K₁))).prodMk hb).prodMk measurable_snd)
  · exact measurable_const

def tableLaw (xi : ℝ) (T : TableIndex m) (j : Fin 2)
    (b : Fin m → ℝ) (u : unitInterval) : FiniteLaw (Finset (Fin m)) :=
  let P := tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1 b u
  let E₀ := if j = 0 then P.1 else P.2
  let E₁ := if j = 0 then P.2 else P.1
  (canonicalClippedOwnerLaw xi T.2.2.2.2 E₀ E₁ (fun a : T.1 => b a)).map
    (embedSelection T.1)

lemma measurable_tableLaw_mass_fixed {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (T : TableIndex m) (j : Fin 2) (S : Finset (Fin m)) :
    Measurable (fun x : (Fin m → ℝ) × unitInterval => (tableLaw xi T j x.1 x.2).mass S) := by
  let A := T.1
  have howners := measurable_tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1
  have hpair : Measurable (fun x : (Fin m → ℝ) × unitInterval =>
      let P := tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1 x.1 x.2
      if j = 0 then P else (P.2, P.1)) := by
    by_cases hj : j = 0
    · simpa only [if_pos hj] using howners
    · simpa only [if_neg hj] using howners.snd.prodMk howners.fst
  have hm (Q : Finset A) : Measurable (fun x : (Finset A × Finset A) × (A → ℝ) =>
      (canonicalClippedOwnerLaw xi T.2.2.2.2 x.1.1 x.1.2 x.2).mass Q) :=
    measurable_from_prod_countable_right (fun P =>
      (ExactCapacity.measurable_symmetricLottery_mass Q).comp
        (measurable_canonicalClippedOwnerP hxi hxi1 T.2.2.2.2 P.1 P.2))
  dsimp only [tableLaw, FiniteLaw.map]
  apply Finset.measurable_sum
  intro Q _
  by_cases hQ : embedSelection T.1 Q = S
  · convert! (hm Q).comp (hpair.prodMk (measurable_pi_lambda _
      (fun a : A => (measurable_pi_apply (a : Fin m)).comp measurable_fst))) using 1
    funext x
    by_cases hj : j = 0 <;> simp [hj,hQ] <;> rfl
  · simpa only [if_neg hQ] using (measurable_const (a := (0 : ℝ)) : Measurable (fun _ : (Fin m → ℝ) × unitInterval => (0 : ℝ)))

lemma measurable_tableLaw_mass {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (j : Fin 2) (S : Finset (Fin m)) :
    Measurable (fun x : TableIndex m × ((Fin m → ℝ) × unitInterval) =>
      (tableLaw xi x.1 j x.2.1 x.2.2).mass S) :=
  measurable_from_prod_countable_right (fun T => measurable_tableLaw_mass_fixed hxi hxi1 T j S)

private lemma measurable_seed_default : Measurable (fun o : Option unitInterval => o.getD 0) := by
  intro S hS
  change MeasurableSet S
  exact hS

def proposalLaw (xi d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2)
    (X : ClassifiedContext m) : FiniteLaw (Finset (Fin m)) :=
  tableLaw xi (tableIndex d L U z c X) j (fun i => entryBid (X.1 i))
    ((observedLowMinimumSeed d μ X.1).getD 0)

lemma measurable_proposalLaw_mass {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2) (S : Finset (Fin m)) :
    Measurable (fun X : ClassifiedContext m => (proposalLaw xi d L U z c μ j X).mass S) := by
  have hm : Measurable (fun X : ClassifiedContext m =>
      (tableIndex d L U z c X,
        ((fun i : Fin m => entryBid (X.1 i)), ((observedLowMinimumSeed d μ X.1).getD 0)))) :=
    (measurable_tableIndex d L U z c).prodMk
      ((measurable_pi_lambda _ (fun i : Fin m => measurable_entryBid.comp
        ((measurable_pi_apply i).comp measurable_fst))).prodMk
        (measurable_seed_default.comp ((measurable_observedLowMinimumSeed d μ).comp measurable_fst)))
  simpa only [Function.comp_def, proposalLaw] using (measurable_tableLaw_mass hxi hxi1 j S).comp hm

def countReady (xi d L U z : ℝ) (c : ℕ) (X : ClassifiedContext m) : Prop :=
  let A := activeSet d X.1
  let d₀ := capacity c A X.2.1
  let d₁ := capacity c A X.2.2
  let K₀ := ownerCount z A d₀ d₁ 0
  let K₁ := ownerCount z A d₀ d₁ 1
  2 ≤ A.card ∧ d₀ ≠ d₁ ∧ 0 < K₀ + K₁ ∧ K₀ + K₁ < A.card ∧
    NormalizedGuardRegion xi L U (finiteCountPoint m A.card (min d₀ d₁)
      (exclusiveQuota z A.card) (residualDifference d₀ d₁)) ∧
    0 < visibleCount (lowOnlyList d X.1) ∧ seedUseAllowed A.card d₀ d₁ ∧
    (A \ boxSet L U X.1).card ≤ 1

lemma measurableSet_countReady (xi d L U z : ℝ) (c : ℕ) :
    MeasurableSet {X : ClassifiedContext m | countReady xi d L U z c X} := by
  let f : ((Finset (Fin m) × Finset (Fin m)) × (ℕ × ℕ)) × ℕ → Prop := fun t =>
    let A := t.1.1.1
    let B := t.1.1.2
    let d₀ := capacity c A t.1.2.1
    let d₁ := capacity c A t.1.2.2
    let K₀ := ownerCount z A d₀ d₁ 0
    let K₁ := ownerCount z A d₀ d₁ 1
    2 ≤ A.card ∧ d₀ ≠ d₁ ∧ 0 < K₀ + K₁ ∧ K₀ + K₁ < A.card ∧
      NormalizedGuardRegion xi L U (finiteCountPoint m A.card (min d₀ d₁)
        (exclusiveQuota z A.card) (residualDifference d₀ d₁)) ∧
      0 < t.2 ∧ seedUseAllowed A.card d₀ d₁ ∧ (A \ B).card ≤ 1
  exact ((measurable_of_countable f).comp
    (((((measurable_activeSet d).comp measurable_fst).prodMk
      ((measurable_boxSet L U).comp measurable_fst)).prodMk measurable_snd).prodMk
        ((measurable_visibleCount.comp (measurable_lowOnlyList d)).comp measurable_fst))).setOf

def proposalReceipt (xi d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2)
    (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  entryBid (X.1 i) * (1 - xi *
    (proposalLaw xi d L U z c μ (otherProposer j) X).prob (fun S => i ∈ S))

lemma measurable_proposalReceipt {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2) (i : Fin m) :
    Measurable (fun X : ClassifiedContext m => proposalReceipt xi d L U z c μ j X i) := by
  have hm : Measurable (fun X : ClassifiedContext m =>
      (proposalLaw xi d L U z c μ (otherProposer j) X).prob (fun S => i ∈ S)) := by
    unfold FiniteLaw.prob FiniteLaw.expect
    exact Finset.measurable_sum _ (fun S _ =>
      (measurable_proposalLaw_mass hxi hxi1 d L U z c μ (otherProposer j) S).mul_const _)
  exact (measurable_entryBid.comp ((measurable_pi_apply i).comp measurable_fst)).mul
    (measurable_const.sub (measurable_const.mul hm))

def proposalValid (xi d L U z : ℝ) (c : ℕ) (μ : Measure ℝ)
    (X : ClassifiedContext m) : Prop :=
  ∀ j : Fin 2, ∀ S : Finset (Fin m),
    (proposalLaw xi d L U z c μ j X).mass S ≠ 0 →
      LocallyFeasible X.1 (c - contextUpper j X) S ∧
      Finite.Optimal (c - contextUpper j X) (proposalReceipt xi d L U z c μ j X) S

lemma measurableSet_proposalValid {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) :
    MeasurableSet {X : ClassifiedContext m | proposalValid xi d L U z c μ X} := by
  simp only [proposalValid, setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro S
  have hcap : Measurable (fun X : ClassifiedContext m => c - contextUpper j X) :=
    measurable_const.sub (measurable_contextUpper j)
  have hcard : MeasurableSet {X : ClassifiedContext m | S.card ≤ c - contextUpper j X} :=
    measurableSet_le measurable_const hcap
  have hvis : MeasurableSet {X : ClassifiedContext m | ∀ i ∈ S, X.1 i ≠ none} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ S
    · simpa only [hi, Set.iInter_true, Set.compl_setOf, Function.comp_def] using
        (measurableSet_eq_fun ((measurable_pi_apply i).comp (measurable_fst : Measurable (Prod.fst : ClassifiedContext m → LocalList m))) (measurable_const (a := (none : Option ℝ)))).compl
    · simp only [hi, Set.iInter_of_empty]
      exact MeasurableSet.univ
  have hsum (T : Finset (Fin m)) : Measurable (fun X : ClassifiedContext m =>
      ∑ i ∈ T, proposalReceipt xi d L U z c μ j X i) :=
    Finset.measurable_sum T (fun i _ => measurable_proposalReceipt hxi hxi1 d L U z c μ j i)
  have hbest : MeasurableSet {X : ClassifiedContext m | ∀ T : Finset (Fin m),
      T.card ≤ c - contextUpper j X →
        (∑ i ∈ T, proposalReceipt xi d L U z c μ j X i) ≤
          ∑ i ∈ S, proposalReceipt xi d L U z c μ j X i} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro T
    have he : {X : ClassifiedContext m | T.card ≤ c - contextUpper j X →
        (∑ i ∈ T, proposalReceipt xi d L U z c μ j X i) ≤
          ∑ i ∈ S, proposalReceipt xi d L U z c μ j X i} =
      {X | ¬ T.card ≤ c - contextUpper j X} ∪
        {X | (∑ i ∈ T, proposalReceipt xi d L U z c μ j X i) ≤
          ∑ i ∈ S, proposalReceipt xi d L U z c μ j X i} := by ext X; simp only [mem_union, mem_setOf_eq]; tauto
    rw [he]
    exact (measurableSet_le measurable_const hcap).compl.union
      (measurableSet_le (hsum T) (hsum S))
  have hzero : MeasurableSet {X : ClassifiedContext m |
      (proposalLaw xi d L U z c μ j X).mass S = 0} :=
    measurableSet_eq_fun (measurable_proposalLaw_mass hxi hxi1 d L U z c μ j S) measurable_const
  have he : {X : ClassifiedContext m |
      (proposalLaw xi d L U z c μ j X).mass S ≠ 0 →
      LocallyFeasible X.1 (c - contextUpper j X) S ∧
      Finite.Optimal (c - contextUpper j X) (proposalReceipt xi d L U z c μ j X) S} =
      {X | (proposalLaw xi d L U z c μ j X).mass S = 0} ∪
        ({X | S.card ≤ c - contextUpper j X} ∩
          {X | ∀ i ∈ S, X.1 i ≠ none} ∩
          {X | ∀ T : Finset (Fin m), T.card ≤ c - contextUpper j X →
            (∑ i ∈ T, proposalReceipt xi d L U z c μ j X i) ≤
              ∑ i ∈ S, proposalReceipt xi d L U z c μ j X i}) := by
    ext X
    simp only [LocallyFeasible, Finite.Optimal, mem_union, mem_inter_iff, mem_setOf_eq]
    tauto
  rw [he]
  exact hzero.union ((hcard.inter hvis).inter hbest)

def proposalSample {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2) :
    ClassifiedContext m → unitInterval → Finset (Fin m) :=
  Classical.choose (exists_support_sampler (proposalLaw xi d L U z c μ j)
    (measurable_proposalLaw_mass hxi hxi1 d L U z c μ j))

lemma proposalSample_spec {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (proposalSample (m := m) hxi hxi1 d L U z c μ j)) ∧
    (∀ X u, 0 < (proposalLaw xi d L U z c μ j X).mass
      (proposalSample (m := m) hxi hxi1 d L U z c μ j X u)) ∧
    ∀ X, volume.map (proposalSample (m := m) hxi hxi1 d L U z c μ j X) =
      FiniteLaw.probabilityMeasure (proposalLaw xi d L U z c μ j X) :=
  Classical.choose_spec (exists_support_sampler (proposalLaw xi d L U z c μ j)
    (measurable_proposalLaw_mass hxi hxi1 d L U z c μ j))

def useProposal (xi d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (X : ClassifiedContext m) : Prop :=
  countReady xi d L U z c X ∧ proposalValid xi d L U z c μ X

def select {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2)
    (X : ClassifiedContext m) (s : unitInterval) : Finset (Fin m) :=
  if useProposal xi d L U z c μ X then proposalSample (m := m) hxi hxi1 d L U z c μ j X s
  else NativeContinuation.select xi hxi hxi1 c j X s

lemma measurable_select {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (select (m := m) hxi hxi1 d L U z c μ j)) :=
  Measurable.ite
    (((measurableSet_countReady xi d L U z c).inter
      (measurableSet_proposalValid hxi hxi1 d L U z c μ)).preimage measurable_fst)
    (proposalSample_spec (m := m) hxi hxi1 d L U z c μ j).1
    (NativeContinuation.measurable_select xi hxi hxi1 c j)

lemma select_feasible {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2)
    (X : ClassifiedContext m) (s : unitInterval) :
    LocallyFeasible X.1 (c - contextUpper j X) (select hxi hxi1 d L U z c μ j X s) := by
  unfold select
  split_ifs with h
  · exact (h.2 j _ ((proposalSample_spec (m := m) hxi hxi1 d L U z c μ j).2.1 X s).ne').1
  · exact NativeContinuation.select_feasible xi hxi hxi1 c j X s

def contextPolicy {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) : ContextPolicy m c unitInterval where
  select := select hxi hxi1 d L U z c μ
  measurable := measurable_select hxi hxi1 d L U z c μ
  feasible := select_feasible hxi hxi1 d L U z c μ

def acceptance {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2)
    (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  ∫ s : unitInterval, (if i ∈ select hxi hxi1 d L U z c μ j X s then (1 : ℝ) else 0) ∂volume

def receipt {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2)
    (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  entryBid (X.1 i) * (1 - xi * acceptance hxi hxi1 d L U z c μ (otherProposer j) X i)

lemma acceptance_proposal {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (j : Fin 2)
    (X : ClassifiedContext m) (hX : useProposal xi d L U z c μ X) (i : Fin m) :
    acceptance hxi hxi1 d L U z c μ j X i =
      (proposalLaw xi d L U z c μ j X).prob (fun S => i ∈ S) := by
  simp only [acceptance, select, if_pos hX]
  have hm : Measurable (proposalSample (m := m) hxi hxi1 d L U z c μ j X) := by
    simpa only [Function.comp_def, Function.uncurry_def,id_eq] using
      (proposalSample_spec (m := m) hxi hxi1 d L U z c μ j).1.comp ((measurable_const (a := X)).prodMk measurable_id)
  have hl := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure (volume : Measure unitInterval)
    (proposalSample (m := m) hxi hxi1 d L U z c μ j X) hm (proposalLaw xi d L U z c μ j X)
    ((proposalSample_spec (m := m) hxi hxi1 d L U z c μ j).2.2 X)
  have he := FiniteLaw.expect_ofMeasure (volume : Measure unitInterval)
    (proposalSample (m := m) hxi hxi1 d L U z c μ j X) hm
    (fun S => if i ∈ S then (1 : ℝ) else 0)
  rw [hl] at he
  convert! he.symm using 1
  apply FiniteLaw.expect_congr
  intro S
  by_cases h : i ∈ S <;> simp [h]

theorem select_numerical_optimal {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1) (j : Fin 2) (s : unitInterval) :
    Finite.Optimal (c - contextUpper j X) (receipt hxi hxi1 d L U z c μ j X)
      (select hxi hxi1 d L U z c μ j X s) := by
  by_cases hp : useProposal xi d L U z c μ X
  · have hr : receipt hxi hxi1 d L U z c μ j X = proposalReceipt xi d L U z c μ j X := by
      funext i
      rw [receipt, acceptance_proposal hxi hxi1 d L U z c μ (otherProposer j) X hp i]
      rfl
    rw [hr, select, if_pos hp]
    exact (hp.2 j _ ((proposalSample_spec (m := m) hxi hxi1 d L U z c μ j).2.1 X s).ne').2
  · have hr : receipt hxi hxi1 d L U z c μ j X =
        NativeContinuation.receipt xi hxi hxi1 c j X := by
      funext i
      simp only [receipt, acceptance, select, if_neg hp,
        NativeContinuation.receipt, NativeContinuation.acceptance]
    rw [hr, select, if_neg hp]
    exact NativeContinuation.select_numerical_optimal xi hxi hxi1 c X hX j s

theorem contextPolicy_lower_optimal {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ)
    (Γ : FiniteGame m 2 c unitInterval) (hseed : Γ.seedLaw = volume)
    (j : Fin 2) (X : ClassifiedContext m) (hX : NonnegativeList X.1) (s : unitInterval) :
    let C := contextPolicy (m := m) hxi hxi1 d L U z c μ
    Finite.Optimal (c - contextUpper j X) (lowerContextReceipt Γ C xi j X) (C.select j X s) := by
  have hr : lowerContextReceipt Γ (contextPolicy hxi hxi1 d L U z c μ) xi j X =
      receipt hxi hxi1 d L U z c μ j X := by
    funext i
    simp only [lowerContextReceipt, contextAcceptance, hseed, contextPolicy, receipt, acceptance]
    rfl
  dsimp only
  rw [hr]
  exact select_numerical_optimal hxi hxi1 d L U z c μ X hX j s

lemma tableLaw_support_subset (xi : ℝ) (T : TableIndex m) (j : Fin 2)
    (b : Fin m → ℝ) (u : unitInterval) (S : Finset (Fin m))
    (hS : (tableLaw xi T j b u).mass S ≠ 0) : S ⊆ T.1 := by
  unfold tableLaw at hS
  obtain ⟨Q, _, hQ⟩ := finiteMap_support _ (embedSelection T.1) S hS
  rw [←hQ]
  exact embedSelection_subset T.1 Q

lemma proposalLaw_support_active (xi d L U z : ℝ) (c : ℕ) (μ : Measure ℝ)
    (j : Fin 2) (X : ClassifiedContext m) (S : Finset (Fin m))
    (hS : (proposalLaw xi d L U z c μ j X).mass S ≠ 0) :
    S ⊆ activeSet d X.1 :=
  tableLaw_support_subset xi _ j _ _ S hS

lemma countReady_box_covers_residual (xi d L U z : ℝ) (c : ℕ)
    (X : ClassifiedContext m) (hX : countReady xi d L U z c X) (j : Fin 2) :
    c - contextUpper j X ≤ (activeSet d X.1 ∩ boxSet L U X.1).card := by
  let A := activeSet d X.1
  let B := boxSet L U X.1
  have hsafe := hX.2.2.2.2.2.2.1
  have hbad : (A \ B).card ≤ 1 := hX.2.2.2.2.2.2.2
  have hraw : c - contextUpper j X < A.card := by
    have hj : j = 0 ∨ j = 1 := by have h := j.isLt; omega
    rcases hj with rfl | rfl
    · have h₀ := hsafe.1
      change min A.card (c - X.2.1) < A.card at h₀
      change c - X.2.1 < A.card
      omega
    · have h₁ := hsafe.2
      change min A.card (c - X.2.2) < A.card at h₁
      change c - X.2.2 < A.card
      omega
  have hpartition := Finset.card_sdiff_add_card_inter A B
  change c - contextUpper j X ≤ (A ∩ B).card
  omega

lemma fallback_excludes_low_on_countReady {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (hgap : d < (1-xi)*L)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hready : countReady xi d L U z c X) (j : Fin 2) (s : unitInterval)
    (i : Fin m) (b : ℝ) (hi : X.1 i = some b) (hb : b ≤ d) :
    i ∉ NativeContinuation.select xi hxi hxi1 c j X s := by
  let w := NativeContinuation.receipt xi hxi hxi1 c j X
  let B := activeSet d X.1 ∩ boxSet L U X.1
  have hwi : w i ≤ d := by
    have hw := (NativeContinuation.receipt_bounds xi hxi hxi1 c j X hX i).2
    have hbi : entryBid (X.1 i) = b := by simp only [hi, entryBid]
    exact hw.trans (hbi.le.trans hb)
  have hbetter : B ⊆ Finset.univ.filter (fun k => w i < w k) := by
    intro k hk
    have hbox := (Finset.mem_filter.mp (Finset.mem_inter.mp hk).2).2.2
    have hfloor : (1-xi)*L ≤ (1-xi)*entryBid (X.1 k) :=
      mul_le_mul_of_nonneg_left hbox.1 (by linarith)
    have hwk := (NativeContinuation.receipt_bounds xi hxi hxi1 c j X hX k).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hwi.trans_lt (hgap.trans_le (hfloor.trans hwk))⟩
  have hn := (countReady_box_covers_residual xi d L U z c X hready j).trans
    (Finset.card_le_card hbetter)
  exact Finite.excluded_of_many_better (c - contextUpper j X) w
    (NativeContinuation.select xi hxi hxi1 c j X s)
    (NativeContinuation.select_numerical_optimal xi hxi hxi1 c X hX j s) i hn

theorem low_context_agreement {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hgap : d < (1-xi)*L) :
    ∀ (j : Fin 2) (X : ClassifiedContext m), NonnegativeList X.1 →
      ∀ (s : unitInterval) (i : Fin m) (b : ℝ), X.1 i = some b → b ≤ d →
        (i ∈ (contextPolicy hxi hxi1 d L U z c μ).select j X s ↔
          i ∈ (NativeContinuation.contextPolicy xi hxi hxi1 c).select j X s) := by
  intro j X hX s i b hi hb
  by_cases hp : useProposal xi d L U z c μ X
  · have hnew : i ∉ proposalSample (m := m) hxi hxi1 d L U z c μ j X s := by
      intro his
      have ha := proposalLaw_support_active xi d L U z c μ j X _
        ((proposalSample_spec (m := m) hxi hxi1 d L U z c μ j).2.1 X s).ne' his
      have hg := (Finset.mem_filter.mp ha).2.2
      simp only [hi, entryBid] at hg
      exact not_lt_of_ge hb hg
    have hold := fallback_excludes_low_on_countReady hxi hxi1 d L U z c hgap
      X hX hp.1 j s i b hi hb
    simp only [contextPolicy, select, if_pos hp, NativeContinuation.contextPolicy,
      hnew, hold]
  · simp only [contextPolicy, select, if_neg hp, NativeContinuation.contextPolicy]

lemma canonical_guarded_law {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GuardedData ι) (j : Fin 2) :
    canonicalClippedOwnerLaw G.xi G.residual
      (if j = 0 then G.owner₁ else G.owner₂)
      (if j = 0 then G.owner₂ else G.owner₁) G.bid = guardedLaw G j := by
  by_cases hj : j = 0
  · simp only [if_pos hj, guardedLaw]
    exact (canonicalClippedOwnerLaw_eq (ClippedOwnerData.of_guarded G)).trans
      (ClippedOwnerData.of_guarded_law₁ G)
  · simp only [if_neg hj, guardedLaw]
    have h := canonicalClippedOwnerLaw_eq (ClippedOwnerData.of_guarded G).swap
    change canonicalClippedOwnerLaw G.xi G.residual G.owner₂ G.owner₁ G.bid =
      ExactCapacity.symmetricLottery (ClippedOwnerData.of_guarded G).swap.p₁ at h
    rw [ClippedOwnerData.swap_p₁, ClippedOwnerData.of_guarded_p₂] at h
    exact h

lemma tableLaw_eq_guarded {xi : ℝ} (T : TableIndex m) (b : Fin m → ℝ)
    (u : unitInterval) (G : GuardedData T.1)
    (hx : G.xi = xi) (hb : G.bid = fun a : T.1 => b a)
    (ho₁ : G.owner₁ = (tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1 b u).1)
    (ho₂ : G.owner₂ = (tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1 b u).2)
    (hr : G.residual = T.2.2.2.2) (j : Fin 2) :
    tableLaw xi T j b u = (guardedLaw G j).map (embedSelection T.1) := by
  unfold tableLaw
  dsimp only
  rw [←hx, ←hb, ←ho₁, ←ho₂, ←hr, canonical_guarded_law]

theorem exists_guardedData_on_context {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (hL : 0 < L)
    (X : ClassifiedContext m) (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (u : unitInterval) :
    ∃ G : GuardedData (activeSet d X.1),
      G.xi = xi ∧ G.bid = (fun i : activeSet d X.1 => entryBid (X.1 i)) ∧
      G.owner₁ = (tableOwners (tableIndex d L U z c X).1
        (tableIndex d L U z c X).2.1 (tableIndex d L U z c X).2.2.1
        (tableIndex d L U z c X).2.2.2.1 (fun i => entryBid (X.1 i)) u).1 ∧
      G.owner₂ = (tableOwners (tableIndex d L U z c X).1
        (tableIndex d L U z c X).2.1 (tableIndex d L U z c X).2.2.1
        (tableIndex d L U z c X).2.2.2.1 (fun i => entryBid (X.1 i)) u).2 ∧
      G.residual = (tableIndex d L U z c X).2.2.2.2 ∧
      (∀ j : Fin 2, guardedCapacity G j = c - contextUpper j X) := by
  let A := activeSet d X.1
  let d₀ := capacity c A X.2.1
  let d₁ := capacity c A X.2.2
  let ell := exclusiveQuota z A.card
  let gap := residualDifference d₀ d₁
  let K₀ := ownerCount z A d₀ d₁ 0
  let K₁ := ownerCount z A d₀ d₁ 1
  let b : A → ℝ := fun i => entryBid (X.1 i)
  have hN : 2 ≤ A.card := hready.1
  letI : Nonempty A := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
    exact ⟨⟨a, ha⟩⟩
  let P := sourceOwnerPair K₀ K₁ b u
  have hBA : boxSet L U X.1 ∩ A = A := by
    apply Finset.inter_eq_right.mpr
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hi).2.1, hbox i hi⟩
  have hP : tableOwners (tableIndex d L U z c X).1
      (tableIndex d L U z c X).2.1 (tableIndex d L U z c X).2.2.1
      (tableIndex d L U z c X).2.2.2.1 (fun i => entryBid (X.1 i)) u = P := by
    change tableOwners A (boxSet L U X.1 ∩ A) K₀ K₁ (fun i : Fin m => entryBid (X.1 i)) u = P
    simp only [tableOwners, dif_pos hN, if_pos hBA]
    rfl
  have hp : (sourceOwnersLaw b K₀ K₁).mass P ≠ 0 :=
    ((sourceOwnerPair_spec K₀ K₁).2.1 b u).ne'
  obtain ⟨hp₀, hp₁, hdis⟩ := sourceOwnersLaw_support b K₀ K₁
    (by simpa using hN) (by simpa using hready.2.2.2.1.le) P.1 P.2 hp
  have hm : 0 < m := by
    have hAm := Finset.card_le_univ A
    simp only [Fintype.card_fin] at hAm
    omega
  have hregion : NormalizedGuardRegion xi L U
      (finiteCountPoint m A.card (min d₀ d₁) ell gap) := hready.2.2.2.2.1
  have hb : ∀ i : A, b i ∈ Icc L U := fun i => hbox i i.property
  have hraw₀ : d₀ = c - X.2.1 := by
    have hs := hready.2.2.2.2.2.2.1.1
    change min A.card (c - X.2.1) < A.card at hs
    exact Nat.min_eq_right (by omega)
  have hraw₁ : d₁ = c - X.2.2 := by
    have hs := hready.2.2.2.2.2.2.1.2
    change min A.card (c - X.2.2) < A.card at hs
    exact Nat.min_eq_right (by omega)
  have hne : d₀ ≠ d₁ := hready.2.1
  rcases lt_or_gt_of_ne hne with hd | hd
  · have hk₀ : K₀ = ell := by
      change ell + (if d₁ < d₀ then residualDifference d₀ d₁ else 0) = ell
      rw [if_neg (not_lt_of_ge hd.le), add_zero]
    have hk₁ : K₁ = ell + (d₁-d₀) := by
      change ell + (if d₀ < d₁ then residualDifference d₀ d₁ else 0) = ell + (d₁-d₀)
      rw [if_pos hd]
      simp only [residualDifference, min_eq_left hd.le, max_eq_right hd.le]
    have hreg : NormalizedGuardRegion xi L U
        (finiteCountPoint m A.card d₀ ell (d₁-d₀)) := by
      simpa only [gap, residualDifference, min_eq_left hd.le, max_eq_right hd.le] using hregion
    obtain ⟨Q, hqx, hqb, hq₁, hq₂, hqr, hqbig, hqsmall⟩ :=
      exists_guardedData_of_count_region hxi hxi1 hL m A.card d₀ d₁ ell hm
        (by simp) hd.le hreg b hb P.2 P.1 hdis.symm
        (by simpa only [hk₁] using hp₁) (by simpa only [hk₀] using hp₀)
    refine ⟨Q.swapOwners, hqx, hqb, ?_, ?_, ?_, ?_⟩
    · simpa only [GuardedData.swapOwners, hP] using hq₂
    · simpa only [GuardedData.swapOwners, hP] using hq₁
    · change Q.residual = min d₀ d₁ - ell
      rw [min_eq_left hd.le]
      exact hqr
    · intro j
      have hj : j = 0 ∨ j = 1 := by have h := j.isLt; omega
      rcases hj with rfl | rfl
      · simpa only [guardedCapacity, ite_true, GuardedData.swapOwners,
          contextUpper, ite_true, ←hraw₀] using hqsmall
      · simpa only [guardedCapacity, show (1 : Fin 2) ≠ 0 by decide, if_false,
          GuardedData.swapOwners, contextUpper, ←hraw₁] using hqbig
  · have hk₀ : K₀ = ell + (d₀-d₁) := by
      change ell + (if d₁ < d₀ then residualDifference d₀ d₁ else 0) = ell + (d₀-d₁)
      rw [if_pos hd]
      simp only [residualDifference, min_eq_right hd.le, max_eq_left hd.le]
    have hk₁ : K₁ = ell := by
      change ell + (if d₀ < d₁ then residualDifference d₀ d₁ else 0) = ell
      rw [if_neg (not_lt_of_ge hd.le), add_zero]
    have hreg : NormalizedGuardRegion xi L U
        (finiteCountPoint m A.card d₁ ell (d₀-d₁)) := by
      simpa only [gap, residualDifference, min_eq_right hd.le, max_eq_left hd.le] using hregion
    obtain ⟨Q, hqx, hqb, hq₁, hq₂, hqr, hqbig, hqsmall⟩ :=
      exists_guardedData_of_count_region hxi hxi1 hL m A.card d₁ d₀ ell hm
        (by simp) hd.le hreg b hb P.1 P.2 hdis
        (by simpa only [hk₀] using hp₀) (by simpa only [hk₁] using hp₁)
    refine ⟨Q, hqx, hqb, ?_, ?_, ?_, ?_⟩
    · simpa only [hP] using hq₁
    · simpa only [hP] using hq₂
    · change Q.residual = min d₀ d₁ - ell
      rw [min_eq_right hd.le]
      exact hqr
    · intro j
      have hj : j = 0 ∨ j = 1 := by have h := j.isLt; omega
      rcases hj with rfl | rfl
      · simpa only [guardedCapacity, ite_true, contextUpper, ite_true, ←hraw₀] using hqbig
      · simpa only [guardedCapacity, show (1 : Fin 2) ≠ 0 by decide, if_false,
          contextUpper, ←hraw₁] using hqsmall

lemma prob_map_embed_active {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (ν : FiniteLaw (Finset A)) (i : A) :
    (ν.map (embedSelection A)).prob (fun S => (i : ι) ∈ S) =
      ν.prob (fun S => i ∈ S) := by
  unfold FiniteLaw.prob
  rw [FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro S
  simp only [mem_embedSelection]
  by_cases h : i ∈ S <;> simp [h]

lemma prob_map_embed_inactive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (ν : FiniteLaw (Finset A)) (i : ι) (hi : i ∉ A) :
    (ν.map (embedSelection A)).prob (fun S => i ∈ S) = 0 := by
  unfold FiniteLaw.prob
  rw [FiniteLaw.expect_map]
  calc
    _ = ν.expect (fun _ => (0 : ℝ)) := by
      apply FiniteLaw.expect_congr
      intro S
      dsimp only
      exact if_neg (fun his => hi (embedSelection_subset A S his))
    _ = 0 := ν.expect_zero

lemma guardedLaw_opponent_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GuardedData ι) (j : Fin 2) (i : ι) :
    G.bid i * (1-G.xi * (guardedLaw G (otherProposer j)).prob (fun S => i ∈ S)) =
      guardedReceipt G j i := by
  have hj : j = 0 ∨ j = 1 := by have h := j.isLt; omega
  rcases hj with rfl | rfl
  · simp [otherProposer, guardedLaw, guardedReceipt, G.law₂_implements.2 i, GuardedData.receipt₁]
  · simp [otherProposer, guardedLaw, guardedReceipt, G.law₁_implements.2 i, GuardedData.receipt₂]

theorem proposalValid_of_guarded {xi : ℝ} (_hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0 ≤ d)
    (hgap : d < (1-xi)*L) (X : ClassifiedContext m)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (G : GuardedData (activeSet d X.1))
    (hx : G.xi = xi) (hb : G.bid = fun i : activeSet d X.1 => entryBid (X.1 i))
    (hcap : ∀ j : Fin 2, guardedCapacity G j = c - contextUpper j X)
    (hlaw : ∀ j : Fin 2, proposalLaw xi d L U z c μ j X =
      (guardedLaw G j).map (embedSelection (activeSet d X.1))) :
    proposalValid xi d L U z c μ X := by
  let A := activeSet d X.1
  have hreceipt (j : Fin 2) (i : A) :
      proposalReceipt xi d L U z c μ j X i = guardedReceipt G j i := by
    rw [proposalReceipt, hlaw, prob_map_embed_active, ←hx]
    change (fun i : A => entryBid (X.1 i)) i * _ = _
    rw [←hb]
    exact guardedLaw_opponent_marginal G j i
  have houtside (j : Fin 2) (i : Fin m) (hi : i ∉ A) :
      proposalReceipt xi d L U z c μ j X i ≤ d := by
    rw [proposalReceipt, hlaw, prob_map_embed_inactive A _ i hi]
    simp only [mul_zero, sub_zero, mul_one]
    by_cases hvis : X.1 i = none
    · simpa only [hvis, entryBid] using hd
    · have hn : ¬ d < entryBid (X.1 i) := by
        intro ht
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvis, ht⟩)
      exact le_of_not_gt hn
  have hlam : d < G.multiplier := by
    obtain ⟨i, hi⟩ := G.mixed_nonempty
    have hiL : L ≤ G.bid i := by rw [hb]; exact (hbox i i.property).1
    have ht := G.lower_guard i
    change (1-G.xi)*G.bid i < G.multiplier at ht
    rw [hx] at ht
    exact hgap.trans_le ((mul_le_mul_of_nonneg_left hiL (by linarith)).trans ht.le)
  intro j S hS
  rw [hlaw j] at hS
  obtain ⟨Q, hQ, rfl⟩ := finiteMap_support _ (embedSelection A) S hS
  obtain ⟨hc, hs, hn⟩ := guardedLaw_support_threshold G j Q hQ
  have hcard : (embedSelection A Q).card = c - contextUpper j X := by
    rw [embedSelection_card, hc, hcap]
  have hselected : ∀ i ∈ embedSelection A Q,
      G.multiplier ≤ proposalReceipt xi d L U z c μ j X i := by
    intro i hi
    have hiA := embedSelection_subset A Q hi
    have hiQ : (⟨i, hiA⟩ : A) ∈ Q := (mem_embedSelection A Q ⟨i, hiA⟩).mp hi
    rw [show proposalReceipt xi d L U z c μ j X i =
      guardedReceipt G j ⟨i, hiA⟩ from hreceipt j ⟨i, hiA⟩]
    exact hs ⟨i, hiA⟩ hiQ
  have hunselected : ∀ i ∉ embedSelection A Q,
      proposalReceipt xi d L U z c μ j X i ≤ G.multiplier := by
    intro i hi
    by_cases hiA : i ∈ A
    · have hiQ : (⟨i, hiA⟩ : A) ∉ Q := fun h => hi ((mem_embedSelection A Q ⟨i, hiA⟩).mpr h)
      rw [show proposalReceipt xi d L U z c μ j X i =
        guardedReceipt G j ⟨i, hiA⟩ from hreceipt j ⟨i, hiA⟩]
      exact hn ⟨i, hiA⟩ hiQ
    · exact (houtside j i hiA).trans hlam.le
  refine ⟨⟨hcard.le, ?_⟩, hcard.le, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp (embedSelection_subset A Q hi)).2.1
  · intro T hT
    exact threshold_optimal _ _ T G.multiplier G.multiplier_pos.le
      (by simpa only [hcard] using hT) hselected hunselected

theorem useProposal_of_inBox {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U) :
    useProposal xi d L U z c μ X := by
  let u := (observedLowMinimumSeed d μ X.1).getD 0
  obtain ⟨G, hx, hb, ho₀, ho₁, hr, hc⟩ :=
    exists_guardedData_on_context hxi hxi1 d L U z c hL X hready hbox u
  refine ⟨hready, proposalValid_of_guarded hxi hxi1 d L U z c μ hd hgap X hbox
    G hx hb hc ?_⟩
  intro j
  convert! tableLaw_eq_guarded (tableIndex d L U z c X) (fun i => entryBid (X.1 i)) u G hx hb ho₀ ho₁ hr j using 1

theorem contextPolicy_law_on_guarded {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (j : Fin 2) :
    volume.map ((contextPolicy hxi hxi1 d L U z c μ).select j X) =
      FiniteLaw.probabilityMeasure (proposalLaw xi d L U z c μ j X) := by
  have hp := useProposal_of_inBox hxi hxi1 d L U z c μ hd hL hgap X hready hbox
  change volume.map (select hxi hxi1 d L U z c μ j X) = _
  have hs : select hxi hxi1 d L U z c μ j X = proposalSample hxi hxi1 d L U z c μ j X := by
    funext u
    exact if_pos hp
  rw [hs]
  exact ((proposalSample_spec (m := m) hxi hxi1 d L U z c μ j).2.2 X)

theorem tableLaw_inBox_expected_payoff {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (hL : 0 < L)
    (X : ClassifiedContext m) (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (u : unitInterval) (eta v : ℝ) (i : activeSet d X.1) :
    ((tableLaw xi (tableIndex d L U z c X) 0 (fun i => entryBid (X.1 i)) u).prod
      (tableLaw xi (tableIndex d L U z c X) 1 (fun i => entryBid (X.1 i)) u)).expect
        (broadcastPayoff eta v (entryBid (X.1 i)) (i : Fin m)) =
      ownerSetPayoff xi eta v (fun i : activeSet d X.1 => entryBid (X.1 i))
        (tableIndex d L U z c X).2.2.2.2 i
        ((tableOwners (tableIndex d L U z c X).1 (tableIndex d L U z c X).2.1
          (tableIndex d L U z c X).2.2.1 (tableIndex d L U z c X).2.2.2.1
          (fun i => entryBid (X.1 i)) u).1 ∪
         (tableOwners (tableIndex d L U z c X).1 (tableIndex d L U z c X).2.1
          (tableIndex d L U z c X).2.2.1 (tableIndex d L U z c X).2.2.2.1
          (fun i => entryBid (X.1 i)) u).2) := by
  obtain ⟨G, hx, hb, ho₀, ho₁, hr, hc⟩ :=
    exists_guardedData_on_context hxi hxi1 d L U z c hL X hready hbox u
  rw [tableLaw_eq_guarded _ _ u G hx hb ho₀ ho₁ hr 0,
    tableLaw_eq_guarded _ _ u G hx hb ho₀ ho₁ hr 1]
  have he : (((guardedLaw G 0).map (embedSelection (activeSet d X.1))).prod
      ((guardedLaw G 1).map (embedSelection (activeSet d X.1)))).expect
      (broadcastPayoff eta v (entryBid (X.1 i)) (i : Fin m)) =
      G.jointLaw.expect (broadcastPayoff eta v (G.bid i) i) := by
    simp only [guardedLaw, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      if_false, GuardedData.jointLaw, FiniteLaw.expect_prod, FiniteLaw.expect_map]
    apply FiniteLaw.expect_congr
    intro S
    apply FiniteLaw.expect_congr
    intro T
    simp only [broadcastPayoff, mem_embedSelection, hb]
  have hh := G.expected_broadcastPayoff eta v i
  convert! he.trans hh using 1
  simp only [hx,hb,ho₀,ho₁,hr]

theorem contextPolicy_private_pair_law {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ)
    (X : ClassifiedContext m) (hp : useProposal xi d L U z c μ X) :
    ((volume : Measure unitInterval).prod volume).map
      (fun s => ((contextPolicy hxi hxi1 d L U z c μ).select 0 X s.1,
        (contextPolicy hxi hxi1 d L U z c μ).select 1 X s.2)) =
      FiniteLaw.probabilityMeasure ((proposalLaw xi d L U z c μ 0 X).prod
        (proposalLaw xi d L U z c μ 1 X)) := by
  have h₀ := proposalSample_spec (m := m) hxi hxi1 d L U z c μ (0 : Fin 2)
  have h₁ := proposalSample_spec (m := m) hxi hxi1 d L U z c μ (1 : Fin 2)
  have hm₀ : Measurable (proposalSample (m := m) hxi hxi1 d L U z c μ 0 X) := by
    simpa only [Function.comp_def, Function.uncurry_def,id_eq] using h₀.1.comp ((measurable_const (a := X)).prodMk measurable_id)
  have hm₁ : Measurable (proposalSample (m := m) hxi hxi1 d L U z c μ 1 X) := by
    simpa only [Function.comp_def, Function.uncurry_def,id_eq] using h₁.1.comp ((measurable_const (a := X)).prodMk measurable_id)
  simp only [contextPolicy, select, if_pos hp]
  have hmap := Measure.map_prod_map (volume : Measure unitInterval) (volume : Measure unitInterval) hm₀ hm₁
  calc
    _ = ((volume : Measure unitInterval).map (proposalSample hxi hxi1 d L U z c μ 0 X)).prod
        ((volume : Measure unitInterval).map (proposalSample hxi hxi1 d L U z c μ 1 X)) := hmap.symm
    _ = _ := by rw [h₀.2.2 X, h₁.2.2 X, ← probabilityMeasure_prod]

theorem contextPolicy_private_payoff_guarded {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (eta v : ℝ) (i : activeSet d X.1) :
    (∫ s : unitInterval × unitInterval,
      broadcastPayoff eta v (entryBid (X.1 i)) (i : Fin m)
        ((contextPolicy hxi hxi1 d L U z c μ).select 0 X s.1,
          (contextPolicy hxi hxi1 d L U z c μ).select 1 X s.2)
      ∂((volume : Measure unitInterval).prod volume)) =
      ((tableLaw xi (tableIndex d L U z c X) 0 (fun i => entryBid (X.1 i))
          ((observedLowMinimumSeed d μ X.1).getD 0)).prod
        (tableLaw xi (tableIndex d L U z c X) 1 (fun i => entryBid (X.1 i))
          ((observedLowMinimumSeed d μ X.1).getD 0))).expect
        (broadcastPayoff eta v (entryBid (X.1 i)) (i : Fin m)) := by
  let C := contextPolicy (m := m) hxi hxi1 d L U z c μ
  let F := fun s : unitInterval × unitInterval => (C.select 0 X s.1, C.select 1 X s.2)
  have hm : Measurable F :=
    ((C.measurable 0).comp (measurable_const.prodMk measurable_fst)).prodMk
      ((C.measurable 1).comp (measurable_const.prodMk measurable_snd))
  have hp := useProposal_of_inBox hxi hxi1 d L U z c μ hd hL hgap X hready hbox
  have hl := contextPolicy_private_pair_law hxi hxi1 d L U z c μ X hp
  have heq := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure
    ((volume : Measure unitInterval).prod volume) F hm
    ((proposalLaw xi d L U z c μ 0 X).prod (proposalLaw xi d L U z c μ 1 X)) hl
  have he := FiniteLaw.expect_ofMeasure ((volume : Measure unitInterval).prod volume)
    F hm (broadcastPayoff eta v (entryBid (X.1 i)) (i : Fin m))
  rw [heq] at he
  convert! he.symm using 1

theorem tableLaw_uniform_common_payoff {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (hL : 0 < L)
    (X : ClassifiedContext m) [Nonempty (activeSet d X.1)]
    (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (eta v : ℝ) (i : activeSet d X.1) :
    (∫ u : unitInterval,
      ((tableLaw xi (tableIndex d L U z c X) 0 (fun i => entryBid (X.1 i)) u).prod
        (tableLaw xi (tableIndex d L U z c X) 1 (fun i => entryBid (X.1 i)) u)).expect
        (broadcastPayoff eta v (entryBid (X.1 i)) (i : Fin m)) ∂volume) =
      sourceOwnerPayoff xi eta v (fun i : activeSet d X.1 => entryBid (X.1 i))
        (tableIndex d L U z c X).2.2.2.2 (tableIndex d L U z c X).2.2.1
        (tableIndex d L U z c X).2.2.2.1 i := by
  have hBA : boxSet L U X.1 ∩ activeSet d X.1 = activeSet d X.1 := by
    apply Finset.inter_eq_right.mpr
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hi).2.1, hbox i hi⟩
  simp_rw [tableLaw_inBox_expected_payoff hxi hxi1 d L U z c hL X hready hbox]
  have hp (u : unitInterval) :
      tableOwners (tableIndex d L U z c X).1 (tableIndex d L U z c X).2.1
        (tableIndex d L U z c X).2.2.1 (tableIndex d L U z c X).2.2.2.1
        (fun i => entryBid (X.1 i)) u =
      sourceOwnerPair (tableIndex d L U z c X).2.2.1
        (tableIndex d L U z c X).2.2.2.1
        (fun i : activeSet d X.1 => entryBid (X.1 i)) u := by
    simp only [tableIndex, hBA, tableOwners, dif_pos hready.1, ite_true]
  simp_rw [hp]
  simpa only [sourceOwnerPayoff, sourceSingletonPayoff] using sourceOwnerPair_expect
    (tableIndex d L U z c X).2.2.1 (tableIndex d L U z c X).2.2.2.1
    (fun i : activeSet d X.1 => entryBid (X.1 i))
    (fun AB => ownerSetPayoff xi eta v (fun i : activeSet d X.1 => entryBid (X.1 i)) (tableIndex d L U z c X).2.2.2.2 i (AB.1 ∪ AB.2))

theorem countReady_iff_activePatternGuarded_of_counts {N : ℕ} (xi d L U z : ℝ)
    (c : ℕ) (kind : Fin N → Fin 4) (X : ClassifiedContext (N+1))
    (hcard : (activeSet d X.1).card = Fintype.card (ActivePatternIndex kind))
    (hupper : ∀ j : Fin 2, contextUpper j X = activePatternUpper kind j)
    (hlow : visibleCount (lowOnlyList d X.1) =
      LowBody.classCount 0 (LowBody.patternRow kind))
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U) :
    countReady xi d L U z c X ↔ activePatternGuarded xi L U c z kind := by
  let A := activeSet d X.1
  have hc₀ : capacity c A X.2.1 = activePatternCapacity c kind 0 := by
    unfold capacity activePatternCapacity
    rw [hcard]
    congr 1
    exact congrArg (fun n => c-n) (hupper 0)
  have hc₁ : capacity c A X.2.2 = activePatternCapacity c kind 1 := by
    unfold capacity activePatternCapacity
    rw [hcard]
    congr 1
    exact congrArg (fun n => c-n) (hupper 1)
  have ho (j : Fin 2) : ownerCount z A (activePatternCapacity c kind 0)
      (activePatternCapacity c kind 1) j = activePatternOwner c z kind j := by
    have hj : j = 0 ∨ j = 1 := by have h := j.isLt; omega
    rcases hj with rfl | rfl <;> simp only [ownerCount, activePatternOwner, activePatternQuota,
      activePatternGap]
    all_goals simp only [ite_true, sub_zero, sub_self, show (1 : Fin 2) ≠ 0 from by decide, if_false]
    all_goals rw [show A.card = Fintype.card (ActivePatternIndex kind) from hcard]
    all_goals rfl
  have hbad : A \ boxSet L U X.1 = ∅ := by
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hi).2.1, hbox i hi⟩
  have he : countReady xi d L U z c X ↔
      activePatternGuarded xi L U c z kind ∧
        seedUseAllowed (Fintype.card (ActivePatternIndex kind))
          (activePatternCapacity c kind 0) (activePatternCapacity c kind 1) := by
    unfold countReady
    dsimp only
    rw [hc₀, hc₁, ho 0, ho 1, hcard, hlow, hbad]
    simp only [Finset.card_empty, Nat.zero_le, and_true]
    unfold activePatternGuarded activePatternSmall activePatternQuota activePatternGap
    tauto
  rw [he]
  exact ⟨fun h => h.1, fun h => ⟨h,
    activePatternGuarded_capacity_lt c z kind h 0,
    activePatternGuarded_capacity_lt c z kind h 1⟩⟩

theorem useProposal_iff_activePatternGuarded_of_counts {N : ℕ} {xi : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hgap : d < (1-xi)*L)
    (kind : Fin N → Fin 4) (X : ClassifiedContext (N+1))
    (hcard : (activeSet d X.1).card = Fintype.card (ActivePatternIndex kind))
    (hupper : ∀ j : Fin 2, contextUpper j X = activePatternUpper kind j)
    (hlow : visibleCount (lowOnlyList d X.1) =
      LowBody.classCount 0 (LowBody.patternRow kind))
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U) :
    useProposal xi d L U z c μ X ↔ activePatternGuarded xi L U c z kind := by
  have he := countReady_iff_activePatternGuarded_of_counts xi d L U z c kind X
    hcard hupper hlow hbox
  constructor
  · intro hp
    exact he.mp hp.1
  · intro hg
    exact useProposal_of_inBox hxi hxi1 d L U z c μ hd hL hgap X (he.mpr hg) hbox

theorem tableLaw_inBox_expected_singleton {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (hL : 0 < L)
    (X : ClassifiedContext m) (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (u : unitInterval) (v : ℝ) (i : activeSet d X.1) :
    ((tableLaw xi (tableIndex d L U z c X) 0 (fun i => entryBid (X.1 i)) u).prod
      (tableLaw xi (tableIndex d L U z c X) 1 (fun i => entryBid (X.1 i)) u)).expect
        (singletonPayoff v (entryBid (X.1 i)) (i : Fin m)) =
      ownerSetSingletonPayoff xi v (fun i : activeSet d X.1 => entryBid (X.1 i))
        (tableIndex d L U z c X).2.2.2.2 i
        ((tableOwners (tableIndex d L U z c X).1 (tableIndex d L U z c X).2.1
          (tableIndex d L U z c X).2.2.1 (tableIndex d L U z c X).2.2.2.1
          (fun i => entryBid (X.1 i)) u).1 ∪
         (tableOwners (tableIndex d L U z c X).1 (tableIndex d L U z c X).2.1
          (tableIndex d L U z c X).2.2.1 (tableIndex d L U z c X).2.2.2.1
          (fun i => entryBid (X.1 i)) u).2) := by
  obtain ⟨G, hx, hb, ho₀, ho₁, hr, hc⟩ :=
    exists_guardedData_on_context hxi hxi1 d L U z c hL X hready hbox u
  rw [tableLaw_eq_guarded _ _ u G hx hb ho₀ ho₁ hr 0,
    tableLaw_eq_guarded _ _ u G hx hb ho₀ ho₁ hr 1]
  have he : (((guardedLaw G 0).map (embedSelection (activeSet d X.1))).prod
      ((guardedLaw G 1).map (embedSelection (activeSet d X.1)))).expect
      (singletonPayoff v (entryBid (X.1 i)) (i : Fin m)) =
      G.jointLaw.expect (singletonPayoff v (G.bid i) i) := by
    simp only [guardedLaw, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      if_false, GuardedData.jointLaw, FiniteLaw.expect_prod, FiniteLaw.expect_map]
    apply FiniteLaw.expect_congr
    intro S
    apply FiniteLaw.expect_congr
    intro T
    simp only [singletonPayoff, mem_embedSelection, hb]
  have hh := G.expected_singletonPayoff v i
  convert! he.trans hh using 1
  simp only [hx,hb,ho₀,ho₁,hr]

theorem contextPolicy_singleton_integrand_guarded {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (v : ℝ) (i : activeSet d X.1) :
    ((v-entryBid (X.1 i))/2)*
      (acceptance hxi hxi1 d L U z c μ 0 X i + acceptance hxi hxi1 d L U z c μ 1 X i) =
      ((proposalLaw xi d L U z c μ 0 X).prod (proposalLaw xi d L U z c μ 1 X)).expect
        (singletonPayoff v (entryBid (X.1 i)) (i : Fin m)) := by
  have hp := useProposal_of_inBox hxi hxi1 d L U z c μ hd hL hgap X hready hbox
  rw [acceptance_proposal _ _ _ _ _ _ _ _ 0 X hp i,
    acceptance_proposal _ _ _ _ _ _ _ _ 1 X hp i, expect_product_singletonPayoff]

theorem tableLaw_uniform_common_singleton {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (hL : 0 < L)
    (X : ClassifiedContext m) [Nonempty (activeSet d X.1)]
    (hready : countReady xi d L U z c X)
    (hbox : ∀ i ∈ activeSet d X.1, entryBid (X.1 i) ∈ Icc L U)
    (v : ℝ) (i : activeSet d X.1) :
    (∫ u : unitInterval,
      ((tableLaw xi (tableIndex d L U z c X) 0 (fun i => entryBid (X.1 i)) u).prod
        (tableLaw xi (tableIndex d L U z c X) 1 (fun i => entryBid (X.1 i)) u)).expect
        (singletonPayoff v (entryBid (X.1 i)) (i : Fin m)) ∂volume) =
      sourceSingletonPayoff xi v (fun i : activeSet d X.1 => entryBid (X.1 i))
        (tableIndex d L U z c X).2.2.2.2 (tableIndex d L U z c X).2.2.1
        (tableIndex d L U z c X).2.2.2.1 i := by
  have hBA : boxSet L U X.1 ∩ activeSet d X.1 = activeSet d X.1 := by
    apply Finset.inter_eq_right.mpr
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hi).2.1, hbox i hi⟩
  simp_rw [tableLaw_inBox_expected_singleton hxi hxi1 d L U z c hL X hready hbox]
  have hp (u : unitInterval) :
      tableOwners (tableIndex d L U z c X).1 (tableIndex d L U z c X).2.1
        (tableIndex d L U z c X).2.2.1 (tableIndex d L U z c X).2.2.2.1
        (fun i => entryBid (X.1 i)) u =
      sourceOwnerPair (tableIndex d L U z c X).2.2.1
        (tableIndex d L U z c X).2.2.2.1
        (fun i : activeSet d X.1 => entryBid (X.1 i)) u := by
    simp only [tableIndex, hBA, tableOwners, dif_pos hready.1, ite_true]
  simp_rw [hp]
  simpa only [sourceSingletonPayoff] using sourceOwnerPair_expect
    (tableIndex d L U z c X).2.2.1 (tableIndex d L U z c X).2.2.2.1
    (fun i : activeSet d X.1 => entryBid (X.1 i))
    (fun AB => ownerSetSingletonPayoff xi v (fun i : activeSet d X.1 => entryBid (X.1 i)) (tableIndex d L U z c X).2.2.2.2 i (AB.1 ∪ AB.2))

lemma tableOwners_congr_active (A B : Finset (Fin m)) (K₀ K₁ : ℕ)
    (b b' : Fin m → ℝ) (u : unitInterval) (hb : ∀ i ∈ A, b i = b' i) :
    tableOwners A B K₀ K₁ b u = tableOwners A B K₀ K₁ b' u := by
  have he : (fun i : A => b i) = fun i : A => b' i :=
    funext (fun i => hb i i.property)
  unfold tableOwners
  split_ifs <;> simp only [he]

lemma tableLaw_congr_active (xi : ℝ) (T : TableIndex m) (j : Fin 2)
    (b b' : Fin m → ℝ) (u : unitInterval) (hb : ∀ i ∈ T.1, b i = b' i) :
    tableLaw xi T j b u = tableLaw xi T j b' u := by
  have he : (fun i : T.1 => b i) = fun i : T.1 => b' i :=
    funext (fun i => hb i i.property)
  simp only [tableLaw, tableOwners_congr_active T.1 T.2.1 T.2.2.1
    T.2.2.2.1 b b' u hb, he]

end FullContext
end FCAppendix.Affine.Hybrid.Native02
