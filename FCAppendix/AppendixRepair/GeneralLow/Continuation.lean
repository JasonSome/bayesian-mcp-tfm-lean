import FCAppendix.AppendixRepair.GeneralLow.HigherReceipts
import FCAppendix.AppendixRepair.GeneralLow.PosteriorCore
import FCAppendix.Game.PosteriorReceipts

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.Continuation
open MeasureTheory ProbabilityTheory Game Bayes Set Filter
open HigherPosterior HigherPolicy HigherReceipts
open scoped BigOperators

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def BothSaturated (C : Information.Classifier) (c : ℕ) (L : LocalList m) : Prop :=
  c ≤ (highSet C L).card ∧ c ≤ otherHigh C L

theorem measurableSet_bothSaturated (C : Information.Classifier) (c : ℕ) :
    MeasurableSet {L : LocalList m | BothSaturated C c L} :=
  (measurableSet_le measurable_const (measurable_highCard C)).inter
    (measurableSet_le measurable_const (measurable_otherHigh C))

def higherGame (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (H : HigherSelector (m := m) C c Seed) : FiniteGame m 2 c Seed :=
  { Γ with
    policy := fun j L z => ⟨H.select j L z, H.card_le j L z,
      fun i hi => highSet_present C L i (H.subset_high j L z hi)⟩
    policy_measurable := H.measurable }

theorem higherGame_userProfileLaw (Γ : FiniteGame m 2 c Seed)
    (C : Information.Classifier) (H : HigherSelector (m := m) C c Seed) :
    userProfileLaw (higherGame Γ C H) = userProfileLaw Γ := rfl

theorem higherGame_seedLaw (Γ : FiniteGame m 2 c Seed)
    (C : Information.Classifier) (H : HigherSelector (m := m) C c Seed) :
    (higherGame Γ C H).seedLaw = Γ.seedLaw := rfl

theorem higherGame_rejects_low (Γ : FiniteGame m 2 c Seed)
    (C : Information.Classifier) (H : HigherSelector (m := m) C c Seed)
    (j : Fin 2) (L : LocalList m) (z : Seed) (i : Fin m)
    (hi : Information.tag C (L i) = 0) :
    i ∉ ((higherGame Γ C H).policy j L z).val := by
  intro hin
  exact highSet_not_low C L i (H.subset_high j L z hin) hi

def higherPosterior (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) : PosteriorSystem (higherGame Γ C H) :=
  posterior (higherGame Γ C H) C d κ R hfull

def highReceipt (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m)
    (i : Fin m) : ℝ :=
  if i ∈ highSet C L then
    beliefReceipts Γ.A (posteriorCountBelief (higherGame Γ C H)
      (higherPosterior Γ C d κ R hfull H) j L) L i
  else 0

structure HC (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ) where
  selector : HigherSelector (m := m) C c Seed
  optimal : ∀ j, ∀ᵐ L ∂observedListLaw Γ j, BothSaturated C c L →
    ∀ᵐ z ∂Γ.seedLaw, Finite.Optimal c
      (highReceipt Γ C d κ R hfull selector j L) (selector.select j L z)

theorem measurable_beliefReceipts (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (j : Fin 2) (i : Fin m) :
    Measurable (fun L : LocalList m => beliefReceipts Γ.A
      (posteriorCountBelief Γ B j L) L i) := by
  have he (L : LocalList m) : beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L i =
      entryBid (L i) * posteriorReceiptFactor Γ B j L i := by
    cases hi : L i with
    | none => simp [beliefReceipts, hi, entryBid]
    | some b =>
        simp only [beliefReceipts, hi, entryBid]
        exact conditionalReceipt_eq_mul_ratio_expect Γ.A _ b
  simp_rw [he]
  exact (measurable_entryBid.comp (measurable_pi_apply i)).mul
    (measurable_posteriorReceiptFactor Γ B j i)

theorem measurable_highReceipt (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (i : Fin m) :
    Measurable (fun L : LocalList m => highReceipt Γ C d κ R hfull H j L i) := by
  apply Measurable.ite
    ((measurable_highSet C) (MeasurableSet.of_discrete :
      MeasurableSet {S : Finset (Fin m) | i ∈ S}))
  · exact measurable_beliefReceipts (higherGame Γ C H)
      (higherPosterior Γ C d κ R hfull H) j i
  · exact measurable_const

theorem measurableSet_fixedOptimal {X : Type*} [MeasurableSpace X]
    (r : X → Fin m → ℝ) (hr : ∀ i, Measurable (fun x => r x i))
    (c : ℕ) (S : Finset (Fin m)) : MeasurableSet {x | Finite.Optimal c (r x) S} := by
  classical
  have hsum (T : Finset (Fin m)) : Measurable (fun x => ∑ i ∈ T, r x i) :=
    Finset.measurable_sum _ fun i _ => hr i
  have he : {x | Finite.Optimal c (r x) S} =
      {x | S.card ≤ c} ∩ ⋂ T : Finset (Fin m),
        {x | T.card ≤ c → (∑ i ∈ T, r x i) ≤ ∑ i ∈ S, r x i} := by
    ext x
    simp [Finite.Optimal]
  rw [he]
  apply (MeasurableSet.const _).inter
  apply MeasurableSet.iInter
  intro T
  by_cases hT : T.card ≤ c
  · simpa only [hT, true_implies] using measurableSet_le (hsum T) (hsum S)
  · simp only [hT, false_implies, setOf_true]
    exact MeasurableSet.univ

theorem measurableSet_optimal_select {X : Type*} [MeasurableSpace X]
    (r : X → Fin m → ℝ) (hr : ∀ i, Measurable (fun x => r x i))
    (f : X → Finset (Fin m)) (hf : Measurable f) (c : ℕ) :
    MeasurableSet {x | Finite.Optimal c (r x) (f x)} := by
  classical
  have he : {x | Finite.Optimal c (r x) (f x)} =
      ⋃ S : Finset (Fin m), {x | f x = S} ∩ {x | Finite.Optimal c (r x) S} := by
    ext x
    simp
  rw [he]
  exact MeasurableSet.iUnion fun S =>
    (measurableSet_eq_fun hf measurable_const).inter (measurableSet_fixedOptimal r hr c S)

def good (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) : Set (LocalList m) :=
  {L | BothSaturated C c L → ∀ᵐ z ∂Γ.seedLaw,
    Finite.Optimal c (highReceipt Γ C d κ R hfull H j L) (H.select j L z)}

theorem measurableSet_good (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) :
    MeasurableSet (good Γ C d κ R hfull H j) := by
  have hg : MeasurableSet {p : LocalList m × Seed |
      ¬ Finite.Optimal c (highReceipt Γ C d κ R hfull H j p.1)
        (H.select j p.1 p.2)} :=
    (measurableSet_optimal_select
      (fun p : LocalList m × Seed => highReceipt Γ C d κ R hfull H j p.1)
      (fun i => (measurable_highReceipt Γ C d κ R hfull H j i).comp measurable_fst)
      (Function.uncurry (H.select j)) (H.measurable j) c).compl
  have hm : Measurable (fun L : LocalList m => Γ.seedLaw
      {z | ¬ Finite.Optimal c (highReceipt Γ C d κ R hfull H j L) (H.select j L z)}) :=
    measurable_measure_prodMk_left hg
  have he : good Γ C d κ R hfull H j =
      {L | BothSaturated C c L}ᶜ ∪
      {L | Γ.seedLaw {z | ¬ Finite.Optimal c
        (highReceipt Γ C d κ R hfull H j L) (H.select j L z)} = 0} := by
    ext L
    simp only [good, mem_setOf_eq, mem_union, mem_compl_iff, imp_iff_not_or, ae_iff]
  rw [he]
  exact (measurableSet_bothSaturated C c).compl.union
    (measurableSet_eq_fun hm measurable_const)

def core (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) : Fin 2 → Set (LocalList m) :=
  PosteriorCore.core Γ (posterior Γ C d κ R hfull) (good Γ C d κ R hfull H)

theorem measurableSet_core (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) :
    MeasurableSet (core Γ C d κ R hfull H j) :=
  PosteriorCore.measurableSet_core Γ (posterior Γ C d κ R hfull)
    (good Γ C d κ R hfull H) (measurableSet_good Γ C d κ R hfull H) j

theorem ae_core (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HC Γ C d κ R hfull) (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j, L ∈ core Γ C d κ R hfull H.selector j :=
  PosteriorCore.ae_core Γ (posterior Γ C d κ R hfull)
    (good Γ C d κ R hfull H.selector) (measurableSet_good Γ C d κ R hfull H.selector)
    H.optimal j

theorem core_optimal (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m)
    (hL : L ∈ core Γ C d κ R hfull H j) (hsat : BothSaturated C c L) :
    ∀ᵐ z ∂Γ.seedLaw, Finite.Optimal c
      (highReceipt Γ C d κ R hfull H j L) (H.select j L z) :=
  (PosteriorCore.core_subset Γ (posterior Γ C d κ R hfull)
    (good Γ C d κ R hfull H) j hL) hsat

theorem core_posterior (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m)
    (hL : L ∈ core Γ C d κ R hfull H j) :
    ∀ᵐ x ∂(posterior Γ C d κ R hfull).posterior j L,
      ∀ l, observe (drawsRealization x) l ∈ core Γ C d κ R hfull H l :=
  PosteriorCore.core_posterior Γ (posterior Γ C d κ R hfull)
    (good Γ C d κ R hfull H) j L hL

end FCAppendix.Appendix08.GeneralLow.Continuation
