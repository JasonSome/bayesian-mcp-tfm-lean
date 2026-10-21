import FCAppendix.AppendixRepair.GeneralLow.Continuation

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.NormalizedContinuation
open MeasureTheory ProbabilityTheory Game Bayes Set Filter
open HigherPolicy HigherPosterior HigherReceipts Continuation
open scoped BigOperators Classical

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def receiptPart (C : Information.Classifier) (r : Fin m → ℝ) (L : LocalList m) : LocalList m :=
  fun i => if i ∈ highSet C L then some (r i) else none

theorem receiptPart_present (C : Information.Classifier) (r : Fin m → ℝ)
    (L : LocalList m) (i : Fin m) : receiptPart C r L i ≠ none ↔ i ∈ highSet C L := by
  classical
  simp [receiptPart]

theorem measurable_receiptPart {X : Type*} [MeasurableSpace X]
    (C : Information.Classifier) (r : X → Fin m → ℝ)
    (hr : ∀ i, Measurable (fun x => r x i)) (L : X → LocalList m) (hL : Measurable L) :
    Measurable (fun x => receiptPart C (r x) (L x)) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    (((measurable_highSet C).comp hL) (MeasurableSet.of_discrete :
      MeasurableSet {S : Finset (Fin m) | i ∈ S}))
    (measurable_some.comp (hr i)) measurable_const

theorem entry_receiptPart (C : Information.Classifier) (r : Fin m → ℝ)
    (L : LocalList m) (hz : ∀ i ∉ highSet C L, r i = 0) :
    (fun i => entryBid (receiptPart C r L i)) = r := by
  classical
  funext i
  by_cases hi : i ∈ highSet C L
  · simp [receiptPart, hi, entryBid]
  · simp [receiptPart, hi, entryBid, hz i hi]

def select (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed) :
    Finset (Fin m) :=
  if BothSaturated C c L then
    if L ∈ Continuation.core Γ C d κ R hfull H j then
      if Finite.Optimal c (highReceipt Γ C d κ R hfull H j L) (H.select j L z)
      then H.select j L z
      else HighestBid.selection (receiptPart C (highReceipt Γ C d κ R hfull H j L) L) c
    else HighestBid.selection (weightedPart C 1 L) c
  else H.select j L z

theorem select_card (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed) :
    (select Γ C d κ R hfull H j L z).card ≤ c := by
  unfold select
  split_ifs
  · exact H.card_le j L z
  · exact (HighestBid.selection_best _ c).1.1
  · exact (HighestBid.selection_best _ c).1.1
  · exact H.card_le j L z

theorem select_subset (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m) (z : Seed) :
    select Γ C d κ R hfull H j L z ⊆ highSet C L := by
  classical
  unfold select
  split_ifs
  · exact H.subset_high j L z
  · intro i hi
    exact (receiptPart_present C _ L i).mp ((HighestBid.selection_best _ c).1.2 i hi)
  · intro i hi
    exact (weightedPart_present C 1 L i).mp ((HighestBid.selection_best _ c).1.2 i hi)
  · exact H.subset_high j L z

theorem measurable_select (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) :
    Measurable (Function.uncurry (select Γ C d κ R hfull H j)) := by
  apply Measurable.ite ((measurableSet_bothSaturated C c).preimage measurable_fst)
  · apply Measurable.ite
      ((Continuation.measurableSet_core Γ C d κ R hfull H j).preimage measurable_fst)
    · apply Measurable.ite
        (measurableSet_optimal_select
          (fun p : LocalList m × Seed => highReceipt Γ C d κ R hfull H j p.1)
          (fun i => (measurable_highReceipt Γ C d κ R hfull H j i).comp measurable_fst)
          (Function.uncurry (H.select j)) (H.measurable j) c) (H.measurable j)
      exact (HighestBid.measurable_selection m c).comp
        (measurable_receiptPart C _
          (fun i => (measurable_highReceipt Γ C d κ R hfull H j i).comp measurable_fst)
          Prod.fst measurable_fst)
    · exact (HighestBid.measurable_selection m c).comp
        ((measurable_weightedPart C 1).comp measurable_fst)
  · exact H.measurable j

def selector (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) : HigherSelector (m := m) C c Seed where
  select := select Γ C d κ R hfull H
  measurable := measurable_select Γ C d κ R hfull H
  card_le := select_card Γ C d κ R hfull H
  subset_high := select_subset Γ C d κ R hfull H

theorem select_ae_eq (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m)
    (hL : L ∈ Continuation.core Γ C d κ R hfull H j) :
    ∀ᵐ z ∂Γ.seedLaw, select Γ C d κ R hfull H j L z = H.select j L z := by
  by_cases hs : BothSaturated C c L
  · filter_upwards [Continuation.core_optimal Γ C d κ R hfull H j L hL hs] with z hz
    simp only [select, if_pos hs, if_pos hL, if_pos hz]
  · exact ae_of_all _ (fun z => by simp only [select, if_neg hs])

theorem selector_ae_eq (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HC Γ C d κ R hfull) (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j, ∀ᵐ z ∂Γ.seedLaw,
      (selector Γ C d κ R hfull H.selector).select j L z = H.selector.select j L z := by
  filter_upwards [Continuation.ae_core Γ C d κ R hfull H j] with L hL
  exact select_ae_eq Γ C d κ R hfull H.selector j L hL

theorem select_optimal_core (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) (L : LocalList m)
    (hL : L ∈ Continuation.core Γ C d κ R hfull H j) (hs : BothSaturated C c L)
    (z : Seed) :
    Finite.Optimal c (highReceipt Γ C d κ R hfull H j L)
      (select Γ C d κ R hfull H j L z) := by
  classical
  unfold select
  rw [if_pos hs, if_pos hL]
  split_ifs with hz
  · exact hz
  · have he := entry_receiptPart C (highReceipt Γ C d κ R hfull H j L) L
      (fun i hi => by simp only [highReceipt, if_neg hi])
    have hh := HighestBid.selection_optimal
      (receiptPart C (highReceipt Γ C d κ R hfull H j L) L) c
    rw [he] at hh
    exact hh

def bad (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) : Set (LocalList m) :=
  {L | BothSaturated C c L} ∩ (Continuation.core Γ C d κ R hfull H j)ᶜ

theorem measurableSet_bad (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) :
    MeasurableSet (bad Γ C d κ R hfull H j) :=
  (measurableSet_bothSaturated C c).inter
    (Continuation.measurableSet_core Γ C d κ R hfull H j).compl

def privateKernel (j : Fin 2) : Kernel (LocalList m) (UserProfile m 2) :=
  Kernel.deterministic (privateProfile j) (measurable_privateProfile j)

instance (j : Fin 2) : IsMarkovKernel (privateKernel (m := m) j) := by
  unfold privateKernel
  infer_instance

def posteriorKernel (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) :
    Kernel (LocalList m) (UserProfile m 2) :=
  Kernel.piecewise (measurableSet_bad Γ C d κ R hfull H j) (privateKernel j)
    ((HigherPosterior.posterior Γ C d κ R hfull).posterior j)

instance (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HigherSelector (m := m) C c Seed) (j : Fin 2) :
    IsMarkovKernel (posteriorKernel Γ C d κ R hfull H j) := by
  unfold posteriorKernel
  infer_instance

def posterior (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (H : HC Γ C d κ R hfull) : PosteriorSystem Γ where
  posterior := posteriorKernel Γ C d κ R hfull H.selector
  markov := fun _ => inferInstance
  on_path j := by
    have he : posteriorKernel Γ C d κ R hfull H.selector j =ᵐ[observedListLaw Γ j]
        (HigherPosterior.posterior Γ C d κ R hfull).posterior j := by
      filter_upwards [Continuation.ae_core Γ C d κ R hfull H j] with L hL
      have hn : L ∉ bad Γ C d κ R hfull H.selector j := fun h => h.2 hL
      simp only [posteriorKernel, Kernel.piecewise_apply, if_neg hn]
    exact ((HigherPosterior.posterior Γ C d κ R hfull).on_path j).trans
      (Measure.compProd_congr he).symm
  feasible j L hL := by
    by_cases hb : L ∈ bad Γ C d κ R hfull H.selector j
    · simp only [posteriorKernel, Kernel.piecewise_apply, if_pos hb,
        privateKernel, Kernel.deterministic_apply]
      apply (ae_dirac_iff
        (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
      exact observe_privateProfile j L ((feasibleObservedList_iff_nonnegative j L).mp hL)
    · simp only [posteriorKernel, Kernel.piecewise_apply, if_neg hb]
      exact (HigherPosterior.posterior Γ C d κ R hfull).feasible j L hL

def rebasePosterior (Γ Δ : FiniteGame m 2 c Seed)
    (hpop : userProfileLaw Δ = userProfileLaw Γ) (B : PosteriorSystem Γ) : PosteriorSystem Δ where
  posterior := B.posterior
  markov := B.markov
  on_path j := by
    change (userProfileLaw Δ).map (fun x => (observe (drawsRealization x) j, x)) =
      (observedListLaw Δ j) ⊗ₘ B.posterior j
    unfold observedListLaw
    rw [hpop]
    exact B.on_path j
  feasible := B.feasible

end FCAppendix.Appendix08.GeneralLow.NormalizedContinuation
