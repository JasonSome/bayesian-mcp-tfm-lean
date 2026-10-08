import FCAppendix.Probability.CountPushforward

namespace FCAppendix
namespace Game

open scoped BigOperators

structure JointAction (n : ℕ) where
  bid : ℝ
  bid_nonneg : 0 ≤ bid
  routeCount : ℕ
  routeCount_le : routeCount ≤ n

abbrev LocalList (m : ℕ) := Fin m → Option ℝ

structure Realization (m n : ℕ) where
  action : Fin m → JointAction n
  recipients : Fin m → Finset (Fin n)
  chosen_size : ∀ i, (recipients i).card = (action i).routeCount

noncomputable def observe {m n : ℕ} (x : Realization m n) (j : Fin n) : LocalList m := by
  classical
  exact fun i => if j ∈ x.recipients i then some (x.action i).bid else none

abbrev LocalPolicy (m c : ℕ) (Seed : Type*) :=
  (ℓ : LocalList m) → Seed → {S : Finset (Fin m) // S.card ≤ c ∧ ∀ i ∈ S, ℓ i ≠ none}

noncomputable def allocation {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (j : Fin n) : Finset (Fin m) :=
  (policy j (observe x j) (seed j)).val

noncomputable def accepted {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => i ∈ allocation x policy seed j)

noncomputable def inclusionCount {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : ℕ := (accepted x policy seed i).card

theorem accepted_subset_recipients {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : accepted x policy seed i ⊆ x.recipients i := by
  classical
  intro j hj
  have hij : i ∈ allocation x policy seed j := (Finset.mem_filter.mp hj).2
  have hlocal := (policy j (observe x j) (seed j)).property.2 i hij
  by_contra hnot
  exact hlocal (by simp [observe, hnot])

theorem inclusionCount_le_chosen {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) :
    inclusionCount x policy seed i ≤ (x.action i).routeCount := by
  rw [← x.chosen_size i]
  exact Finset.card_le_card (accepted_subset_recipients x policy seed i)

theorem inclusionCount_le_n {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : inclusionCount x policy seed i ≤ n :=
  le_trans (inclusionCount_le_chosen x policy seed i) (x.action i).routeCount_le

theorem abstention_count_zero {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) (hi : (x.action i).routeCount = 0) :
    inclusionCount x policy seed i = 0 := by
  have h := inclusionCount_le_chosen x policy seed i
  omega

theorem sum_membership {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    (∑ a, if a ∈ S then (1 : ℕ) else 0) = S.card := by
  classical
  rw [← Finset.sum_filter]
  simp

theorem inclusionCount_eq_sum {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) :
    inclusionCount x policy seed i = ∑ j, if i ∈ allocation x policy seed j then 1 else 0 := by
  classical
  rw [inclusionCount, ← sum_membership]
  simp [accepted]

theorem double_count {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) :
    (∑ i, inclusionCount x policy seed i) = ∑ j, (allocation x policy seed j).card := by
  classical
  simp_rw [inclusionCount_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact sum_membership _

theorem total_capacity {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) : ∑ i, inclusionCount x policy seed i ≤ n * c := by
  rw [double_count]
  calc
    _ ≤ ∑ _j : Fin n, c := Finset.sum_le_sum (fun j _ => (policy j (observe x j) (seed j)).property.1)
    _ = _ := by simp

noncomputable def deviate {m n : ℕ} (x : Realization m n) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (R : Finset (Fin n)) : Realization m n := by
  classical
  let a : JointAction n := {
    bid := b
    bid_nonneg := hb
    routeCount := R.card
    routeCount_le := by simpa using (Finset.card_le_univ R) }
  exact {
    action := Function.update x.action i a
    recipients := Function.update x.recipients i R
    chosen_size := fun j => by
      by_cases h : j = i
      · subst j
        simp [a]
      · simpa [Function.update, h] using x.chosen_size j }

theorem deviate_rival_action {m n : ℕ} (x : Realization m n) (i j : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (R : Finset (Fin n)) (hji : j ≠ i) :
    (deviate x i b hb R).action j = x.action j := by
  classical
  simp [deviate, Function.update, hji]

theorem observe_old_recipient {m n : ℕ} (x : Realization m n) (i : Fin m)
    (R : Finset (Fin n)) (hR : x.recipients i ⊆ R) (j : Fin n)
    (hj : j ∈ x.recipients i) :
    observe (deviate x i (x.action i).bid (x.action i).bid_nonneg R) j = observe x j := by
  classical
  funext u
  by_cases hu : u = i
  · subst u
    simp [observe, deviate, hj, hR hj]
  · simp [observe, deviate, Function.update, hu]

theorem accepted_mono_add_routes {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m)
    (R : Finset (Fin n)) (hR : x.recipients i ⊆ R) :
    accepted x policy seed i ⊆
      accepted (deviate x i (x.action i).bid (x.action i).bid_nonneg R) policy seed i := by
  classical
  intro j hj
  have hr := accepted_subset_recipients x policy seed i hj
  have ho := observe_old_recipient x i R hR j hr
  have ha : i ∈ allocation x policy seed j := (Finset.mem_filter.mp hj).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold allocation at ha ⊢
  rw [ho]
  exact ha

theorem count_mono_add_routes {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m)
    (R : Finset (Fin n)) (hR : x.recipients i ⊆ R) :
    inclusionCount x policy seed i ≤
      inclusionCount (deviate x i (x.action i).bid (x.action i).bid_nonneg R) policy seed i :=
  Finset.card_le_card (accepted_mono_add_routes x policy seed i R hR)

noncomputable def boundedCount {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : Fin (n + 1) :=
  ⟨inclusionCount x policy seed i, by have := inclusionCount_le_n x policy seed i; omega⟩

end Game
end FCAppendix
