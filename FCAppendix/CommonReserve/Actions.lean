import FCAppendix.Existence.HighestBidPolicy
import FCAppendix.Game.Routing

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory
open scoped BigOperators

abbrev Action (n : ℕ) (r : ℝ) :=
  {a : Fin n → Option ℝ // ∀ j b, a j = some b → r ≤ b}

variable {m n c : ℕ} {r : ℝ} {Seed : Type*}

def abstain : Action n r := ⟨fun _ => none, by simp⟩

def singleton (j : Fin n) (b : ℝ) (hb : r ≤ b) : Action n r := by
  classical
  refine ⟨fun l => if l = j then some b else none, ?_⟩
  intro l t ht
  by_cases hl : l = j
  · have he : b = t := by simpa [hl] using ht
    exact he ▸ hb
  · simp [hl] at ht

def erase (a : Action n r) (j : Fin n) : Action n r := by
  classical
  refine ⟨Function.update a.val j none, ?_⟩
  intro l b hb
  by_cases hl : l = j
  · simp [hl] at hb
  · exact a.property l b (by simpa [Function.update, hl] using hb)

abbrev Profile (m n : ℕ) (r : ℝ) := Fin m → Action n r

def observe (x : Profile m n r) (j : Fin n) : LocalList m := fun i => (x i).val j

def allocation (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (j : Fin n) : Finset (Fin m) :=
  (policy j (observe x j) (seed j)).val

def accepted (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => i ∈ allocation x policy seed j)

def count (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : ℕ := (accepted x policy seed i).card

theorem count_le (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : count x policy seed i ≤ n :=
  by classical simpa [count] using (Finset.card_le_univ (accepted x policy seed i))

theorem accepted_present (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) (j : Fin n)
    (hj : j ∈ accepted x policy seed i) : (x i).val j ≠ none := by
  classical
  exact (policy j (observe x j) (seed j)).property.2 i (Finset.mem_filter.mp hj).2

theorem bid_ge_reserve (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) (j : Fin n)
    (hj : j ∈ accepted x policy seed i) : r ≤ Bayes.entryBid ((x i).val j) := by
  have hp := accepted_present x policy seed i j hj
  cases he : (x i).val j with
  | none => exact (hp he).elim
  | some b => exact (x i).property j b he

theorem total_capacity (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) : (∑ i, count x policy seed i) ≤ n * c := by
  classical
  have he : ∀ i, count x policy seed i =
      ∑ j, if i ∈ allocation x policy seed j then 1 else 0 := by
    intro i
    rw [count, ← Game.sum_membership]
    simp [accepted]
  simp_rw [he]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, (allocation x policy seed j).card := by
      apply Finset.sum_congr rfl
      intro j _
      exact Game.sum_membership _
    _ ≤ ∑ _j : Fin n, c :=
      Finset.sum_le_sum fun j _ => (policy j (observe x j) (seed j)).property.1
    _ = _ := by simp

def ofRealization (x : Realization m n)
    (hx : ∀ i, 0 < (x.action i).routeCount → r ≤ (x.action i).bid) : Profile m n r := by
  classical
  intro i
  refine ⟨fun j => Game.observe x j i, ?_⟩
  intro j b hb
  by_cases hj : j ∈ x.recipients i
  · have hbid : (x.action i).bid = b := by simpa [Game.observe, hj] using hb
    rw [← hbid]
    apply hx i
    rw [← x.chosen_size i]
    exact Finset.card_pos.mpr ⟨j, hj⟩
  · simp [Game.observe, hj] at hb

@[simp] theorem observe_ofRealization (x : Realization m n)
    (hx : ∀ i, 0 < (x.action i).routeCount → r ≤ (x.action i).bid) (j : Fin n) :
    observe (ofRealization x hx) j = Game.observe x j := rfl

@[simp] theorem count_ofRealization (x : Realization m n)
    (hx : ∀ i, 0 < (x.action i).routeCount → r ≤ (x.action i).bid)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed) (i : Fin m) :
    count (ofRealization x hx) policy seed i = Game.inclusionCount x policy seed i := rfl

end FCAppendix.CommonReserve
