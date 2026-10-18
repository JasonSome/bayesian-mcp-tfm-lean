import FCAppendix.Exclusive.ActionLawTransport
import FCAppendix.Exclusive.NarrowExistenceCanonicalRow

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Existence
open scoped BigOperators

def actionRivalCount {m n : ℕ} (a : Fin m → JointAction n) : ℕ :=
  ∑ j, if (a j).routeCount = 0 then 0 else 1

def actionRivalWeight {m : ℕ} (n : ℕ) (a : Fin m → JointAction n) : ℝ :=
  ∑ j, if (a j).routeCount = 0 then 0 else inverseBid n (a j).bid

theorem sum_erase_eq_succAbove {m : ℕ} {M : Type*} [AddCancelCommMonoid M]
    (i : Fin (m+1)) (f : Fin (m+1) → M) :
    (∑ j ∈ Finset.univ.erase i, f j) = ∑ j : Fin m, f (i.succAbove j) := by
  classical
  have he := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ i)
  have hs := Fin.sum_univ_succAbove f i
  exact add_right_cancel (he.trans (hs.trans (add_comm _ _)))

theorem rivalCount_eq_actionRivalCount {m n : ℕ} (i : Fin (m+1)) (d : UserProfile (m+1) n) :
    rivalCount i d = 1+actionRivalCount (fun j : Fin m => (d (i.succAbove j)).1.2) := by
  classical
  rw [rivalCount, activeRivals, Finset.card_eq_sum_ones, Finset.sum_filter]
  have he := sum_erase_eq_succAbove i (fun j => if (d j).1.2.routeCount = 0 then 0 else (1:ℕ))
  change (∑ j ∈ Finset.univ.erase i, if ¬(d j).1.2.routeCount = 0 then 1 else 0)+1 = _
  simp_rw [ite_not]
  rw [he]
  exact add_comm _ _

theorem rivalWeight_eq_actionRivalWeight {m n : ℕ} (i : Fin (m+1)) (d : UserProfile (m+1) n) :
    rivalWeight i d = actionRivalWeight n (fun j : Fin m => (d (i.succAbove j)).1.2) := by
  classical
  rw [rivalWeight, activeRivals, Finset.sum_filter]
  simp_rw [ite_not]
  exact sum_erase_eq_succAbove i _

theorem measurable_actionRivalCount {m n : ℕ} :
    Measurable (actionRivalCount (m := m) (n := n)) := by
  unfold actionRivalCount
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_eq_fun ((measurable_routeCount n).comp (measurable_pi_apply j))
    measurable_const) measurable_const measurable_const

theorem measurable_actionRivalWeight {m : ℕ} (n : ℕ) :
    Measurable (actionRivalWeight (m := m) n) := by
  unfold actionRivalWeight
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_eq_fun ((measurable_routeCount n).comp (measurable_pi_apply j))
    measurable_const) measurable_const
      (((measurable_bid n).comp (measurable_pi_apply j)).pow_const (-rate n))

theorem actionRivalCount_flag {m n : ℕ} {V : Type*} (hn : 0 < n) (b : V → ℝ)
    (omega : RivalProfile m V) :
    actionRivalCount (fun j => flagAction n b (omega j)) = activeCount omega := by
  unfold actionRivalCount activeCount
  apply Finset.sum_congr rfl
  intro j _
  cases h : (omega j).1 <;> simp [flagAction, h, activeNat, Interim.abstain, hn.ne']

theorem actionRivalWeight_flag {m n : ℕ} {V : Type*} (hn : 0 < n) (b : V → ℝ)
    (hb : ∀ v, 0 ≤ b v) (omega : RivalProfile m V) :
    actionRivalWeight n (fun j => flagAction n b (omega j)) =
      ∑ j, activeBit (omega j).1*inverseBid n (b (omega j).2) := by
  unfold actionRivalWeight
  apply Finset.sum_congr rfl
  intro j _
  cases h : (omega j).1 <;> simp [flagAction, h, activeBit, Interim.abstain, hn.ne', max_eq_left (hb _)]

end FCAppendix.Bayes.ExclusiveConstruction
