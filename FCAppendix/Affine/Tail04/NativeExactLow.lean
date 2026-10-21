import FCAppendix.AppendixRepair.GeneralLow.ExactLowPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeExactLow
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open FCAppendix.Affine.Hybrid
open Existence.PayOnceBounded (listBids)
open scoped BigOperators

namespace Direct
export FCAppendix.AppendixRepair.GeneralLow.ExactLow
  (select select_feasible select_optimal measurable_select acceptance receipt
   seedAveragePayoff seed_average_payoff_eq_residualPayoff zero_payoff_le_positive select_copy)
end Direct

variable {m : ℕ}

abbrev residual := @NativeContinuation.residual

def select (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) : Finset (Fin m) :=
  Direct.select ξ hξ hξ1 X.1 (residual c j X) (residual c (otherProposer j) X) s

lemma measurable_select (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (j : Fin 2) :
    Measurable (Function.uncurry (select (m:=m) ξ hξ hξ1 c j)) := by
  exact Direct.measurable_select ξ hξ hξ1
    (fun q : ClassifiedContext m × unitInterval => q.1.1) measurable_fst.fst
    (fun q => residual c j q.1) (fun q => residual c (otherProposer j) q.1)
    ((NativeContinuation.measurable_residual c j).comp measurable_fst)
    ((NativeContinuation.measurable_residual c (otherProposer j)).comp measurable_fst)
    Prod.snd measurable_snd

lemma select_feasible (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (s : unitInterval) :
    LocallyFeasible X.1 (residual c j X) (select ξ hξ hξ1 c j X s) :=
  Direct.select_feasible ξ hξ hξ1 X.1 (residual c j X) (residual c (otherProposer j) X) s

def acceptance (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  ∫ s : unitInterval, if i ∈ select ξ hξ hξ1 c j X s then (1:ℝ) else 0

def receipt (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  entryBid (X.1 i) * (1 - ξ * acceptance ξ hξ hξ1 c (otherProposer j) X i)

lemma receipt_eq_direct (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) :
    receipt ξ hξ hξ1 c j X =
      Direct.receipt ξ hξ hξ1 X.1 (residual c j X) (residual c (otherProposer j) X) := by
  funext i
  have hb : listBids X.1 i = entryBid (X.1 i) := by
    cases h : X.1 i <;> simp [listBids,entryBid,h]
  simp only [receipt,FCAppendix.AppendixRepair.GeneralLow.ExactLow.receipt,hb]
  congr 2
  unfold acceptance select FCAppendix.AppendixRepair.GeneralLow.ExactLow.acceptance
  rw [otherProposer_other j]

lemma select_numerical_optimal (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (_hX : NonnegativeList X.1) (j : Fin 2) (s : unitInterval) :
    Finite.Optimal (residual c j X) (receipt ξ hξ hξ1 c j X)
      (select ξ hξ hξ1 c j X s) := by
  rw [receipt_eq_direct]
  exact Direct.select_optimal ξ hξ hξ1 X.1 (residual c j X)
    (residual c (otherProposer j) X) s

theorem select_copy (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (j : Fin 2) (X Y : ClassifiedContext m) (hXY : X = Y) (s : unitInterval) :
    select ξ hξ hξ1 c j X s = select ξ hξ hξ1 c j Y s := by
  subst Y
  rfl

end FCAppendix.Affine.Tail04.NativeExactLow
