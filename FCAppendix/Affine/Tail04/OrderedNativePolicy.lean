import FCAppendix.Affine.Tail04.NativeObservationPair
import FCAppendix.Affine.Tail04.OrderedHigherRoles

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePolicy
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates NativeLocalPolicy
open FCAppendix.Affine.Hybrid

variable {m c : ℕ} (E : Observable.Regions)

def role (j : Fin 2) (L : LocalList m) : Fin 2 :=
  if OrderedHigherRoles.first j (E.localCount L 2) (E.otherPrivateCount L) then 0 else 1

lemma measurableSet_first (j : Fin 2) :
    MeasurableSet {L : LocalList m |
      OrderedHigherRoles.first j (E.localCount L 2) (E.otherPrivateCount L)} :=
  (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ |
    OrderedHigherRoles.first j p.1 p.2}).preimage
      ((E.measurable_localCount 2).prodMk E.measurable_otherPrivateCount)

lemma measurable_role (j : Fin 2) : Measurable (role E (m:=m) j) :=
  Measurable.ite (measurableSet_first E j) measurable_const measurable_const

lemma role_small (j : Fin 2) (L : LocalList m)
    (h : E.localCount L 2 < E.otherPrivateCount L) : role E j L = 0 :=
  if_pos (OrderedHigherRoles.first_of_lt h)

lemma role_large (j : Fin 2) (L : LocalList m)
    (h : E.otherPrivateCount L < E.localCount L 2) : role E j L = 1 :=
  if_neg (OrderedHigherRoles.not_first_of_gt h)

lemma role_equal (j : Fin 2) (L : LocalList m)
    (h : E.localCount L 2 = E.otherPrivateCount L) : role E j L = j := by
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl <;> simp [role,h,OrderedHigherRoles.first]

lemma role_pair {L K : LocalList m} (h : E.Compatible L K) (j : Fin 2) :
    role E (otherProposer j) K = otherProposer (role E j L) := by
  have h0 : E.otherPrivateCount L = E.localCount K 2 := by
    simpa only [ids_card] using E.otherPrivateCount_pair h
  have h1 : E.otherPrivateCount K = E.localCount L 2 := by
    simpa only [ids_card] using E.otherPrivateCount_pair (E.compatible_symm h)
  rcases lt_trichotomy (E.localCount L 2) (E.otherPrivateCount L) with hs | he | hl
  · rw [role_small E j L hs,role_large E (otherProposer j) K (by omega)]
    rfl
  · rw [role_equal E j L he,role_equal E (otherProposer j) K (by omega)]
  · rw [role_large E j L hl,role_small E (otherProposer j) K (by omega)]
    rfl

lemma lowSelect_label_independent (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (j k : Fin 2) (L : LocalList m) (u : unitInterval) :
    E.lowSelect ξ hξ hξ1 c j L u = E.lowSelect ξ hξ hξ1 c k L u := by
  have hj : j = 0 ∨ j = 1 := by omega
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
    simp [Observable.Regions.lowSelect,NativeExactLow.select,NativeContinuation.residual,
      Observable.Regions.lowContext,Observable.Regions.context,contextUpper,otherProposer]

variable (D : NativeLocalPolicy.Data m c)

def policy (j : Fin 2) : LocalPolicy m c Seed :=
  fun L u => D.completedPolicy (role D.E j L) L u

lemma policy_measurable (j : Fin 2) :
    Measurable (fun z : LocalList m × Seed => (policy D j z.1 z.2).val) := by
  have he : (fun z : LocalList m × Seed => (policy D j z.1 z.2).val) =
      (fun z => if OrderedHigherRoles.first j (D.E.localCount z.1 2) (D.E.otherPrivateCount z.1)
        then (D.completedPolicy 0 z.1 z.2).val else (D.completedPolicy 1 z.1 z.2).val) := by
    funext z
    by_cases h : OrderedHigherRoles.first j (D.E.localCount z.1 2) (D.E.otherPrivateCount z.1) <;>
      simp [policy,role,h]
  rw [he]
  exact Measurable.ite ((measurableSet_first D.E j).preimage measurable_fst)
    (D.completedPolicy_measurable 0) (D.completedPolicy_measurable 1)

def numericalReceipt (j : Fin 2) (L : LocalList m) : Fin m → ℝ :=
  D.completedNumericalReceipt (role D.E j L) L

lemma numerical_optimal (hlow : D.E.d < 1 - D.ξ) (j : Fin 2)
    (L : LocalList m) (hL : NonnegativeList L) (u : Seed) :
    Finite.Optimal c (numericalReceipt D j L) (policy D j L u).val :=
  D.completed_numerical_optimal hlow (role D.E j L) L hL u

lemma policy_on_menu (j : Fin 2) (L : LocalList m) (hL : D.offCommon L = ∅) (u : Seed) :
    policy D j L u = D.policy (role D.E j L) L u :=
  D.completed_on_menu (role D.E j L) L hL u

end FCAppendix.Affine.Tail04.OrderedNativePolicy
