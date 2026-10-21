import FCAppendix.Affine.Tail04.NativeCountCoordinates
import FCAppendix.Affine.Tail04.OrderedNativePolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeCountCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeCountCoordinates LocalCoordinates Hybrid

variable {m c : ℕ} (D : Data m c)

def pair (L K : LocalList m) (i : Fin m) (u v : Seed) : Fin 3 :=
  boolPairCount (decide (i∈(OrderedNativePolicy.policy D 0 L u).val),
    decide (i∈(OrderedNativePolicy.policy D 1 K v).val))

def zeroList (L K : LocalList m) : LocalList m :=
  if OrderedNativePolicy.role D.E 0 L=0 then L else K

def oneList (L K : LocalList m) : LocalList m :=
  if OrderedNativePolicy.role D.E 0 L=0 then K else L

def zeroSeed (L : LocalList m) (u v : Seed) : Seed :=
  if OrderedNativePolicy.role D.E 0 L=0 then u else v

def oneSeed (L : LocalList m) (u v : Seed) : Seed :=
  if OrderedNativePolicy.role D.E 0 L=0 then v else u

lemma boolPairCount_comm (a b : Bool) : boolPairCount (a,b)=boolPairCount (b,a) := by
  cases a <;> cases b <;> rfl

lemma role_zero_iff (L : LocalList m) :
    OrderedNativePolicy.role D.E 0 L=0 ↔ D.E.localCount L 2≤D.E.otherPrivateCount L := by
  simp only [OrderedNativePolicy.role,OrderedHigherRoles.first]
  split_ifs <;> simp_all <;> omega

lemma roles_opposite {L K : LocalList m} (h : D.E.Compatible L K) :
    OrderedNativePolicy.role D.E 1 K=otherProposer (OrderedNativePolicy.role D.E 0 L) := by
  simpa only [otherProposer,ite_true] using OrderedNativePolicy.role_pair D.E h 0

theorem pair_eq_restored {L K : LocalList m} (h : D.E.Compatible L K)
    (i : Fin m) (u v : Seed) :
    pair D L K i u v=NativeCountCoordinates.listPairCount D
      (zeroList D L K) (oneList D L K) i (zeroSeed D L u v) (oneSeed D L u v) := by
  have hop := roles_opposite D h
  dsimp only [zeroList,oneList,zeroSeed,oneSeed]
  by_cases hz : OrderedNativePolicy.role D.E 0 L=0
  · simp only [if_pos hz]
    rw [hz] at hop
    unfold pair OrderedNativePolicy.policy NativeCountCoordinates.listPairCount
    rw [hz,hop]
    rfl
  · have ho : OrderedNativePolicy.role D.E 0 L=1 := by
      have hh := (OrderedNativePolicy.role D.E 0 L).isLt
      omega
    simp only [if_neg hz]
    rw [ho] at hop
    unfold pair OrderedNativePolicy.policy NativeCountCoordinates.listPairCount
    rw [ho,hop]
    exact boolPairCount_comm _ _

lemma ordered_compatible {L K : LocalList m} (h : D.E.Compatible L K) :
    D.E.Compatible (zeroList D L K) (oneList D L K) := by
  unfold zeroList oneList
  split
  · exact h
  · exact D.E.compatible_symm h

theorem ordered_private_counts {L K : LocalList m} (h : D.E.Compatible L K) :
    D.E.localCount (zeroList D L K) 2=min (D.E.localCount L 2) (D.E.localCount K 2) ∧
    D.E.localCount (oneList D L K) 2=max (D.E.localCount L 2) (D.E.localCount K 2) := by
  have hk : D.E.otherPrivateCount L=D.E.localCount K 2 := by
    simpa only [ids_card] using D.E.otherPrivateCount_pair h
  by_cases hz : OrderedNativePolicy.role D.E 0 L=0
  · have hh := (role_zero_iff D L).mp hz
    rw [hk] at hh
    simp only [zeroList,oneList,if_pos hz,min_eq_left hh,max_eq_right hh]
    trivial
  · have hh : D.E.localCount K 2≤D.E.localCount L 2 := by
      have hn := (role_zero_iff D L).not.mp hz
      omega
    simp only [zeroList,oneList,if_neg hz,min_eq_right hh,max_eq_left hh]
    trivial

theorem boundedCount_eq_pair (x : Realization m 2) (s : Fin 2→Seed) (i : Fin m) :
    Game.boundedCount x (OrderedNativePolicy.policy D) s i=
      pair D (observe x 0) (observe x 1) i (s 0) (s 1) := by
  apply Fin.ext
  simp only [Game.boundedCount,inclusionCount_eq_sum,Fin.sum_univ_two,
    allocation,pair,boolPairCount,decide_eq_true_eq]
  rfl

end FCAppendix.Affine.Tail04.OrderedNativeCountCoordinates
