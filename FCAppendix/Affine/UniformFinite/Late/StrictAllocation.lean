import FCAppendix.Affine.UniformFinite.Late.StrictReceivedPolicy
import FCAppendix.Affine.Hybrid.NativeAllocationCounts

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.Strict
open MeasureTheory ProbabilityTheory Game Bayes Set Classical LowBody
open Hybrid
open scoped BigOperators
variable {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem native_allocation_mem_iff (C : ContextPolicy M c Seed) (Γ : FiniteGame M 2 c Seed)
    (R : ℝ) (d : UserProfile M 2) (hd : d∈profiles M R) (s : Fin 2→ Seed)
    (j : Fin 2) (a : Fin M) (ha : (d a).1.2.bid< R) :
    a∈allocation (drawsRealization d) (nativeGame C Γ R).policy s j ↔
      a∈C.select j (actualContext R d) (s j) := by
  have hlow : lowerPart R (observe (drawsRealization d) j) a≠none := by
    rw [lowerPart_observe d hd j]
    simp only [if_pos ha,ne_eq,Option.some_ne_none,not_false_eq_true]
  have hf := factors C R j (observe (drawsRealization d) j) (s j) a hlow
  rw [observedContext_eq_actual d hd j] at hf
  exact hf

theorem native_inclusionCount_eq_focalCopy (C : ContextPolicy M c Seed)
    (Γ : FiniteGame M 2 c Seed) (R : ℝ) (d : UserProfile M 2)
    (hd : d∈profiles M R) (s : Fin 2→ Seed) (a : Fin M) (ha : (d a).1.2.bid< R) :
    inclusionCount (drawsRealization d) (nativeGame C Γ R).policy s a=
      (focalCopy (C.selectionPair (actualContext R d) s) a).val := by
  rw [inclusionCount_eq_sum,Fin.sum_univ_two]
  simp only [native_allocation_mem_iff C Γ R d hd s 0 a ha,
    native_allocation_mem_iff C Γ R d hd s 1 a ha]
  by_cases h0 : a∈C.select 0 (actualContext R d) (s 0) <;>
    by_cases h1 : a∈C.select 1 (actualContext R d) (s 1) <;>
    simp [Hybrid.ContextPolicy.selectionPair,focalCopy,h0,h1]

theorem actualContext_entryBid (R : ℝ) (d : UserProfile M 2)
    (hd : d∈profiles M R) (a : Fin M) (ha : (d a).1.2.bid< R) :
    entryBid ((actualContext R d).1 a)=(d a).1.2.bid := by
  change entryBid (lowerPart R (observe (drawsRealization d) 0) a)=_
  rw [lowerPart_observe d hd 0]
  dsimp only
  rw [if_pos ha]
  rfl

end FCAppendix.Affine.UniformFinite.Late.Strict
