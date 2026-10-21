import FCAppendix.Affine.Hybrid.NativeResidualPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
open scoped BigOperators
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

namespace ContextPolicy

def selectionPair (C : ContextPolicy m c Seed) (X : ClassifiedContext m) (s : Fin 2 → Seed) :
    Finset (Fin m)×Finset (Fin m):=(C.select 0 X (s 0),C.select 1 X (s 1))

theorem native_allocation_mem_iff (C : ContextPolicy m c Seed) (Gamma : FiniteGame m 2 c Seed)
    (U : ℝ) (d : UserProfile m 2) (hd:d∈classifiedProfiles m U) (s : Fin 2 → Seed)
    (j : Fin 2) (i : Fin m) (hi:(d i).1.2.bid ≤ U) :
    i∈allocation (drawsRealization d) (C.nativeGame Gamma U).policy s j↔
      i∈C.select j (actualContext U d) (s j):=by
  have hlow : broadcastPart U (observe (drawsRealization d) j) i≠none:=by
    rw [broadcastPart_observe d hd j]
    simp only [if_pos hi,ne_eq,Option.some_ne_none,not_false_eq_true]
  have hf:=C.factors U j (observe (drawsRealization d) j) (s j) i hlow
  rw [observedContext_eq_actual d hd j] at hf
  exact hf

theorem native_inclusionCount_eq_focalCopy (C : ContextPolicy m c Seed)
    (Gamma : FiniteGame m 2 c Seed) (U : ℝ) (d : UserProfile m 2)
    (hd:d∈classifiedProfiles m U) (s : Fin 2 → Seed) (i : Fin m) (hi:(d i).1.2.bid ≤ U) :
    inclusionCount (drawsRealization d) (C.nativeGame Gamma U).policy s i=
      (focalCopy (C.selectionPair (actualContext U d) s) i).val:=by
  rw [inclusionCount_eq_sum,Fin.sum_univ_two]
  simp only [C.native_allocation_mem_iff Gamma U d hd s 0 i hi,
    C.native_allocation_mem_iff Gamma U d hd s 1 i hi]
  by_cases h0:i∈C.select 0 (actualContext U d) (s 0) <;>
    by_cases h1:i∈C.select 1 (actualContext U d) (s 1) <;>
    simp [selectionPair,focalCopy,h0,h1]

end ContextPolicy

namespace NativeContinuation

lemma selectionPair_pure (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (he:residual c 0 X≠residual c 1 X) (s : Fin 2 → unitInterval) :
    (contextPolicy ξ hξ hξ1 c).selectionPair X s=purePair ξ c X:=by
  change (select ξ hξ hξ1 c 0 X (s 0),select ξ hξ hξ1 c 1 X (s 1))=purePair ξ c X
  rw [select,if_neg he,if_pos rfl,select,if_neg he,if_neg (by decide : (1:Fin 2)≠0)]

theorem native_pure_inclusionCount (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (Gamma : FiniteGame m 2 c unitInterval) (U : ℝ) (d : UserProfile m 2)
    (hd:d∈classifiedProfiles m U) (s : Fin 2 → unitInterval) (i : Fin m) (hi:(d i).1.2.bid ≤ U)
    (he:residual c 0 (actualContext U d)≠residual c 1 (actualContext U d)) :
    inclusionCount (drawsRealization d) ((contextPolicy ξ hξ hξ1 c).nativeGame Gamma U).policy s i=
      (focalCopy (purePair ξ c (actualContext U d)) i).val:=by
  rw [ContextPolicy.native_inclusionCount_eq_focalCopy _ Gamma U d hd s i hi,selectionPair_pure ξ hξ hξ1 c _ he]

lemma actualContext_entryBid (U : ℝ) (d : UserProfile m 2) (hd:d∈classifiedProfiles m U)
    (i : Fin m) (hi:(d i).1.2.bid ≤ U) :
    entryBid ((actualContext U d).1 i)=(d i).1.2.bid:=by
  change entryBid (broadcastPart U (observe (drawsRealization d) 0) i)=_
  rw [broadcastPart_observe d hd 0]
  dsimp only
  rw [if_pos hi]
  rfl

lemma affine_count_payoff_eq_pure (η : ℝ) (hη0:0 ≤ η) (hη1:η ≤ 1)
    (w : ℝ) (b : Fin m → ℝ) (P : Finset (Fin m)×Finset (Fin m)) (i : Fin m)
    (G : ℕ → ℝ) :
    userPayoff w (b i) 0 (Schedule.affine 2 η hη0 hη1).charge G (focalCopy P i).val=
      purePayoff ((1+η)/2) w b P i:=by
  unfold purePayoff
  generalize focalCopy P i=k
  fin_cases k
  · simp [userPayoff,successIndicator,Schedule.affine]
  · simp [userPayoff,successIndicator,Schedule.affine]
  · simp [userPayoff,successIndicator,Schedule.affine]
    ring

theorem native_pure_realized_payoff (η : ℝ) (hη0:0 ≤ η) (hη1:η<1) (c : ℕ)
    (Gamma : FiniteGame m 2 c unitInterval) (U : ℝ) (d : UserProfile m 2)
    (hd:d∈classifiedProfiles m U) (s : Fin 2 → unitInterval) (i : Fin m) (hi:(d i).1.2.bid ≤ U)
    (he:residual c 0 (actualContext U d)≠residual c 1 (actualContext U d)) (w : ℝ) (G : ℕ → ℝ) :
    let ξ:=(1-η)/2
    let hξ:0<ξ:=by dsimp only [ξ];linarith
    let hξ1:ξ<1:=by dsimp only [ξ];linarith
    let C:=contextPolicy (m:=m) ξ hξ hξ1 c
    userPayoff w (d i).1.2.bid 0 (Schedule.affine 2 η hη0 hη1.le).charge G
      (inclusionCount (drawsRealization d) (C.nativeGame Gamma U).policy s i)=
      purePayoff (1-ξ) w (fun k=>entryBid ((actualContext U d).1 k))
        (purePair ξ c (actualContext U d)) i:=by
  dsimp only
  rw [native_pure_inclusionCount _ (by linarith) (by linarith) c Gamma U d hd s i hi he,
    ←actualContext_entryBid U d hd i hi]
  rw [affine_count_payoff_eq_pure η hη0 hη1.le w
    (fun k=>entryBid ((actualContext U d).1 k)) (purePair ((1-η)/2) c (actualContext U d)) i G]
  congr 1
  ring

end NativeContinuation
end FCAppendix.Affine.Hybrid
