import FCAppendix.Affine.Hybrid.CollapsedContext

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
open scoped BigOperators
variable {m N : ℕ}

lemma low_included_implies_active_underflow (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX:NonnegativeList X.1) (j : Fin 2) (s : unitInterval)
    (d : ℝ) (A : Finset (Fin m)) (hA:∀k∈A,d<(1-ξ)*entryBid (X.1 k))
    (hlow:∀k∉A,entryBid (X.1 k) ≤ d) (i : Fin m) (hi:i∉A)
    (hs:i∈select ξ hξ hξ1 c j X s) : A.card<residual c j X:=by
  by_contra hn
  exact hi (low_excluded_under_active_overload ξ hξ hξ1 c X hX j s d A hA hlow
    (le_of_not_gt hn) hs)

theorem native_duplicate_implies_bothUnderflow (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (Gamma : FiniteGame (N+1) 2 c unitInterval) {d U : ℝ} (hd:0 ≤ d) (hdU:d ≤ U)
    (z : UserProfile (N+1) 2) (hz:z∈classifiedProfiles (N+1) U) (hf:(z 0).1.2.bid ≤ d)
    (hactive:∀i∈upperSet d (actualContext U z).1,d<(1-ξ)*entryBid ((actualContext U z).1 i))
    (s : Fin 2→unitInterval)
    (hdup:inclusionCount (drawsRealization z)
      ((contextPolicy ξ hξ hξ1 c).nativeGame Gamma U).policy s 0=2) :
    BothUnderflow c (fun j=>(collapsedProfileRow d U z j).1):=by
  let X:=actualContext U z
  let A:=upperSet d X.1
  let omega:=collapsedProfileRow d U z
  have hX:NonnegativeList X.1:=by
    change NonnegativeList (actualContext U z).1
    rw [←observedContext_eq_actual z hz 0]
    exact nonnegative_observedContext U 0 _
      ((feasibleObservedList_iff_nonnegative 0 _).mp ⟨z,rfl⟩)
  have hbid:=actualContext_entryBid U z hz 0 (hf.trans hdU)
  have hi:(0:Fin (N+1))∉A:=by
    intro hh
    have hgt:=upperSet_entry_gt X.1 0 hh
    rw [hbid] at hgt
    linarith
  have hlow:∀i∉A,entryBid (X.1 i) ≤ d:=fun i hi=>nonupper_entry_le hd _ i hi
  rw [ContextPolicy.native_inclusionCount_eq_focalCopy _ Gamma U z hz s 0 (hf.trans hdU)] at hdup
  have hboth:0∈select ξ hξ hξ1 c 0 X (s 0) ∧ 0∈select ξ hξ hξ1 c 1 X (s 1):=by
    by_cases h0:0∈select ξ hξ hξ1 c 0 X (s 0)
    · by_cases h1:0∈select ξ hξ hξ1 c 1 X (s 1)
      · exact ⟨h0,h1⟩
      · simp [ContextPolicy.selectionPair,contextPolicy,focalCopy,X,h0,h1] at hdup
    · by_cases h1:0∈select ξ hξ hξ1 c 1 X (s 1) <;>
        simp [ContextPolicy.selectionPair,contextPolicy,focalCopy,X,h0,h1] at hdup
  have hu (j : Fin 2):classCount 1 omega+classCount (upperTag j) omega<c:=by
    have hs:0∈select ξ hξ hξ1 c j X (s j):=by fin_cases j <;> tauto
    have hh:=low_included_implies_active_underflow ξ hξ hξ1 c X hX j (s j) d A hactive hlow 0 hi hs
    have hr:residual c j X-A.card=c-classCount 1 omega-classCount (upperTag j) omega:=
      (collapsed_context_data (c:=c) hdU z hz hf).2.2 j
    omega
  constructor
  · rw [sum_firstHigher]
    exact hu 0
  · rw [sum_secondHigher]
    exact hu 1

end FCAppendix.Affine.Hybrid.NativeContinuation
