import FCAppendix.Affine.Tail04.SortedCoordinates
import FCAppendix.Affine.Tail04.AllCountHighPolicy
import FCAppendix.Affine.Tail04.NativeExactLow

noncomputable section
namespace FCAppendix.Affine.Tail04.LowResidualCompletion
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon
open FCAppendix.Affine.Hybrid

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

lemma optimal_card_min {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℕ) (r : α → ℝ) (S : Finset α) (hS : Finite.Optimal c r S)
    (hr : ∀ i, 0< r i) : S.card=min c (Fintype.card α) := by
  apply le_antisymm (le_min hS.1 (by simpa using Finset.card_le_univ S))
  by_cases hu : S=Finset.univ
  · simp [hu]
  · have hex : ∃ i, i∉S := by
      by_contra hh
      push Not at hh
      exact hu (Finset.eq_univ_iff_forall.mpr hh)
    obtain ⟨i,hi⟩ := hex
    rw [Finite.optimal_fills c r S hS i hi (hr i)]
    exact min_le_left _ _

lemma receipt_lower {N H : ℕ} {R Rp Rm ξ : ℝ}
    (b q : Fin N → ℝ) (row : Row H R Rp Rm)
    (hξ0 : 0≤ ξ) (hξ1 : ξ<1) (hb : ∀ i,1≤ b i) (hq : ∀ i,q i≤1)
    (hR : 0< R) (hRRm : R≤ Rm) (i : Target N H) :
    0< min (1-ξ) R ∧ min (1-ξ) R≤ receipt b q ξ row i := by
  refine ⟨lt_min (by linarith) hR,?_⟩
  cases i with
  | inl i =>
    have hf : 1-ξ≤1-ξ*q i := by nlinarith [mul_le_mul_of_nonneg_left (hq i) hξ0]
    have hn : 0≤1-ξ*q i := (show 0≤1-ξ by linarith).trans hf
    exact (min_le_left _ _).trans (hf.trans (by
      change 1-ξ*q i≤ b i*(1-ξ*q i)
      nlinarith [mul_le_mul_of_nonneg_right (hb i) hn]))
  | inr j =>
    exact (min_le_right _ _).trans (by
      simpa only [receipt,numericalBid,Sum.elim_inr] using
        numerical_private_ge b row hRRm (Sum.inr j) (by simp))

theorem high_count {N H c : ℕ} {R Rp Rm ξ : ℝ}
    (b q : Fin N → ℝ) (row : Row H R Rp Rm) (S : Finset (Target N H))
    (hS : Finite.Optimal c (receipt b q ξ row) S)
    (hξ0 : 0≤ ξ) (hξ1 : ξ<1) (hb : ∀ i,1≤ b i) (hq : ∀ i,q i≤1)
    (hR : 0< R) (hRRm : R≤ Rm) : S.card=min c (N+H) := by
  have hpos (i : Target N H) := receipt_lower b q row hξ0 hξ1 hb hq hR hRRm i
  simpa using optimal_card_min c _ S hS (fun i => (hpos i).1.trans_le (hpos i).2)

theorem high_low_union_optimal {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℕ) (r : α → ℝ) (H S T : Finset α)
    (hSsub : S⊆H) (hTdisj : Disjoint H T)
    (hS : Finite.Optimal c (fun i => if i∈H then r i else 0) S)
    (hT : Finite.Optimal (c-H.card) (fun i => if i∈H then 0 else r i) T)
    (hr : ∀ i,0≤ r i) (hHpos : ∀ i∈H,0< r i)
    (hpriority : ∀ i∈H,∀ j∉H,r j≤ r i) : Finite.Optimal c r (S∪T) := by
  have hfill (i : α) (hi : i∈H) (his : i∉S) : S.card=c :=
    Finite.optimal_fills c _ S hS i his (by simpa [hi] using hHpos i hi)
  by_cases hH : H.card≤ c
  · have he : S=H := by
      apply Finset.Subset.antisymm hSsub
      intro i hi
      by_contra hn
      have hc := hfill i hi hn
      have hlt : S.card< H.card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hSsub,fun he => hn (he.symm ▸ hi)⟩)
      omega
    rw [he]
    exact priority_union_optimal c r H T hH hTdisj hr hpriority hT
  · have hc : S.card=c := by
      obtain ⟨i,hi,his⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (show S.card< H.card by have hh:=hS.1;omega)
      exact hfill i hi his
    have ht : T=∅ := Finset.card_eq_zero.mp (by have hh:=hT.1;omega)
    rw [ht,Finset.union_empty]
    exact priority_full_optimal c r H S hSsub hc hr hpriority hS

end FCAppendix.Affine.Tail04.LowResidualCompletion

namespace FCAppendix.Affine.Tail04.Observable.Regions
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open FCAppendix.Affine.Hybrid
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon LowResidualCompletion
variable (E : Tail04.Observable.Regions) {m c : ℕ}

def lowContext (j : Fin 2) (L : LocalList m) : ClassifiedContext m :=
  ((E.context j L).1.1,
    (E.localCount L 1+(E.context j L).2.1,
      E.localCount L 1+(E.context j L).2.2))

lemma measurable_lowContext (j : Fin 2) : Measurable (E.lowContext (m:=m) j) :=
  ((E.measurable_context j).fst.fst).prodMk
    (((E.measurable_localCount 1).add (E.measurable_context j).snd.fst).prodMk
      ((E.measurable_localCount 1).add (E.measurable_context j).snd.snd))

lemma lowContext_own_count (j : Fin 2) (L : LocalList m) :
    contextUpper j (E.lowContext j L)=E.localCount L 1+E.localCount L 2 := by
  fin_cases j <;> simp [lowContext,contextUpper,Tail04.Observable.Regions.context]

lemma lowContext_list (j : Fin 2) (L : LocalList m) :
    (E.lowContext j L).1=E.roleList 0 L := rfl

lemma lowContext_common (kind : Fin m → Fin 3) (x : Realization m 2)
    (hb : E.RoleSupport kind x) (hr : TaggedLocal.ClassRoutes kind x) :
    E.lowContext 0 (observe x 0)=E.lowContext 1 (observe x 1) := by
  have hctx := E.context_common kind x hb hr
  have hc0 := (E.local_counts kind x hb hr 0).2.1
  have hc1 := (E.local_counts kind x hb hr 1).2.1
  simp only [lowContext,hctx,hc0,hc1]

def lowSelect (ξ : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (L : LocalList m) (u : unitInterval) : Finset (Fin m) :=
  NativeExactLow.select ξ hξ hξ1 c j (E.lowContext j L) u

lemma measurable_lowSelect (ξ : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1) (c : ℕ) (j : Fin 2) :
    Measurable (Function.uncurry (E.lowSelect (m:=m) ξ hξ hξ1 c j)) :=
  (NativeExactLow.measurable_select ξ hξ hξ1 c j).comp
    (((E.measurable_lowContext j).comp measurable_fst).prodMk measurable_snd)

lemma lowSelect_feasible (ξ : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (L : LocalList m) (u : unitInterval) :
    LocallyFeasible (E.roleList 0 L) (c-(E.localCount L 1+E.localCount L 2))
      (E.lowSelect ξ hξ hξ1 c j L u) := by
  simpa only [NativeContinuation.residual,E.lowContext_own_count,E.lowContext_list,lowSelect]
    using NativeExactLow.select_feasible ξ hξ hξ1 c j (E.lowContext j L) u

lemma lowSelect_present (ξ : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (L : LocalList m) (u : unitInterval) (i : Fin m)
    (hi : i∈E.lowSelect ξ hξ hξ1 c j L u) : L i≠none ∧ E.localTag (L i)=0 := by
  have hf := (E.lowSelect_feasible ξ hξ hξ1 c j L u).2 i hi
  by_cases ht : E.localTag (L i)=0
  · exact ⟨by simpa [Tail04.Observable.Regions.roleList,ht] using hf,ht⟩
  · simp [Tail04.Observable.Regions.roleList,ht] at hf

lemma lowContext_nonnegative (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    NonnegativeList (E.lowContext j L).1 := by
  intro i
  change 0≤ entryBid (E.roleList 0 L i)
  by_cases ht : E.localTag (L i)=0
  · simpa [Tail04.Observable.Regions.roleList,ht] using hL i
  · simp [Tail04.Observable.Regions.roleList,ht,entryBid]

theorem lowSelect_optimal (ξ : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) (u : unitInterval) :
    Finite.Optimal (c-(E.localCount L 1+E.localCount L 2))
      (NativeExactLow.receipt ξ hξ hξ1 c j (E.lowContext j L))
      (E.lowSelect ξ hξ hξ1 c j L u) := by
  simpa only [NativeContinuation.residual,E.lowContext_own_count,lowSelect]
    using NativeExactLow.select_numerical_optimal ξ hξ hξ1 c
      (E.lowContext j L) (E.lowContext_nonnegative j L hL) j u

end FCAppendix.Affine.Tail04.Observable.Regions
