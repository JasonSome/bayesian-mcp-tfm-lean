import FCAppendix.Affine.UniformFinite.Late.NativeExceptionalLaw
import FCAppendix.Affine.UniformFinite.NativeOptimality

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.NativeExceptional
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05
open scoped BigOperators
variable {M : ℕ} [NeZero M]

def rawBids (X : Hybrid.ClassifiedContext M) : Fin M → ℝ := fun a => entryBid (X.1 a)

omit [NeZero M] in
theorem measurable_rawBids : Measurable (rawBids (M:=M)) := by
  apply measurable_pi_lambda
  intro a
  exact measurable_entryBid.comp ((measurable_pi_apply a).comp measurable_fst)

omit [NeZero M] in
theorem lowerBids_raw (X : Hybrid.ClassifiedContext M) :
    Source.lowerBids (NativeContext.decode X) (rawBids X) = rawBids X := by
  funext a
  cases ha : X.1 a with
  | none => simp [Source.lowerBids,NativeContext.decode,NativeContext.present,rawBids,ha,entryBid]
  | some b => simp [Source.lowerBids,NativeContext.decode,NativeContext.present,rawBids,ha]

def Ordinary (i : Row) (X : Hybrid.ClassifiedContext M) : Prop :=
  ∀ a, rawBids X a ≤ cap i

omit [NeZero M] in
theorem measurableSet_ordinary (i : Row) : MeasurableSet (Ordinary (M:=M) i) := by
  convert! MeasurableSet.iInter (fun a : Fin M=>measurableSet_le
    ((measurable_pi_apply a).comp measurable_rawBids)
      (measurable_const : Measurable (fun _ : Hybrid.ClassifiedContext M=>cap i))) using 1
  ext X
  change Ordinary i X↔_
  simp [Ordinary]

def exceptions (i : Row) (X : Hybrid.ClassifiedContext M) : Finset (Fin M) :=
  Hybrid.upperSet (cap i) X.1

omit [NeZero M] in
theorem measurable_exceptions (i : Row) : Measurable (exceptions (M:=M) i) :=
  (Hybrid.measurable_upperSet (cap i)).comp measurable_fst

omit [NeZero M] in
theorem mem_exceptions (i : Row) (X : Hybrid.ClassifiedContext M) (a : Fin M) :
    a∈exceptions i X ↔ X.1 a ≠ none ∧ cap i < rawBids X a := by
  cases ha : X.1 a with
  | none => simp [exceptions,Hybrid.upperSet,TaggedLocal.tag,ha,rawBids,entryBid]
  | some b =>
    by_cases hb : b≤ cap i
    · simp [exceptions,Hybrid.upperSet,TaggedLocal.tag,ha,rawBids,entryBid,hb,not_lt.mpr hb]
    · simp [exceptions,Hybrid.upperSet,TaggedLocal.tag,ha,rawBids,entryBid,hb,lt_of_not_ge hb]

def first (S : Finset (Fin M)) : Fin M := if h : S.Nonempty then S.min' h else 0

theorem first_mem (S : Finset (Fin M)) (h : S.Nonempty) : first S∈S := by
  simp only [first,dif_pos h]
  exact Finset.min'_mem S h

def exceptionalId (i : Row) (X : Hybrid.ClassifiedContext M) : Fin M := first (exceptions i X)

theorem measurable_exceptionalId (i : Row) : Measurable (exceptionalId (M:=M) i) :=
  (measurable_of_countable first).comp (measurable_exceptions i)

def Ready (i : Row) (X : Hybrid.ClassifiedContext M) : Prop :=
  NativeContext.Valid X ∧ NonnegativeList X.1 ∧ (exceptions i X).card=1

omit [NeZero M] in
theorem measurableSet_nonnegative : MeasurableSet (fun X : Hybrid.ClassifiedContext M =>
    NonnegativeList X.1) := by
  convert! MeasurableSet.iInter (fun a : Fin M=>measurableSet_le
    (measurable_const : Measurable (fun _ : Hybrid.ClassifiedContext M=>(0:ℝ)))
    ((measurable_pi_apply a).comp measurable_rawBids)) using 1
  ext X
  change NonnegativeList X.1↔_
  simp [NonnegativeList,rawBids]

omit [NeZero M] in
theorem measurableSet_ready (i : Row) : MeasurableSet (Ready (M:=M) i) :=
  NativeContext.measurableSet_valid.inter (measurableSet_nonnegative.inter
    (measurableSet_eq_fun ((measurable_of_countable Finset.card).comp (measurable_exceptions i))
      measurable_const))

theorem ready_good (i : Row) (X : Hybrid.ClassifiedContext M) (h : Ready i X) :
    NativeExceptionalRow.Good i (NativeContext.decode X) (exceptionalId i X) (rawBids X) := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h.2.2
  have hmem : exceptionalId i X∈exceptions i X :=
    first_mem _ (Finset.card_pos.mp (by rw [h.2.2];norm_num))
  have heq : exceptionalId i X=a := by simpa only [ha,Finset.mem_singleton] using hmem
  refine ⟨?_,fun j _ => h.2.1 j,?_⟩
  · have hp := (mem_exceptions i X _).mp hmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.1⟩
  · intro j hj hja
    by_contra hnot
    have hjmem : j∈exceptions i X := (mem_exceptions i X j).mpr
      ⟨(Finset.mem_filter.mp hj).2,lt_of_not_ge hnot⟩
    have hjeq : j=a := by simpa only [ha,Finset.mem_singleton] using hjmem
    exact hja (hjeq.trans heq.symm)

theorem exceptionalId_eq (i : Row) (X : Hybrid.ClassifiedContext M) (a : Fin M)
    (ha : a∈exceptions i X) (hcard : (exceptions i X).card=1) : exceptionalId i X=a := by
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hcard
  have hmem : exceptionalId i X∈exceptions i X :=
    first_mem _ (Finset.card_pos.mp (by omega))
  have he : exceptionalId i X=b := by simpa only [hb,Finset.mem_singleton] using hmem
  have he' : a=b := by simpa only [hb,Finset.mem_singleton] using ha
  exact he.trans he'.symm

def exceptionalSelect (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) (s : unitInterval) : Finset (Fin M) :=
  NativeExceptionalRow.select i G (NativeContext.decode X) (exceptionalId i X) j (rawBids X)
    (NativeContext.common i μseed X) s

theorem measurable_exceptionalSelect (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) : Measurable (Function.uncurry (exceptionalSelect (M:=M) i G μseed j)) := by
  have hr (k : Source.CountRow M × Fin M) :
      Measurable (fun x : Hybrid.ClassifiedContext M × unitInterval =>
        NativeExceptionalRow.select i G k.1 k.2 j (rawBids x.1)
          (NativeContext.common i μseed x.1) x.2) := by
    convert! (NativeExceptionalRow.select_measurable i G k.1 k.2 j).comp
      (((measurable_rawBids.comp measurable_fst).prodMk
        ((NativeContext.measurable_common i μseed).comp measurable_fst)).prodMk measurable_snd) using 1
  have hm : Measurable (fun p : (Source.CountRow M×Fin M)×
      (Hybrid.ClassifiedContext M×unitInterval)=>
      NativeExceptionalRow.select i G p.1.1 p.1.2 j (rawBids p.2.1)
        (NativeContext.common i μseed p.2.1) p.2.2) :=
    measurable_from_prod_countable_right hr
  convert! hm.comp
    (((NativeContext.measurable_decode.comp measurable_fst).prodMk
      ((measurable_exceptionalId i).comp measurable_fst)).prodMk measurable_id) using 1

def select (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) (s : unitInterval) : Finset (Fin M) :=
  if Ordinary i X then NativeContext.select i G μseed j X s
  else if Ready i X then exceptionalSelect i G μseed j X s
  else Hybrid.NativeContinuation.select (xi i) (xi_range i).1 (xi_range i).2
    (Uniform07.capacity M) j X s

theorem select_on_path (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (X : Hybrid.ClassifiedContext M) (hX : Ordinary i X) (j : Fin 2) (s : unitInterval) :
    select i G μseed j X s = NativeContext.select i G μseed j X s := by
  simp only [select,if_pos hX]

theorem select_exceptional (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (X : Hybrid.ClassifiedContext M) (hX : Ready i X) (j : Fin 2) (s : unitInterval) :
    select i G μseed j X s = exceptionalSelect i G μseed j X s := by
  have hn : ¬ Ordinary i X := by
    intro hO
    have ha := first_mem (exceptions i X) (Finset.card_pos.mp (by have := hX.2.2; omega))
    have hh := (mem_exceptions i X _).mp ha
    exact (not_lt.mpr (hO _)) hh.2
  simp only [select,if_neg hn,if_pos hX]

theorem measurable_select (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (select (M:=M) i G μseed j)) := by
  exact Measurable.ite ((measurableSet_ordinary i).preimage measurable_fst)
    (NativeContext.measurable_select i G μseed j)
    (Measurable.ite ((measurableSet_ready i).preimage measurable_fst)
      (measurable_exceptionalSelect i G μseed j)
      (Hybrid.NativeContinuation.measurable_select (xi i) (xi_range i).1 (xi_range i).2
        (Uniform07.capacity M) j))

theorem select_feasible (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) (s : unitInterval) :
    LocallyFeasible X.1 (Uniform07.capacity M-Hybrid.contextUpper j X) (select i G μseed j X s) := by
  by_cases hO : Ordinary i X
  · rw [select,if_pos hO]
    exact NativeContext.select_feasible i G μseed j X s
  · by_cases hX : Ready i X
    · rw [select,if_neg hO,if_pos hX]
      have h := NativeExceptionalRow.select_feasible i G (NativeContext.decode X)
        (exceptionalId i X) (rawBids X) (ready_good i X hX) j (NativeContext.common i μseed X) s
      refine ⟨h.1.trans ?_,?_⟩
      · change min (NativeContext.present X.1).card
          (Uniform07.capacity M-Source.upperCount (NativeContext.decode X) j) ≤ _
        rw [NativeContext.decode_upper X hX.1 j]
        exact min_le_right _ _
      · intro a ha
        exact (Finset.mem_filter.mp (h.2 ha)).2
    · rw [select,if_neg hO,if_neg hX]
      exact Hybrid.NativeContinuation.select_feasible (xi i) (xi_range i).1 (xi_range i).2
        (Uniform07.capacity M) j X s

def contextPolicy (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ) :
    Hybrid.ContextPolicy M (Uniform07.capacity M) unitInterval where
  select := select i G μseed
  measurable := measurable_select i G μseed
  feasible := select_feasible i G μseed

def acceptance (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) (a : Fin M) : ℝ :=
  ∫ s : unitInterval, if a∈select i G μseed j X s then (1:ℝ) else 0

def receipt (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) (a : Fin M) : ℝ :=
  rawBids X a*(1-xi i*acceptance i G μseed (Hybrid.otherProposer j) X a)

theorem acceptance_ordinary (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (X : Hybrid.ClassifiedContext M) (hX : NativeContext.Valid X) (hO : Ordinary i X)
    (j : Fin 2) (a : Fin M) :
    acceptance i G μseed j X a = NativeRow.acceptance i (NativeContext.decode X) j
      (NativeContext.state i G X) (NativeContext.common i μseed X) a := by
  simp only [acceptance,select,if_pos hO,NativeContext.select,if_pos hX,
    NativeContext.sourceSelect,NativeRow.acceptance]

theorem acceptance_exceptional (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (X : Hybrid.ClassifiedContext M) (hX : Ready i X) (j : Fin 2) (a : Fin M) :
    acceptance i G μseed j X a = NativeExceptionalRow.acceptance i G (NativeContext.decode X)
      (exceptionalId i X) j (rawBids X) (NativeContext.common i μseed X) a := by
  simp only [acceptance,select_exceptional i G μseed X hX,
    exceptionalSelect,NativeExceptionalRow.acceptance]

theorem lower_optimal (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (X : Hybrid.ClassifiedContext M) (hX : NativeContext.Valid X)
    (h0 : NonnegativeList X.1) (j : Fin 2) (s : unitInterval) :
    Finite.Optimal (Uniform07.capacity M-Hybrid.contextUpper j X)
      (receipt i G μseed j X) (select i G μseed j X s) := by
  have hc : Source.residual (NativeContext.decode X) j =
      min (NativeContext.present X.1).card (Uniform07.capacity M-Hybrid.contextUpper j X) := by
    unfold Source.residual
    rw [NativeContext.decode_upper X hX j]
    rfl
  have hz (a : Fin M) (ha : a∉NativeContext.present X.1) : receipt i G μseed j X a=0 := by
    have hn : X.1 a=none := by simpa only [NativeContext.present,Finset.mem_filter,
      Finset.mem_univ,true_and,not_not] using ha
    simp [receipt,rawBids,hn,entryBid]
  by_cases hO : Ordinary i X
  · have hs := NativeRow.select_optimal i (NativeContext.decode X) j
      (NativeContext.state i G X) (NativeContext.common i μseed X) s
    have hr : (fun a => Source.lowerBids (NativeContext.decode X)
        (SourceContinuity.bids i (NativeContext.state i G X)) a *
        (1-xi i*NativeRow.acceptance i (NativeContext.decode X) (Hybrid.otherProposer j)
          (NativeContext.state i G X) (NativeContext.common i μseed X) a)) = receipt i G μseed j X := by
      rw [NativeContext.state_lowerBids i G X h0 hO]
      funext a
      simp only [receipt,rawBids,acceptance_ordinary i G μseed X hX hO]
    rw [hc,hr] at hs
    have ht := NativeContext.extend_budget (NativeContext.present X.1) _
      (Uniform07.capacity M-Hybrid.contextUpper j X) _ hz hs
    simpa only [select,if_pos hO,NativeContext.select,if_pos hX,NativeContext.sourceSelect] using ht
  · by_cases hR : Ready i X
    · have hs := NativeExceptionalRow.select_optimal i G (NativeContext.decode X)
        (exceptionalId i X) (rawBids X) (ready_good i X hR) j (NativeContext.common i μseed X) s
      have hr : (fun a => Source.lowerBids (NativeContext.decode X) (rawBids X) a *
          (1-xi i*NativeExceptionalRow.acceptance i G (NativeContext.decode X)
            (exceptionalId i X) (Hybrid.otherProposer j) (rawBids X)
              (NativeContext.common i μseed X) a)) = receipt i G μseed j X := by
        rw [lowerBids_raw]
        funext a
        simp only [receipt,acceptance_exceptional i G μseed X hR]
      rw [hc,hr] at hs
      have ht := NativeContext.extend_budget (NativeContext.present X.1) _
        (Uniform07.capacity M-Hybrid.contextUpper j X) _ hz hs
      simpa only [select,if_neg hO,if_pos hR,exceptionalSelect] using ht
    · have hs := Hybrid.NativeContinuation.select_numerical_optimal
        (xi i) (xi_range i).1 (xi_range i).2 (Uniform07.capacity M) X h0 j s
      have hacc (k : Fin 2) (a : Fin M) : acceptance i G μseed k X a=
          Hybrid.NativeContinuation.acceptance (xi i) (xi_range i).1 (xi_range i).2
            (Uniform07.capacity M) k X a := by
        unfold acceptance Hybrid.NativeContinuation.acceptance
        simp_rw [select,if_neg hO,if_neg hR]
      have hr : receipt i G μseed j X=
          Hybrid.NativeContinuation.receipt (xi i) (xi_range i).1 (xi_range i).2
            (Uniform07.capacity M) j X := by
        funext a
        unfold receipt Hybrid.NativeContinuation.receipt
        rw [hacc]
        rfl
      rw [hr]
      simpa only [select,if_neg hO,if_neg hR,Hybrid.NativeContinuation.residual] using hs

theorem lowerContextReceipt_eq (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) (hseed : Γ.seedLaw=volume)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) :
    Hybrid.lowerContextReceipt Γ (contextPolicy i G μseed) (xi i) j X = receipt i G μseed j X := by
  funext a
  simp only [Hybrid.lowerContextReceipt,Hybrid.contextAcceptance,contextPolicy,
    hseed,receipt,acceptance,rawBids]
  rfl

theorem context_optimal (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) (hseed : Γ.seedLaw=volume)
    (X : Hybrid.ClassifiedContext M) (hX : NativeContext.Valid X)
    (h0 : NonnegativeList X.1) (j : Fin 2) (s : unitInterval) :
    Finite.Optimal (Uniform07.capacity M-Hybrid.contextUpper j X)
      (Hybrid.lowerContextReceipt Γ (contextPolicy i G μseed) (xi i) j X)
      ((contextPolicy i G μseed).select j X s) := by
  rw [lowerContextReceipt_eq i G μseed Γ hseed]
  exact lower_optimal i G μseed X hX h0 j s

theorem unique_exception_select (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (X : Hybrid.ClassifiedContext M) (a : Fin M) (hX : NativeContext.Valid X)
    (h0 : NonnegativeList X.1) (ha : a∈exceptions i X) (hcard : (exceptions i X).card=1)
    (j : Fin 2) (s : unitInterval) :
    select i G μseed j X s = NativeExceptionalRow.select i G (NativeContext.decode X) a j
      (rawBids X) (NativeContext.common i μseed X) s := by
  rw [select_exceptional i G μseed X ⟨hX,h0,hcard⟩,exceptionalSelect,
    exceptionalId_eq i X a ha hcard]

end FCAppendix.Affine.UniformFinite.Late.NativeExceptional
