import FCAppendix.Affine.UniformFinite.NativeRowLaw
import FCAppendix.Affine.UniformFinite.CountRowCode

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05 SourceContinuity
open scoped BigOperators

namespace NativeContext
variable {M : ℕ}

def present (L : LocalList M) : Finset (Fin M) := Finset.univ.filter (fun a => L a ≠ none)

theorem measurable_present : Measurable (present (M:=M)) := by
  apply measurable_to_countable'
  intro S
  have he : present ⁻¹' {S} = ⋂ a : Fin M, {L : LocalList M | (a∈S ↔ L a ≠ none)} := by
    ext L
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_setOf_eq, present]
    exact ⟨fun h a => by rw [← h]; simp,
      fun h => Finset.ext (fun a => by simpa using (h a).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro a
  have hEq : MeasurableSet {L : LocalList M | L a=none} :=
    (measurableSet_singleton (none : Option ℝ)).preimage (measurable_pi_apply a)
  by_cases ha : a∈S
  · simp only [ha,true_iff]
    convert! hEq.compl using 1
  · simpa only [ha, false_iff, not_not] using
      hEq

theorem present_card_le (L : LocalList M) : (present L).card ≤ M := by
  simpa using Finset.card_le_univ (present L)

def Valid (X : Hybrid.ClassifiedContext M) : Prop :=
  (present X.1).card+X.2.1+X.2.2=M

theorem measurableSet_valid : MeasurableSet (Valid (M:=M)) := by
  exact measurableSet_eq_fun
    (((measurable_of_countable Finset.card).comp (measurable_present.comp measurable_fst)).add
      measurable_snd.fst |>.add measurable_snd.snd) measurable_const

def decode (X : Hybrid.ClassifiedContext M) : Source.CountRow M where
  lower := present X.1
  upper0 := min X.2.1 (M-(present X.1).card)
  upper1 := M-(present X.1).card-min X.2.1 (M-(present X.1).card)
  partition := by
    have hp := present_card_le X.1
    have hm := min_le_right X.2.1 (M-(present X.1).card)
    omega

theorem decode_upper (X : Hybrid.ClassifiedContext M) (hX : Valid X) (j : Fin 2) :
    Source.upperCount (decode X) j = Hybrid.contextUpper j X := by
  have h0 : X.2.1 ≤ M-(present X.1).card := by dsimp [Valid] at hX; omega
  have h1 : M-(present X.1).card-X.2.1 = X.2.2 := by dsimp [Valid] at hX; omega
  fin_cases j <;> simp [Source.upperCount, Hybrid.contextUpper, decode, min_eq_left h0, h1]

theorem countRow_eq_iff (P Q : Source.CountRow M) :
    P=Q ↔ P.lower=Q.lower ∧ P.upper0=Q.upper0 ∧ P.upper1=Q.upper1 := by
  constructor
  · rintro rfl
    exact ⟨rfl,rfl,rfl⟩
  · rcases P with ⟨p,p0,p1,hp⟩
    rcases Q with ⟨q,q0,q1,hq⟩
    rintro ⟨hL,h0,h1⟩
    cases hL
    cases h0
    cases h1
    rfl

theorem measurable_decode : Measurable (decode (M:=M)) := by
  have hl := measurable_present.comp (measurable_fst : Measurable (Prod.fst : Hybrid.ClassifiedContext M → LocalList M))
  have hn : Measurable (fun X : Hybrid.ClassifiedContext M => M-(present X.1).card) :=
    measurable_const.sub ((measurable_of_countable Finset.card).comp hl)
  have h0 := measurable_snd.fst.min hn
  have h1 := hn.sub h0
  apply measurable_to_countable'
  intro row
  have he : decode ⁻¹' {row} = {X | present X.1=row.lower} ∩
      ({X | min X.2.1 (M-(present X.1).card)=row.upper0} ∩
        {X | M-(present X.1).card-min X.2.1 (M-(present X.1).card)=row.upper1}) := by
    ext X
    simp only [mem_preimage, mem_singleton_iff, countRow_eq_iff, decode, mem_inter_iff, mem_setOf_eq]
  rw [he]
  exact (measurableSet_eq_fun hl measurable_const).inter
    ((measurableSet_eq_fun h0 measurable_const).inter (measurableSet_eq_fun h1 measurable_const))

def cappedList (i : Row) (L : LocalList M) : Fin M → Bid i := fun a =>
  ⟨min (cap i) (max 0 (entryBid (L a))),
    le_min (cap_pos i).le (le_max_left _ _), min_le_left _ _⟩

theorem measurable_cappedList (i : Row) : Measurable (cappedList (M:=M) i) := by
  apply measurable_pi_lambda
  intro a
  apply Measurable.subtype_mk
  exact measurable_const.min (measurable_const.max (measurable_entryBid.comp (measurable_pi_apply a)))

def state (i : Row) (G : RestrictedLaw i) (X : Hybrid.ClassifiedContext M) : State i M :=
  (G,cappedList i X.1)

theorem measurable_state (i : Row) (G : RestrictedLaw i) : Measurable (state (M:=M) i G) :=
  (SourceContinuity.measurable_fixedLawState i G).comp
    ((measurable_cappedList i).comp measurable_fst)

theorem state_lowerBids (i : Row) (G : RestrictedLaw i) (X : Hybrid.ClassifiedContext M)
    (h0 : NonnegativeList X.1) (hU : ∀ a, entryBid (X.1 a) ≤ cap i) :
    Source.lowerBids (decode X) (bids i (state i G X)) = fun a => entryBid (X.1 a) := by
  funext a
  by_cases ha : X.1 a = none
  · simp [decode, present, Source.lowerBids, ha, entryBid]
  · simp [Source.lowerBids, decode, present, ha, bids, state, cappedList,
      max_eq_right (h0 a), min_eq_right (hU a)]

def common (i : Row) (μseed : Measure ℝ) (X : Hybrid.ClassifiedContext M) : unitInterval :=
  (Hybrid.observedLowSeed (t i/2) (cap i) μseed X.1).getD 0

theorem measurable_common (i : Row) (μseed : Measure ℝ) : Measurable (common (M:=M) i μseed) := by
  have hget : Measurable (fun x : Option unitInterval => x.getD 0) := by
    intro S hS
    change MeasurableSet S
    exact hS
  exact hget.comp ((Hybrid.measurable_observedLowSeed (t i/2) (cap i) μseed).comp measurable_fst)

variable [NeZero M]

def sourceSelect (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) (s : unitInterval) : Finset (Fin M) :=
  NativeRow.select i (decode X) j (state i G X) (common i μseed X) s

theorem measurable_sourceSelect (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (sourceSelect (M:=M) i G μseed j)) := by
  have hr (row : Source.CountRow M) : Measurable (fun x : Hybrid.ClassifiedContext M × unitInterval =>
      NativeRow.select i row j (state i G x.1) (common i μseed x.1) x.2) := by
    convert! (NativeRow.select_measurable i row j).comp
      ((((measurable_state i G).comp measurable_fst).prodMk
        ((measurable_common i μseed).comp measurable_fst)).prodMk measurable_snd) using 1
  have hboth : Measurable (fun x : Source.CountRow M×(Hybrid.ClassifiedContext M×unitInterval)=>
      NativeRow.select i x.1 j (state i G x.2.1) (common i μseed x.2.1) x.2.2) :=
    measurable_from_prod_countable_right hr
  convert! hboth.comp
    ((measurable_decode.comp measurable_fst).prodMk measurable_id) using 1

def select (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) (s : unitInterval) : Finset (Fin M) :=
  if Valid X then sourceSelect i G μseed j X s
  else Hybrid.NativeContinuation.select (xi i) (xi_range i).1 (xi_range i).2
    (Uniform07.capacity M) j X s

theorem measurable_select (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (select (M:=M) i G μseed j)) :=
  Measurable.ite (measurableSet_valid.preimage measurable_fst)
    (measurable_sourceSelect i G μseed j)
    (Hybrid.NativeContinuation.measurable_select (xi i) (xi_range i).1 (xi_range i).2
      (Uniform07.capacity M) j)

theorem select_feasible (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (j : Fin 2) (X : Hybrid.ClassifiedContext M) (s : unitInterval) :
    LocallyFeasible X.1 (Uniform07.capacity M-Hybrid.contextUpper j X) (select i G μseed j X s) := by
  by_cases hX : Valid X
  · rw [select, if_pos hX]
    have h := NativeRow.select_feasible i (decode X) j (state i G X) (common i μseed X) s
    refine ⟨h.1.trans ?_,?_⟩
    · change min (present X.1).card (Uniform07.capacity M-Source.upperCount (decode X) j) ≤ _
      rw [decode_upper X hX j]
      exact min_le_right _ _
    · intro a ha
      exact (Finset.mem_filter.mp (h.2 ha)).2
  · rw [select, if_neg hX]
    exact Hybrid.NativeContinuation.select_feasible (xi i) (xi_range i).1 (xi_range i).2
      (Uniform07.capacity M) j X s

def contextPolicy (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ) :
    Hybrid.ContextPolicy M (Uniform07.capacity M) unitInterval where
  select := select i G μseed
  measurable := measurable_select i G μseed
  feasible := select_feasible i G μseed

omit [NeZero M] in
theorem present_broadcastPart (U : ℝ) (L : LocalList M) :
    present (Hybrid.broadcastPart U L) = Finset.univ.filter (fun a => TaggedLocal.tag U U (L a)=0) := by
  ext a
  cases hL : L a with
  | none => simp [present, Hybrid.broadcastPart, TaggedLocal.lowList, TaggedLocal.tag, hL]
  | some b =>
    by_cases hb : b≤ U <;> simp [present, Hybrid.broadcastPart, TaggedLocal.lowList, TaggedLocal.tag, hL, hb]

omit [NeZero M] in
theorem present_broadcastPart_card (U : ℝ) (L : LocalList M) :
    (present (Hybrid.broadcastPart U L)).card = TaggedLocal.localCount U U L 0 := by
  rw [present_broadcastPart]
  simp only [TaggedLocal.localCount, Finset.card_eq_sum_ones, Finset.sum_filter]

omit [NeZero M] in
theorem observed_valid (U : ℝ) (j : Fin 2) (L : LocalList M) :
    Valid (Hybrid.observedContext U j L) := by
  have hd : Disjoint (present (Hybrid.broadcastPart U L)) (Hybrid.upperSet U L) := by
    apply Finset.disjoint_left.mpr
    intro a ha hl
    rw [present_broadcastPart] at ha
    have h0 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hl).2
    rw [h0] at h2
    exact (by decide : (0:Fin 4)≠2) h2
  have hc : (present (Hybrid.broadcastPart U L)).card+(Hybrid.upperSet U L).card ≤ M := by
    rw [← Finset.card_union_of_disjoint hd]
    simpa using Finset.card_le_univ (present (Hybrid.broadcastPart U L) ∪ Hybrid.upperSet U L)
  rw [present_broadcastPart_card, Hybrid.upperSet_card] at hc
  fin_cases j <;> simp [Valid,Hybrid.observedContext,present_broadcastPart_card] <;> omega

omit [NeZero M] in
theorem observed_bid_box (i : Row) (j : Fin 2) (L : LocalList M) (hL : NonnegativeList L) :
    NonnegativeList (Hybrid.observedContext (cap i) j L).1 ∧
      ∀ a, entryBid ((Hybrid.observedContext (cap i) j L).1 a) ≤ cap i := by
  refine ⟨Hybrid.NativeContinuation.nonnegative_observedContext (cap i) j L hL,?_⟩
  intro a
  change entryBid (Hybrid.broadcastPart (cap i) L a) ≤ cap i
  cases he : L a with
  | none => simp [Hybrid.broadcastPart, TaggedLocal.lowList, TaggedLocal.tag, he, entryBid, (cap_pos i).le]
  | some b =>
    by_cases hb : b≤ cap i
    · simp [Hybrid.broadcastPart, TaggedLocal.lowList, TaggedLocal.tag, he, hb, entryBid]
    · simp [Hybrid.broadcastPart, TaggedLocal.lowList, TaggedLocal.tag, he, hb, entryBid, (cap_pos i).le]

end NativeContext
end FCAppendix.Affine.UniformFinite
