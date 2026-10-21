import FCAppendix.Affine.Hybrid.ClassifiedCompletion

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Bayes Game Set Filter

def classifiedKind {m : ℕ} (U : ℝ) (d : UserProfile m 2) (i : Fin m) : Fin 3 :=
  if (d i).1.2.bid≤U then 0 else 2

lemma classifiedKind_boxes {m : ℕ} (U : ℝ) (d : UserProfile m 2) :
    TaggedLocal.BidBoxes (classifiedKind U d) (drawsRealization d) U U := by
  intro i
  by_cases hi : (d i).1.2.bid≤U
  · simp [classifiedKind,hi,drawsRealization]
  · simp [classifiedKind,hi,drawsRealization,lt_of_not_ge hi]

lemma classifiedKind_routes {m : ℕ} {U : ℝ} (d : UserProfile m 2)
    (hd : d∈classifiedProfiles m U) :
    TaggedLocal.ClassRoutes (classifiedKind U d) (drawsRealization d) := by
  constructor
  · intro i hi
    rcases hd i with ⟨hb,hr⟩ | ⟨hb,hr⟩
    · simp [drawsRealization,hr,firstK_full_two]
    · have : classifiedKind U d i=2 := by simp [classifiedKind,not_le.mpr hb]
      exact False.elim (hi this)
  · intro i hi
    rcases hd i with ⟨hb,hr⟩ | ⟨hb,hr⟩
    · have : classifiedKind U d i=0 := by simp [classifiedKind,hb]
      rw [this] at hi
      have hbad := congrArg Fin.val hi
      norm_num at hbad
    · change (firstK (d i).2 (d i).1.2.routeCount).card=1
      rw [hr,card_firstK _ _ (by omega)]

def broadcastPart {m : ℕ} (U : ℝ) : LocalList m → LocalList m := TaggedLocal.lowList U U

lemma measurable_broadcastPart {m : ℕ} (U : ℝ) : Measurable (broadcastPart (m:=m) U) :=
  TaggedLocal.measurable_lowList U U

lemma broadcastPart_observe {m : ℕ} {U : ℝ} (d : UserProfile m 2)
    (hd : d∈classifiedProfiles m U) (j : Fin 2) :
    broadcastPart U (observe (drawsRealization d) j)=
      fun i=>if (d i).1.2.bid≤U then some (d i).1.2.bid else none := by
  have h := TaggedLocal.lowList_observe (classifiedKind U d) (drawsRealization d)
    (le_refl U) (classifiedKind_boxes U d) (classifiedKind_routes d hd) j
  change TaggedLocal.lowList U U (observe (drawsRealization d) j)=_
  rw [h]
  funext i
  by_cases hi : (d i).1.2.bid≤U <;> simp [classifiedKind,hi,drawsRealization]

lemma broadcastPart_common {m : ℕ} {U : ℝ} (d : UserProfile m 2)
    (hd : d∈classifiedProfiles m U) (j l : Fin 2) :
    broadcastPart U (observe (drawsRealization d) j)=
      broadcastPart U (observe (drawsRealization d) l) := by
  rw [broadcastPart_observe d hd j,broadcastPart_observe d hd l]

abbrev ClassifiedContext (m : ℕ) := LocalList m × (ℕ × ℕ)

def observedContext {m : ℕ} (U : ℝ) (j : Fin 2) (L : LocalList m) : ClassifiedContext m :=
  let broadcasts := TaggedLocal.localCount U U L 0
  let here := TaggedLocal.localCount U U L 2
  let there := m-broadcasts-here
  (broadcastPart U L,if j=0 then (here,there) else (there,here))

lemma measurable_observedContext {m : ℕ} (U : ℝ) (j : Fin 2) :
    Measurable (observedContext (m:=m) U j) := by
  have hb := TaggedLocal.measurable_localCount (m:=m) U U 0
  have hh := TaggedLocal.measurable_localCount (m:=m) U U 2
  have ht : Measurable (fun L : LocalList m=>m-TaggedLocal.localCount U U L 0-
      TaggedLocal.localCount U U L 2) :=
    (measurable_of_countable (fun BH : ℕ×ℕ=>m-BH.1-BH.2)).comp (hb.prodMk hh)
  unfold observedContext
  split_ifs
  · exact (measurable_broadcastPart U).prodMk (hh.prodMk ht)
  · exact (measurable_broadcastPart U).prodMk (ht.prodMk hh)

def actualContext {m : ℕ} (U : ℝ) (d : UserProfile m 2) : ClassifiedContext m :=
  (broadcastPart U (observe (drawsRealization d) 0),
    TaggedLocal.upperAt (classifiedKind U d) (drawsRealization d) 0,
    TaggedLocal.upperAt (classifiedKind U d) (drawsRealization d) 1)

theorem observedContext_eq_actual {m : ℕ} {U : ℝ} (d : UserProfile m 2)
    (hd : d∈classifiedProfiles m U) (j : Fin 2) :
    observedContext U j (observe (drawsRealization d) j)=actualContext U d := by
  have hcounts := TaggedLocal.local_counts_correct (classifiedKind U d) (drawsRealization d)
    (le_refl U) (classifiedKind_boxes U d) (classifiedKind_routes d hd)
  have hpartition := TaggedLocal.counts_partition (classifiedKind U d) (drawsRealization d)
    (classifiedKind_routes d hd)
  have hactive : TaggedLocal.countKind (classifiedKind U d) 1=0 := by
    unfold TaggedLocal.countKind
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : (d i).1.2.bid≤U <;> simp [classifiedKind,hi]
  rw [hactive] at hpartition
  have ht0 : m-TaggedLocal.countKind (classifiedKind U d) 0-
      TaggedLocal.upperAt (classifiedKind U d) (drawsRealization d) 0=
      TaggedLocal.upperAt (classifiedKind U d) (drawsRealization d) 1 := by omega
  have ht1 : m-TaggedLocal.countKind (classifiedKind U d) 0-
      TaggedLocal.upperAt (classifiedKind U d) (drawsRealization d) 1=
      TaggedLocal.upperAt (classifiedKind U d) (drawsRealization d) 0 := by omega
  have hcommon := broadcastPart_common d hd j 0
  unfold observedContext actualContext
  rw [hcommon,(hcounts j).1,(hcounts j).2.2]
  fin_cases j
  · simp [ht0]
  · simp [ht1]

theorem classifiedPosterior_context {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hU : 0≤U) (hR : U<R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈classifiedProfiles m U)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) (l : Fin 2) :
    ∀ᵐd ∂(classifiedPosterior Γ (R:=R) hfull).posterior j L,
      observedContext U l (observe (drawsRealization d) l)=observedContext U j L := by
  filter_upwards [classifiedPosterior_support Γ hU hR hfull j L hL] with d hd
  rw [observedContext_eq_actual d hd.2 l,←observedContext_eq_actual d hd.2 j,hd.1]

end FCAppendix.Affine.Hybrid
