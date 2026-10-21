import FCAppendix.Affine.Hybrid.ClassifiedPolicy

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical
open scoped BigOperators

variable {m c : ℕ}

def closedTag (R : ℝ) : Option ℝ → Fin 4
  | none => 3
  | some b => if b < R then 0 else 2

lemma measurable_closedTag (R : ℝ) : Measurable (closedTag R) := by
  intro S hS
  change MeasurableSet ((fun b : ℝ => if b < R then (0 : Fin 4) else 2) ⁻¹' S)
  exact (Measurable.ite measurableSet_Iio measurable_const measurable_const) hS

@[simp] lemma closedTag_at_floor (R : ℝ) : closedTag R (some R) = 2 := by
  simp [closedTag]

lemma closedTag_lower_iff {R b : ℝ} : closedTag R (some b) = 0 ↔ b < R := by
  by_cases h : b < R <;> simp [closedTag, h]

lemma closedTag_upper_iff {R b : ℝ} : closedTag R (some b) = 2 ↔ R ≤ b := by
  by_cases h : b < R
  · simp [closedTag, h, not_le.mpr h]
  · simp [closedTag, h, le_of_not_gt h]

def lowerPart (R : ℝ) (L : LocalList m) : LocalList m :=
  fun i => if closedTag R (L i) = 0 then L i else none

def upperPart (R : ℝ) (L : LocalList m) : LocalList m :=
  fun i => if closedTag R (L i) = 2 then L i else none

def upperSet (R : ℝ) (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => closedTag R (L i) = 2)

def localCount (R : ℝ) (L : LocalList m) (k : Fin 4) : ℕ :=
  ∑ i : Fin m, if closedTag R (L i) = k then 1 else 0

lemma measurable_lowerPart (R : ℝ) : Measurable (lowerPart (m := m) R) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_closedTag R).comp (measurable_pi_apply i))
      measurable_const) (measurable_pi_apply i) measurable_const

lemma measurable_upperPart (R : ℝ) : Measurable (upperPart (m := m) R) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_closedTag R).comp (measurable_pi_apply i))
      measurable_const) (measurable_pi_apply i) measurable_const

lemma measurable_upperSet (R : ℝ) : Measurable (upperSet (m := m) R) := by
  apply measurable_to_countable'
  intro S
  have he : (upperSet R) ⁻¹' {S} =
      ⋂ i : Fin m, {L : LocalList m | (i ∈ S ↔ closedTag R (L i) = 2)} := by
    ext L
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_setOf_eq, upperSet]
    exact ⟨fun h i => by rw [← h]; simp,
      fun h => Finset.ext (fun i => by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (h i).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ S
  · simp only [hi, true_iff]
    exact measurableSet_eq_fun ((measurable_closedTag R).comp (measurable_pi_apply i))
      measurable_const
  · simp only [hi, false_iff]
    exact (measurableSet_eq_fun ((measurable_closedTag R).comp (measurable_pi_apply i))
      measurable_const).compl

lemma measurable_localCount (R : ℝ) (k : Fin 4) :
    Measurable (fun L : LocalList m => localCount R L k) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_closedTag R).comp (measurable_pi_apply i))
      measurable_const) measurable_const measurable_const

lemma lowerPart_some {R b : ℝ} (L : LocalList m) (i : Fin m)
    (hi : L i = some b) (hb : b < R) : lowerPart R L i = some b := by
  simp [lowerPart, closedTag, hi, hb]

lemma lowerPart_present (R : ℝ) (L : LocalList m) (i : Fin m)
    (hi : lowerPart R L i ≠ none) : L i ≠ none ∧ i ∉ upperSet R L := by
  unfold lowerPart at hi
  by_cases ht : closedTag R (L i) = 0
  · simp only [if_pos ht] at hi
    exact ⟨hi, by simp [upperSet, ht]⟩
  · simp only [if_neg ht] at hi
    exact False.elim (hi rfl)

lemma upperSet_present (R : ℝ) (L : LocalList m) (i : Fin m)
    (hi : i ∈ upperSet R L) : L i ≠ none := by
  have ht := (Finset.mem_filter.mp hi).2
  intro hn
  simp [hn, closedTag] at ht

lemma upperSet_iff_bid {R b : ℝ} (L : LocalList m) (i : Fin m)
    (hi : L i = some b) : i ∈ upperSet R L ↔ R ≤ b := by
  simpa only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and, hi]
    using (closedTag_upper_iff (R := R) (b := b))

lemma upperPart_present_iff (R : ℝ) (L : LocalList m) (i : Fin m) :
    upperPart R L i ≠ none ↔ i ∈ upperSet R L := by
  by_cases hi : i ∈ upperSet R L
  · have ht := (Finset.mem_filter.mp hi).2
    simp [upperPart, ht, hi, upperSet_present R L i hi]
  · have ht : closedTag R (L i) ≠ 2 := by simpa [upperSet] using hi
    simp [upperPart, ht, hi]

lemma upperSet_card (R : ℝ) (L : LocalList m) :
    (upperSet R L).card = localCount R L 2 := by
  simp only [upperSet, localCount, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma upperSet_entry_ge {R : ℝ} (L : LocalList m) (i : Fin m)
    (hi : i ∈ upperSet R L) : R ≤ entryBid (L i) := by
  cases he : L i with
  | none => exact False.elim (upperSet_present R L i hi he)
  | some b => simpa only [he, entryBid] using (upperSet_iff_bid L i he).mp hi

lemma nonupper_entry_le {R : ℝ} (hR : 0 ≤ R) (L : LocalList m) (i : Fin m)
    (hi : i ∉ upperSet R L) : entryBid (L i) ≤ R := by
  cases he : L i with
  | none => simpa only [he, entryBid] using hR
  | some b =>
    have hb : ¬ R ≤ b := fun h => hi ((upperSet_iff_bid L i he).mpr h)
    simpa only [he, entryBid] using (lt_of_not_ge hb).le

def closedProfiles (m : ℕ) (R : ℝ) : Set (UserProfile m 2) :=
  {d | ∀ i, ((d i).1.2.bid < R ∧ (d i).1.2.routeCount = 2) ∨
    (R ≤ (d i).1.2.bid ∧ (d i).1.2.routeCount = 1)}

lemma measurableSet_closedProfiles (m : ℕ) (R : ℝ) :
    MeasurableSet (closedProfiles m R) := by
  simp only [closedProfiles, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have ha : Measurable (fun d : UserProfile m 2 => (d i).1.2) :=
    (measurable_pi_apply i).fst.snd
  have hb := (measurable_bid 2).comp ha
  have hr := (measurable_routeCount 2).comp ha
  exact ((measurableSet_lt hb measurable_const).inter
    (measurableSet_eq_fun hr measurable_const)).union
      ((measurableSet_le measurable_const hb).inter
        (measurableSet_eq_fun hr measurable_const))

lemma closedProfiles_of_separated_support {d L U R : ℝ} (hUR : U < R)
    (z : UserProfile m 2)
    (hz : ∀ i,
      ((z i).1.2.bid ≤ d ∧ (z i).1.2.routeCount = 2) ∨
      ((z i).1.2.bid ∈ Icc L U ∧ (z i).1.2.routeCount = 2) ∨
      (R ≤ (z i).1.2.bid ∧ (z i).1.2.routeCount = 1)) (hdU : d ≤ U) :
    z ∈ closedProfiles m R := by
  intro i
  rcases hz i with hlo | hact | hupp
  · exact Or.inl ⟨(hlo.1.trans hdU).trans_lt hUR, hlo.2⟩
  · exact Or.inl ⟨hact.1.2.trans_lt hUR, hact.2⟩
  · exact Or.inr hupp

def closedAction (R : ℝ) : Option ℝ → JointAction 2
  | none => ⟨max R 0, le_max_right _ _, 1, by omega⟩
  | some b => ⟨max b 0, le_max_right _ _, if b < R then 2 else 1,
      by split_ifs <;> omega⟩

lemma measurable_closedAction (R : ℝ) : Measurable (closedAction R) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  intro S hS
  change MeasurableSet ((fun b : ℝ => (max b 0, if b < R then (2 : ℕ) else 1)) ⁻¹' S)
  exact (((measurable_id.max measurable_const).prodMk
    (Measurable.ite measurableSet_Iio measurable_const measurable_const))) hS

def closedProfile (m : ℕ) (R : ℝ) (j : Fin 2) (L : LocalList m) : UserProfile m 2 :=
  fun i => ((0, closedAction R (L i)), classifiedOrdering j (L i))

lemma measurable_closedProfile (m : ℕ) (R : ℝ) (j : Fin 2) :
    Measurable (closedProfile m R j) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_const.prodMk
    ((measurable_closedAction R).comp (measurable_pi_apply i))).prodMk
      ((measurable_classifiedOrdering j).comp (measurable_pi_apply i))

lemma observe_closedProfile (R : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) :
    observe (drawsRealization (closedProfile m R j L)) j = L := by
  funext i
  cases hentry : L i with
  | none =>
    simp [observe, drawsRealization, closedProfile, closedAction, classifiedOrdering,
      hentry, firstK_routeTo]
  | some b =>
    have hb : 0 ≤ b := by simpa only [NonnegativeList, hentry, entryBid] using hL i
    by_cases hbR : b < R
    · simp [observe, drawsRealization, closedProfile, closedAction, classifiedOrdering,
        hentry, hbR, firstK_full_two, max_eq_left hb]
    · simp [observe, drawsRealization, closedProfile, closedAction, classifiedOrdering,
        hentry, hbR, firstK_routeTo, max_eq_left hb]

lemma closedProfile_mem (R : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) : closedProfile m R j L ∈ closedProfiles m R := by
  intro i
  cases hentry : L i with
  | none =>
    right
    simpa only [closedProfile, closedAction, hentry] using
      (And.intro (le_max_left R 0) rfl : R ≤ max R 0 ∧ (1 : ℕ) = 1)
  | some b =>
    have hb : 0 ≤ b := by simpa only [NonnegativeList, hentry, entryBid] using hL i
    by_cases hbR : b < R
    · left
      simp [closedProfile, closedAction, hentry, hbR, max_eq_left hb]
    · right
      simp [closedProfile, closedAction, hentry, hbR, max_eq_left hb, le_of_not_gt hbR]

def closedFallback (m : ℕ) (R : ℝ) (j : Fin 2) :
    Kernel (LocalList m) (UserProfile m 2) :=
  Kernel.deterministic (closedProfile m R j) (measurable_closedProfile m R j)

instance (m : ℕ) (R : ℝ) (j : Fin 2) : IsMarkovKernel (closedFallback m R j) := by
  unfold closedFallback
  infer_instance

lemma closedFallback_feasible (R : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂closedFallback m R j L, observe (drawsRealization d) j = L := by
  rw [closedFallback, Kernel.deterministic_apply]
  apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j)
    measurable_const)).mpr
  exact observe_closedProfile R j L ((feasibleObservedList_iff_nonnegative j L).mp hL)

def closedUpperPosterior {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐ d ∂userProfileLaw Γ, d ∈ closedProfiles m R) : PosteriorSystem Γ :=
  posteriorWithFallback Γ (measurableSet_closedProfiles m R) hfull
    (closedFallback m R) (closedFallback_feasible R)

theorem closedUpperPosterior_support {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐ d ∂userProfileLaw Γ, d ∈ closedProfiles m R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂(closedUpperPosterior Γ R hfull).posterior j L,
      observe (drawsRealization d) j = L ∧ d ∈ closedProfiles m R := by
  change ∀ᵐ d ∂posteriorWithFallbackKernel Γ (measurableSet_closedProfiles m R)
    (closedFallback m R) j L, _
  by_cases hgood : L ∈ goodPosteriorLists Γ (closedProfiles m R) j
  · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_pos hgood]
    exact ae_iff.mpr hgood
  · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_neg hgood,
      closedFallback, Kernel.deterministic_apply]
    apply (ae_dirac_iff ((measurableSet_eq_lists (measurable_observe_draws j)
      measurable_const).inter (measurableSet_closedProfiles m R))).mpr
    have hnonneg := (feasibleObservedList_iff_nonnegative j L).mp hL
    exact ⟨observe_closedProfile R j L hnonneg, closedProfile_mem R j L hnonneg⟩

def closedKind (R : ℝ) (z : UserProfile m 2) (i : Fin m) : Fin 3 :=
  if (z i).1.2.bid < R then 0 else 2

lemma closedKind_routes {R : ℝ} (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) :
    TaggedLocal.ClassRoutes (closedKind R z) (drawsRealization z) := by
  constructor
  · intro i hi
    rcases hz i with ⟨hb, hr⟩ | ⟨hb, hr⟩
    · simp [drawsRealization, hr, firstK_full_two]
    · have hh : closedKind R z i = 2 := by simp [closedKind, not_lt.mpr hb]
      exact False.elim (hi hh)
  · intro i hi
    rcases hz i with ⟨hb, hr⟩ | ⟨hb, hr⟩
    · have hh : closedKind R z i = 0 := by simp [closedKind, hb]
      rw [hh] at hi
      have hbad := congrArg Fin.val hi
      norm_num at hbad
    · change (firstK (z i).2 (z i).1.2.routeCount).card = 1
      rw [hr, card_firstK _ _ (by omega)]

lemma closedTag_of_kind (R : ℝ) (z : UserProfile m 2) (i : Fin m) :
    closedTag R (some (z i).1.2.bid) = (closedKind R z i).castSucc := by
  by_cases hb : (z i).1.2.bid < R <;> simp [closedTag, closedKind, hb]

lemma local_counts_correct {R : ℝ} (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (j : Fin 2) :
    localCount R (observe (drawsRealization z) j) 0 =
        TaggedLocal.countKind (closedKind R z) 0 ∧
    localCount R (observe (drawsRealization z) j) 2 =
        TaggedLocal.upperAt (closedKind R z) (drawsRealization z) j := by
  have hr := closedKind_routes z hz
  have hterm (i : Fin m) :
      (if closedTag R (observe (drawsRealization z) j i) = 0 then 1 else 0) =
        (if closedKind R z i = 0 then 1 else 0) ∧
      (if closedTag R (observe (drawsRealization z) j i) = 2 then 1 else 0) =
        (if closedKind R z i = 2 ∧ j ∈ (drawsRealization z).recipients i then 1 else 0) := by
    by_cases hb : (z i).1.2.bid < R
    · have hrec := hr.1 i (by simp [closedKind, hb])
      have hj : j ∈ (drawsRealization z).recipients i := by rw [hrec]; exact Finset.mem_univ j
      have hobs : observe (drawsRealization z) j i = some (z i).1.2.bid := by
        change (if j ∈ (drawsRealization z).recipients i then some ((drawsRealization z).action i).bid else none) = _
        rw [if_pos hj]
        rfl
      simp [hobs, closedTag, closedKind, hb, hj]
    · by_cases hj : j ∈ (drawsRealization z).recipients i
      · have hobs : observe (drawsRealization z) j i = some (z i).1.2.bid := by
          change (if j ∈ (drawsRealization z).recipients i then some ((drawsRealization z).action i).bid else none) = _
          rw [if_pos hj]
          rfl
        simp [hobs, closedTag, closedKind, hb, hj]
      · simp [observe, hj, closedTag, closedKind, hb]
  exact ⟨Finset.sum_congr rfl (fun i _ => (hterm i).1),
    Finset.sum_congr rfl (fun i _ => (hterm i).2)⟩

lemma lowerPart_observe {R : ℝ} (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (j : Fin 2) :
    lowerPart R (observe (drawsRealization z) j) =
      fun i => if (z i).1.2.bid < R then some (z i).1.2.bid else none := by
  funext i
  have hr := closedKind_routes z hz
  by_cases hb : (z i).1.2.bid < R
  · have hrec := hr.1 i (by simp [closedKind, hb])
    have hj : j ∈ (drawsRealization z).recipients i := by rw [hrec]; exact Finset.mem_univ j
    have hobs : observe (drawsRealization z) j i = some (z i).1.2.bid := by
      change (if j ∈ (drawsRealization z).recipients i then some ((drawsRealization z).action i).bid else none) = _
      rw [if_pos hj]
      rfl
    simp [lowerPart, hobs, closedTag, hb]
  · by_cases hj : j ∈ (drawsRealization z).recipients i
    · have hobs : observe (drawsRealization z) j i = some (z i).1.2.bid := by
        change (if j ∈ (drawsRealization z).recipients i then some ((drawsRealization z).action i).bid else none) = _
        rw [if_pos hj]
        rfl
      simp [lowerPart, hobs, closedTag, hb]
    · simp [lowerPart, observe, hj, closedTag, hb]

lemma lowerPart_common {R : ℝ} (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (j l : Fin 2) :
    lowerPart R (observe (drawsRealization z) j) =
      lowerPart R (observe (drawsRealization z) l) := by
  rw [lowerPart_observe z hz j, lowerPart_observe z hz l]

abbrev ClosedContext (m : ℕ) := ClassifiedContext m

def observedClosedContext (R : ℝ) (j : Fin 2) (L : LocalList m) : ClosedContext m :=
  let broadcasts := localCount R L 0
  let here := localCount R L 2
  let there := m - broadcasts - here
  (lowerPart R L, if j = 0 then (here, there) else (there, here))

lemma measurable_observedClosedContext (R : ℝ) (j : Fin 2) :
    Measurable (observedClosedContext (m := m) R j) := by
  have hb := measurable_localCount (m := m) R 0
  have hh := measurable_localCount (m := m) R 2
  have ht : Measurable (fun L : LocalList m => m - localCount R L 0 - localCount R L 2) :=
    (measurable_of_countable (fun BH : ℕ × ℕ => m - BH.1 - BH.2)).comp (hb.prodMk hh)
  unfold observedClosedContext
  split_ifs
  · exact (measurable_lowerPart R).prodMk (hh.prodMk ht)
  · exact (measurable_lowerPart R).prodMk (ht.prodMk hh)

def actualClosedContext (R : ℝ) (z : UserProfile m 2) : ClosedContext m :=
  (lowerPart R (observe (drawsRealization z) 0),
    TaggedLocal.upperAt (closedKind R z) (drawsRealization z) 0,
    TaggedLocal.upperAt (closedKind R z) (drawsRealization z) 1)

lemma contextUpper_observedClosed (R : ℝ) (j : Fin 2) (L : LocalList m) :
    contextUpper j (observedClosedContext R j L) = localCount R L 2 := by
  fin_cases j <;> simp [contextUpper, observedClosedContext]

theorem observedClosedContext_eq_actual {R : ℝ} (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (j : Fin 2) :
    observedClosedContext R j (observe (drawsRealization z) j) = actualClosedContext R z := by
  have hcounts := local_counts_correct z hz
  have hpartition := TaggedLocal.counts_partition (closedKind R z) (drawsRealization z)
    (closedKind_routes z hz)
  have hactive : TaggedLocal.countKind (closedKind R z) 1 = 0 := by
    unfold TaggedLocal.countKind
    apply Finset.sum_eq_zero
    intro i _
    by_cases hb : (z i).1.2.bid < R <;> simp [closedKind, hb]
  rw [hactive] at hpartition
  have ht0 : m - TaggedLocal.countKind (closedKind R z) 0 -
      TaggedLocal.upperAt (closedKind R z) (drawsRealization z) 0 =
      TaggedLocal.upperAt (closedKind R z) (drawsRealization z) 1 := by omega
  have ht1 : m - TaggedLocal.countKind (closedKind R z) 0 -
      TaggedLocal.upperAt (closedKind R z) (drawsRealization z) 1 =
      TaggedLocal.upperAt (closedKind R z) (drawsRealization z) 0 := by omega
  have hcommon := lowerPart_common z hz j 0
  unfold observedClosedContext actualClosedContext
  rw [hcommon, (hcounts j).1, (hcounts j).2]
  fin_cases j
  · simp [ht0]
  · simp [ht1]

theorem closed_context_common_on_actual_profiles {R : ℝ} (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (j k : Fin 2) :
    observedClosedContext R j (observe (drawsRealization z) j) =
      observedClosedContext R k (observe (drawsRealization z) k) := by
  rw [observedClosedContext_eq_actual z hz j, observedClosedContext_eq_actual z hz k]

theorem closedUpperPosterior_context {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles m R)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) (l : Fin 2) :
    ∀ᵐ z ∂(closedUpperPosterior Γ R hfull).posterior j L,
      observedClosedContext R l (observe (drawsRealization z) l) = observedClosedContext R j L := by
  filter_upwards [closedUpperPosterior_support Γ R hfull j L hL] with z hz
  rw [observedClosedContext_eq_actual z hz.2 l,
    ← observedClosedContext_eq_actual z hz.2 j, hz.1]

lemma nonnegative_observedClosedContext (R : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) : NonnegativeList (observedClosedContext R j L).1 := by
  intro i
  change 0 ≤ entryBid (lowerPart R L i)
  unfold lowerPart
  split
  · exact hL i
  · simp only [entryBid, le_refl]

def inBox (L U : ℝ) (X : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ b, X i = some b ∧ b ∈ Icc L U)

def activeSet (d R : ℝ) (X : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ b, lowerPart R X i = some b ∧ d < b)

def exceptional (d L U R : ℝ) (X : LocalList m) : Finset (Fin m) :=
  activeSet d R X \ inBox L U X

lemma measurable_filter_entries (S : Set (Option ℝ)) (hS : MeasurableSet S) :
    Measurable (fun X : LocalList m => Finset.univ.filter (fun i => X i ∈ S)) := by
  apply measurable_to_countable'
  intro A
  have he : (fun X : LocalList m => Finset.univ.filter (fun i => X i ∈ S)) ⁻¹' {A} =
      ⋂ i : Fin m, {X : LocalList m | (i ∈ A ↔ X i ∈ S)} := by
    ext X
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_setOf_eq]
    exact ⟨fun h i => by rw [← h]; simp,
      fun h => Finset.ext (fun i => by simpa only [Finset.mem_filter,
        Finset.mem_univ, true_and] using (h i).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ A
  · simp only [hi, true_iff]
    exact (measurable_pi_apply i) hS
  · simp only [hi, false_iff]
    exact ((measurable_pi_apply i) hS).compl

lemma measurable_inBox (L U : ℝ) : Measurable (inBox (m := m) L U) := by
  let S : Set (Option ℝ) := {o | ∃ b, o = some b ∧ b ∈ Icc L U}
  have hS : MeasurableSet S := by
    change MeasurableSet {x : ℝ | ∃ b, some x = some b ∧ b ∈ Icc L U}
    convert! (measurableSet_Icc : MeasurableSet (Icc L U)) using 1
    ext x
    simp
  convert! measurable_filter_entries (m := m) S hS using 1
  funext X
  ext i
  simp [inBox, S]

lemma measurable_activeSet (d R : ℝ) : Measurable (activeSet (m := m) d R) := by
  have he : activeSet (m := m) d R =
      fun X : LocalList m => Finset.univ.filter
        (fun i => ∃ b, X i = some b ∧ b ∈ Ioo d R) := by
    funext X
    apply Finset.ext
    intro i
    cases hi : X i with
    | none => simp [activeSet, lowerPart, closedTag, hi]
    | some b =>
      by_cases hb : b < R
      · simp [activeSet, lowerPart, closedTag, hi, hb, and_comm]
      · simp [activeSet, lowerPart, closedTag, hi, hb]
  rw [he]
  let S : Set (Option ℝ) := {o | ∃ b, o = some b ∧ b ∈ Ioo d R}
  have hS : MeasurableSet S := by
    change MeasurableSet {x : ℝ | ∃ b, some x = some b ∧ b ∈ Ioo d R}
    convert! (measurableSet_Ioo : MeasurableSet (Ioo d R)) using 1
    ext x
    simp
  convert! measurable_filter_entries (m := m) S hS using 1
  funext X
  ext i
  simp [S]

lemma measurable_exceptional (d L U R : ℝ) :
    Measurable (exceptional (m := m) d L U R) :=
  (measurable_of_countable (fun AB : Finset (Fin m) × Finset (Fin m) => AB.1 \ AB.2)).comp
    ((measurable_activeSet d R).prodMk (measurable_inBox L U))

lemma exceptional_card_cases (d L U R : ℝ) (X : LocalList m) :
    exceptional d L U R X = ∅ ∨
      (exceptional d L U R X).card = 1 ∨ 2 ≤ (exceptional d L U R X).card := by
  by_cases hz : (exceptional d L U R X).card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hz)
  · right
    omega

lemma floor_not_active (d R : ℝ) (X : LocalList m) (i : Fin m)
    (hi : X i = some R) : i ∉ activeSet d R X := by
  simp [activeSet, lowerPart, closedTag, hi]

end FCAppendix.Affine.Hybrid.Native02
