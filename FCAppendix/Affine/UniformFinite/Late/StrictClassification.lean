import FCAppendix.Affine.UniformFinite.NativeContext
import FCAppendix.Affine.Hybrid.ClassifiedOptimality

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.Strict
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical
open Hybrid
open scoped BigOperators

def tag (R : ℝ) : Option ℝ → Fin 4
  | none => 3
  | some b => if b < R then 0 else 2

theorem measurable_tag (R : ℝ) : Measurable (tag R) := by
  intro S hS
  change MeasurableSet ((fun b : ℝ => if b < R then (0:Fin 4) else 2) ⁻¹' S)
  exact (Measurable.ite measurableSet_Iio measurable_const measurable_const) hS

def localCount {M : ℕ} (R : ℝ) (L : LocalList M) (k : Fin 4) : ℕ :=
  ∑ a : Fin M, if tag R (L a)=k then 1 else 0

theorem measurable_localCount {M : ℕ} (R : ℝ) (k : Fin 4) :
    Measurable (fun L : LocalList M => localCount R L k) := by
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_tag R).comp (measurable_pi_apply a)) measurable_const)
    measurable_const measurable_const

def lowerPart {M : ℕ} (R : ℝ) (L : LocalList M) : LocalList M :=
  fun a => if tag R (L a)=0 then L a else none

def upperPart {M : ℕ} (R : ℝ) (L : LocalList M) : LocalList M :=
  fun a => if tag R (L a)=2 then L a else none

def upperSet {M : ℕ} (R : ℝ) (L : LocalList M) : Finset (Fin M) :=
  Finset.univ.filter (fun a => tag R (L a)=2)

theorem measurable_lowerPart {M : ℕ} (R : ℝ) : Measurable (lowerPart (M:=M) R) := by
  apply measurable_pi_lambda
  intro a
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_tag R).comp (measurable_pi_apply a)) measurable_const)
    (measurable_pi_apply a) measurable_const

theorem measurable_upperPart {M : ℕ} (R : ℝ) : Measurable (upperPart (M:=M) R) := by
  apply measurable_pi_lambda
  intro a
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_tag R).comp (measurable_pi_apply a)) measurable_const)
    (measurable_pi_apply a) measurable_const

theorem measurable_upperSet {M : ℕ} (R : ℝ) : Measurable (upperSet (M:=M) R) := by
  apply measurable_to_countable'
  intro S
  have he : (upperSet R) ⁻¹' {S} =
      ⋂ a : Fin M, {L : LocalList M | (a∈S ↔ tag R (L a)=2)} := by
    ext L
    simp only [mem_preimage,mem_singleton_iff,mem_iInter,mem_setOf_eq,upperSet]
    exact ⟨fun h a => by rw [← h]; simp,
      fun h => Finset.ext (fun a => by
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using (h a).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro a
  by_cases ha : a∈S
  · simp only [ha,true_iff]
    exact measurableSet_eq_fun ((measurable_tag R).comp (measurable_pi_apply a)) measurable_const
  · simp only [ha,false_iff]
    exact (measurableSet_eq_fun ((measurable_tag R).comp (measurable_pi_apply a))
      measurable_const).compl

theorem upperSet_card {M : ℕ} (R : ℝ) (L : LocalList M) :
    (upperSet R L).card=localCount R L 2 := by
  simp only [upperSet,localCount,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem lowerPart_some {M : ℕ} {R b : ℝ} (L : LocalList M) (a : Fin M)
    (ha : L a=some b) (hb : b< R) : lowerPart R L a=some b := by
  simp [lowerPart,tag,ha,hb]

theorem upperSet_present {M : ℕ} (R : ℝ) (L : LocalList M) (a : Fin M)
    (ha : a∈upperSet R L) : L a≠none := by
  have ht := (Finset.mem_filter.mp ha).2
  intro hn
  simp [hn,tag] at ht

theorem upperSet_iff_bid {M : ℕ} {R b : ℝ} (L : LocalList M) (a : Fin M)
    (ha : L a=some b) : a∈upperSet R L ↔ R≤ b := by
  by_cases hb : b< R
  · simp [upperSet,tag,ha,hb,not_le.mpr hb]
  · simp [upperSet,tag,ha,hb,le_of_not_gt hb]

theorem upperSet_entry_ge {M : ℕ} {R : ℝ} (L : LocalList M) (a : Fin M)
    (ha : a∈upperSet R L) : R≤ entryBid (L a) := by
  cases he : L a with
  | none => exact False.elim (upperSet_present R L a ha he)
  | some b => simpa only [he,entryBid] using (upperSet_iff_bid L a he).mp ha

theorem nonupper_entry_le {M : ℕ} {R : ℝ} (hR : 0≤ R) (L : LocalList M)
    (a : Fin M) (ha : a∉upperSet R L) : entryBid (L a)≤ R := by
  cases he : L a with
  | none => simpa only [he,entryBid] using hR
  | some b =>
    have hb : b< R := lt_of_not_ge (fun h => ha ((upperSet_iff_bid L a he).mpr h))
    simpa only [he,entryBid] using hb.le

theorem upperPart_present_iff {M : ℕ} (R : ℝ) (L : LocalList M) (a : Fin M) :
    upperPart R L a≠none ↔ a∈upperSet R L := by
  by_cases ha : a∈upperSet R L
  · have ht := (Finset.mem_filter.mp ha).2
    simp [upperPart,ht,ha,upperSet_present R L a ha]
  · have ht : tag R (L a)≠2 := by simpa [upperSet] using ha
    simp [upperPart,ht,ha]

theorem lowerPart_present {M : ℕ} (R : ℝ) (L : LocalList M) (a : Fin M)
    (ha : lowerPart R L a≠none) : L a≠none ∧ a∉upperSet R L := by
  by_cases ht : tag R (L a)=0
  · simp only [lowerPart,if_pos ht] at ha
    exact ⟨ha,by simp [upperSet,ht]⟩
  · simp only [lowerPart,if_neg ht] at ha
    exact False.elim (ha rfl)

theorem lowerPart_upper {M : ℕ} (R : ℝ) (L : LocalList M) (a : Fin M)
    (ha : a∈upperSet R L) : lowerPart R L a=none := by
  have ht := (Finset.mem_filter.mp ha).2
  simp [lowerPart,ht]

theorem lowerPart_nonnegative {M : ℕ} (R : ℝ) (L : LocalList M)
    (hL : NonnegativeList L) : NonnegativeList (lowerPart R L) := by
  intro a
  by_cases ht : tag R (L a)=0
  · simpa only [lowerPart,if_pos ht] using hL a
  · simp only [lowerPart,if_neg ht,entryBid,le_refl]

theorem present_lowerPart {M : ℕ} (R : ℝ) (L : LocalList M) :
    NativeContext.present (lowerPart R L)=Finset.univ.filter (fun a => tag R (L a)=0) := by
  ext a
  cases he : L a with
  | none => simp [NativeContext.present,lowerPart,tag,he]
  | some b => by_cases hb : b< R <;> simp [NativeContext.present,lowerPart,tag,he,hb]

theorem present_lowerPart_card {M : ℕ} (R : ℝ) (L : LocalList M) :
    (NativeContext.present (lowerPart R L)).card=localCount R L 0 := by
  rw [present_lowerPart]
  simp only [localCount,Finset.card_eq_sum_ones,Finset.sum_filter]

def observedContext {M : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList M) : ClassifiedContext M :=
  let nlow := localCount R L 0
  let here := localCount R L 2
  let there := M-nlow-here
  (lowerPart R L,if j=0 then (here,there) else (there,here))

theorem measurable_observedContext {M : ℕ} (R : ℝ) (j : Fin 2) :
    Measurable (observedContext (M:=M) R j) := by
  have hl := measurable_localCount (M:=M) R 0
  have hh := measurable_localCount (M:=M) R 2
  have ht : Measurable (fun L : LocalList M => M-localCount R L 0-localCount R L 2) :=
    (measurable_of_countable (fun p : ℕ×ℕ => M-p.1-p.2)).comp (hl.prodMk hh)
  unfold observedContext
  split_ifs
  · exact (measurable_lowerPart R).prodMk (hh.prodMk ht)
  · exact (measurable_lowerPart R).prodMk (ht.prodMk hh)

theorem contextUpper_observed {M : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList M) :
    contextUpper j (observedContext R j L)=localCount R L 2 := by
  fin_cases j <;> simp [contextUpper,observedContext]

theorem observed_valid {M : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList M) :
    NativeContext.Valid (observedContext R j L) := by
  have hd : Disjoint (NativeContext.present (lowerPart R L)) (upperSet R L) := by
    apply Finset.disjoint_left.mpr
    intro a ha hu
    have hp := (Finset.mem_filter.mp ha).2
    exact (lowerPart_present R L a hp).2 hu
  have hc : (NativeContext.present (lowerPart R L)).card+(upperSet R L).card≤ M := by
    rw [← Finset.card_union_of_disjoint hd]
    simpa using Finset.card_le_univ (NativeContext.present (lowerPart R L) ∪ upperSet R L)
  rw [present_lowerPart_card,upperSet_card] at hc
  by_cases hj : j=0
  · simp only [NativeContext.Valid,observedContext,if_pos hj,present_lowerPart_card]
    omega
  · simp only [NativeContext.Valid,observedContext,if_neg hj,present_lowerPart_card]
    omega

def profiles (M : ℕ) (R : ℝ) : Set (UserProfile M 2) :=
  {d | ∀a,((d a).1.2.bid< R ∧ (d a).1.2.routeCount=2) ∨
    (R≤(d a).1.2.bid ∧ (d a).1.2.routeCount=1)}

def strongProfiles (M : ℕ) (U R : ℝ) : Set (UserProfile M 2) :=
  {d | ∀a,((d a).1.2.bid≤ U ∧ (d a).1.2.routeCount=2) ∨
    (R≤(d a).1.2.bid ∧ (d a).1.2.routeCount=1)}

theorem measurableSet_profiles (M : ℕ) (R : ℝ) : MeasurableSet (profiles M R) := by
  simp only [profiles,setOf_forall]
  apply MeasurableSet.iInter
  intro a
  have ha : Measurable (fun d : UserProfile M 2 => (d a).1.2) :=
    (measurable_pi_apply a).fst.snd
  have hb := (measurable_bid 2).comp ha
  have hr := (measurable_routeCount 2).comp ha
  exact ((measurableSet_lt hb measurable_const).inter
    (measurableSet_eq_fun hr measurable_const)).union
    ((measurableSet_le measurable_const hb).inter (measurableSet_eq_fun hr measurable_const))

theorem measurableSet_strongProfiles (M : ℕ) (U R : ℝ) :
    MeasurableSet (strongProfiles M U R) := by
  simp only [strongProfiles,setOf_forall]
  apply MeasurableSet.iInter
  intro a
  have ha : Measurable (fun d : UserProfile M 2 => (d a).1.2) :=
    (measurable_pi_apply a).fst.snd
  have hb := (measurable_bid 2).comp ha
  have hr := (measurable_routeCount 2).comp ha
  exact ((measurableSet_le hb measurable_const).inter
    (measurableSet_eq_fun hr measurable_const)).union
    ((measurableSet_le measurable_const hb).inter (measurableSet_eq_fun hr measurable_const))

theorem strongProfiles_subset {M : ℕ} {U R : ℝ} (hUR : U< R) :
    strongProfiles M U R ⊆ profiles M R := by
  intro d hd a
  rcases hd a with h | h
  · exact Or.inl ⟨h.1.trans_lt hUR,h.2⟩
  · exact Or.inr h

theorem strongProfiles_old {M : ℕ} {U R : ℝ} (hUR : U< R) :
    strongProfiles M U R ⊆ Hybrid.classifiedProfiles M U := by
  intro d hd a
  rcases hd a with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hUR.trans_le h.1,h.2⟩

def completedAction (R : ℝ) : Option ℝ → JointAction 2
  | none => ⟨max R 0,le_max_right _ _,1,by omega⟩
  | some b => ⟨max b 0,le_max_right _ _,if b< R then 2 else 1,by split_ifs <;> omega⟩

theorem measurable_completedAction (R : ℝ) : Measurable (completedAction R) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  intro S hS
  change MeasurableSet ((fun b : ℝ => (max b 0,if b< R then (2:ℕ) else 1)) ⁻¹' S)
  exact (((measurable_id.max measurable_const).prodMk
    (Measurable.ite measurableSet_Iio measurable_const measurable_const))) hS

def completedProfile (M : ℕ) (R : ℝ) (j : Fin 2) (L : LocalList M) : UserProfile M 2 :=
  fun a => ((0,completedAction R (L a)),Hybrid.classifiedOrdering j (L a))

theorem measurable_completedProfile (M : ℕ) (R : ℝ) (j : Fin 2) :
    Measurable (completedProfile M R j) := by
  apply measurable_pi_lambda
  intro a
  exact (measurable_const.prodMk
    ((measurable_completedAction R).comp (measurable_pi_apply a))).prodMk
    ((Hybrid.measurable_classifiedOrdering j).comp (measurable_pi_apply a))

theorem observe_completedProfile {M : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList M)
    (hL : NonnegativeList L) : observe (drawsRealization (completedProfile M R j L)) j=L := by
  funext a
  cases he : L a with
  | none => simp [observe,drawsRealization,completedProfile,completedAction,
      Hybrid.classifiedOrdering,he,firstK_routeTo]
  | some b =>
    have hb : 0≤ b := by simpa only [he,entryBid] using hL a
    by_cases hbR : b< R
    · simp [observe,drawsRealization,completedProfile,completedAction,
        Hybrid.classifiedOrdering,he,hbR,firstK_full_two,max_eq_left hb]
    · simp [observe,drawsRealization,completedProfile,completedAction,
        Hybrid.classifiedOrdering,he,hbR,firstK_routeTo,max_eq_left hb]

theorem completedProfile_mem {M : ℕ} {R : ℝ} (hR : 0≤ R) (j : Fin 2)
    (L : LocalList M) (hL : NonnegativeList L) : completedProfile M R j L∈profiles M R := by
  intro a
  cases he : L a with
  | none =>
    right
    simp [completedProfile,completedAction,he,max_eq_left hR]
  | some b =>
    have hb : 0≤ b := by simpa only [he,entryBid] using hL a
    by_cases hbR : b< R
    · left
      simp [completedProfile,completedAction,he,hbR,max_eq_left hb]
    · right
      simp [completedProfile,completedAction,he,hbR,max_eq_left hb,le_of_not_gt hbR]

def fallback (M : ℕ) (R : ℝ) (j : Fin 2) : Kernel (LocalList M) (UserProfile M 2) :=
  Kernel.deterministic (completedProfile M R j) (measurable_completedProfile M R j)

instance (M : ℕ) (R : ℝ) (j : Fin 2) : IsMarkovKernel (fallback M R j) := by
  unfold fallback
  infer_instance

theorem fallback_feasible {M : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList M)
    (hL : FeasibleObservedList j L) :
    ∀ᵐd ∂fallback M R j L,observe (drawsRealization d) j=L := by
  rw [fallback,Kernel.deterministic_apply]
  apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
  exact observe_completedProfile R j L ((feasibleObservedList_iff_nonnegative j L).mp hL)

def posterior {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame M 2 c Seed) {U R : ℝ}
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R) : PosteriorSystem Γ :=
  posteriorWithFallback Γ (measurableSet_strongProfiles M U R) hfull
    (fallback M R) (fallback_feasible R)

theorem posterior_support {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame M 2 c Seed) {U R : ℝ} (hU : 0≤ U) (hUR : U< R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R)
    (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L) :
    ∀ᵐd ∂(posterior Γ hfull).posterior j L,
      observe (drawsRealization d) j=L ∧ d∈profiles M R := by
  change ∀ᵐd ∂posteriorWithFallbackKernel Γ (measurableSet_strongProfiles M U R)
    (fallback M R) j L,_
  by_cases hg : L∈goodPosteriorLists Γ (strongProfiles M U R) j
  · simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_pos hg]
    exact (ae_iff.mpr hg).mono (fun d hd => ⟨hd.1,strongProfiles_subset hUR hd.2⟩)
  · simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_neg hg,
      fallback,Kernel.deterministic_apply]
    apply (ae_dirac_iff ((measurableSet_eq_lists (measurable_observe_draws j) measurable_const).inter
      (measurableSet_profiles M R))).mpr
    have hn := (feasibleObservedList_iff_nonnegative j L).mp hL
    exact ⟨observe_completedProfile R j L hn,completedProfile_mem (hU.trans hUR.le) j L hn⟩

theorem posterior_eq_regular_ae {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame M 2 c Seed) {U R : ℝ}
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R) (j : Fin 2) :
    (posterior Γ hfull).posterior j =ᵐ[observedListLaw Γ j] regularUserPosterior Γ j := by
  filter_upwards [ae_goodPosteriorLists Γ (measurableSet_strongProfiles M U R) hfull j] with L hL
  simp only [posterior,posteriorWithFallback,posteriorWithFallbackKernel,
    Kernel.piecewise_apply,if_pos hL]

theorem exceptional_not_strong_observation {M : ℕ} {U R b : ℝ}
    (j : Fin 2) (L : LocalList M) (a : Fin M) (ha : L a=some b)
    (hUb : U< b) (hbR : b< R) (d : UserProfile M 2) :
    ¬(observe (drawsRealization d) j=L ∧ d∈strongProfiles M U R) := by
  rintro ⟨hobs,hd⟩
  have he : observe (drawsRealization d) j a=some b := by rw [hobs,ha]
  have hj : j∈(drawsRealization d).recipients a := by
    by_contra hn
    simp only [observe,if_neg hn] at he
    cases he
  have hbid : (d a).1.2.bid=b := by
    apply Option.some.inj
    change j∈firstK (d a).2 (d a).1.2.routeCount at hj
    simpa only [observe,drawsRealization,if_pos hj] using he
  rcases hd a with h | h
  · rw [hbid] at h
    exact (not_le.mpr hUb) h.1
  · rw [hbid] at h
    exact (not_le.mpr hbR) h.1

theorem posterior_exceptional {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame M 2 c Seed) {U R : ℝ}
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R)
    (j : Fin 2) (L : LocalList M) (a : Fin M) (b : ℝ) (ha : L a=some b)
    (hUb : U< b) (hbR : b< R) :
    (posterior Γ hfull).posterior j L=Measure.dirac (completedProfile M R j L) := by
  have hg : L∉goodPosteriorLists Γ (strongProfiles M U R) j := by
    intro h
    have he : {d : UserProfile M 2 | ¬(observe (drawsRealization d) j=L ∧
        d∈strongProfiles M U R)}=univ :=
      Set.eq_univ_of_forall (exceptional_not_strong_observation j L a ha hUb hbR)
    change regularUserPosterior Γ j L _=0 at h
    rw [he,measure_univ] at h
    exact one_ne_zero h
  simp only [posterior,posteriorWithFallback,posteriorWithFallbackKernel,
    Kernel.piecewise_apply,if_neg hg,fallback,Kernel.deterministic_apply]

def kind {M : ℕ} (R : ℝ) (d : UserProfile M 2) (a : Fin M) : Fin 3 :=
  if (d a).1.2.bid< R then 0 else 2

theorem kind_routes {M : ℕ} {R : ℝ} (d : UserProfile M 2) (hd : d∈profiles M R) :
    TaggedLocal.ClassRoutes (kind R d) (drawsRealization d) := by
  constructor
  · intro a ha
    rcases hd a with h | h
    · simp [drawsRealization,h.2,firstK_full_two]
    · have he : kind R d a=2 := by simp [kind,not_lt.mpr h.1]
      exact False.elim (ha he)
  · intro a ha
    rcases hd a with h | h
    · have he : kind R d a=0 := by simp [kind,h.1]
      rw [he] at ha
      exact False.elim ((by decide : (0:Fin 3)≠2) ha)
    · change (firstK (d a).2 (d a).1.2.routeCount).card=1
      rw [h.2,card_firstK _ _ (by omega)]

theorem lowerPart_observe {M : ℕ} {R : ℝ} (d : UserProfile M 2)
    (hd : d∈profiles M R) (j : Fin 2) :
    lowerPart R (observe (drawsRealization d) j)=
      fun a => if (d a).1.2.bid< R then some (d a).1.2.bid else none := by
  funext a
  rcases hd a with h | h
  · simp [lowerPart,tag,observe,drawsRealization,h.2,firstK_full_two,h.1]
  · by_cases hj : j∈(drawsRealization d).recipients a
    · change j∈firstK (d a).2 (d a).1.2.routeCount at hj
      simp [lowerPart,tag,observe,drawsRealization,hj,not_lt.mpr h.1]
    · simp [lowerPart,tag,observe,hj,not_lt.mpr h.1]

theorem lowerPart_common {M : ℕ} {R : ℝ} (d : UserProfile M 2)
    (hd : d∈profiles M R) (j l : Fin 2) :
    lowerPart R (observe (drawsRealization d) j)=
      lowerPart R (observe (drawsRealization d) l) := by
  rw [lowerPart_observe d hd j,lowerPart_observe d hd l]

theorem local_counts_correct {M : ℕ} {R : ℝ} (d : UserProfile M 2)
    (hd : d∈profiles M R) (j : Fin 2) :
    localCount R (observe (drawsRealization d) j) 0=TaggedLocal.countKind (kind R d) 0 ∧
    localCount R (observe (drawsRealization d) j) 2=
      TaggedLocal.upperAt (kind R d) (drawsRealization d) j := by
  have hterm (a : Fin M) :
      (if tag R (observe (drawsRealization d) j a)=0 then 1 else 0)=
        (if kind R d a=0 then (1:ℕ) else 0) ∧
      (if tag R (observe (drawsRealization d) j a)=2 then 1 else 0)=
        (if kind R d a=2 ∧ j∈(drawsRealization d).recipients a then (1:ℕ) else 0) := by
    rcases hd a with h | h
    · simp [observe,drawsRealization,h.2,firstK_full_two,tag,kind,h.1]
    · by_cases hj : j∈(drawsRealization d).recipients a
      · change j∈firstK (d a).2 (d a).1.2.routeCount at hj
        simp [observe,tag,kind,drawsRealization,hj,not_lt.mpr h.1]
      · simp [observe,hj,tag,kind,not_lt.mpr h.1]
  exact ⟨Finset.sum_congr rfl (fun a _ => (hterm a).1),
    Finset.sum_congr rfl (fun a _ => (hterm a).2)⟩

def actualContext {M : ℕ} (R : ℝ) (d : UserProfile M 2) : ClassifiedContext M :=
  (lowerPart R (observe (drawsRealization d) 0),
    TaggedLocal.upperAt (kind R d) (drawsRealization d) 0,
    TaggedLocal.upperAt (kind R d) (drawsRealization d) 1)

theorem observedContext_eq_actual {M : ℕ} {R : ℝ} (d : UserProfile M 2)
    (hd : d∈profiles M R) (j : Fin 2) :
    observedContext R j (observe (drawsRealization d) j)=actualContext R d := by
  have hcounts := local_counts_correct d hd
  have hp := TaggedLocal.counts_partition (kind R d) (drawsRealization d) (kind_routes d hd)
  have hactive : TaggedLocal.countKind (kind R d) 1=0 := by
    unfold TaggedLocal.countKind
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : (d a).1.2.bid< R <;> simp [kind,ha]
  rw [hactive] at hp
  have ht0 : M-TaggedLocal.countKind (kind R d) 0-
      TaggedLocal.upperAt (kind R d) (drawsRealization d) 0=
      TaggedLocal.upperAt (kind R d) (drawsRealization d) 1 := by omega
  have ht1 : M-TaggedLocal.countKind (kind R d) 0-
      TaggedLocal.upperAt (kind R d) (drawsRealization d) 1=
      TaggedLocal.upperAt (kind R d) (drawsRealization d) 0 := by omega
  have hcommon := lowerPart_common d hd j 0
  unfold observedContext actualContext
  rw [hcommon,(hcounts j).1,(hcounts j).2]
  fin_cases j <;> simp [ht0,ht1]

theorem posterior_context {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame M 2 c Seed) {U R : ℝ} (hU : 0≤ U) (hUR : U< R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈strongProfiles M U R)
    (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L) (l : Fin 2) :
    ∀ᵐd ∂(posterior Γ hfull).posterior j L,
      observedContext R l (observe (drawsRealization d) l)=observedContext R j L := by
  filter_upwards [posterior_support Γ hU hUR hfull j L hL] with d hd
  rw [observedContext_eq_actual d hd.2 l,← observedContext_eq_actual d hd.2 j,hd.1]

theorem upper_other_absent {M : ℕ} {R b : ℝ} (d : UserProfile M 2)
    (hd : d∈profiles M R) (j : Fin 2) (a : Fin M)
    (ha : observe (drawsRealization d) j a=some b) (hb : R≤ b) :
    observe (drawsRealization d) (otherProposer j) a=none := by
  have hj : j∈(drawsRealization d).recipients a := by
    by_contra hn
    simp only [observe,if_neg hn] at ha
    cases ha
  have hbid : (d a).1.2.bid=b := by
    apply Option.some.inj
    change j∈firstK (d a).2 (d a).1.2.routeCount at hj
    simpa only [observe,drawsRealization,if_pos hj] using ha
  have hr : (d a).1.2.routeCount=1 := by
    rcases hd a with h | h
    · rw [hbid] at h
      exact False.elim ((not_lt.mpr hb) h.1)
    · exact h.2
  have hc : ((drawsRealization d).recipients a).card=1 := by
    rw [(drawsRealization d).chosen_size]
    exact hr
  obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hc
  have hlj : l=j := by
    rw [hl] at hj
    exact (Finset.mem_singleton.mp hj).symm
  rw [hlj] at hl
  simp only [observe,hl,Finset.mem_singleton,otherProposer_ne,if_false]

def OriginalList {M : ℕ} (U R : ℝ) (L : LocalList M) : Prop :=
  ∀a b,L a=some b → b≤ U ∨ R≤ b

theorem original_observe {M : ℕ} {U R : ℝ} (d : UserProfile M 2)
    (hd : d∈strongProfiles M U R) (j : Fin 2) :
    OriginalList U R (observe (drawsRealization d) j) := by
  intro a b he
  have hj : j∈(drawsRealization d).recipients a := by
    by_contra hn
    simp only [observe,if_neg hn] at he
    cases he
  have hb : (d a).1.2.bid=b := by
    apply Option.some.inj
    change j∈firstK (d a).2 (d a).1.2.routeCount at hj
    simpa only [observe,drawsRealization,if_pos hj] using he
  rcases hd a with h | h
  · exact Or.inl (hb ▸ h.1)
  · exact Or.inr (hb ▸ h.1)

theorem tag_eq_original {M : ℕ} {U R : ℝ} (hUR : U< R) (L : LocalList M)
    (hL : OriginalList U R L) (a : Fin M) : tag R (L a)=TaggedLocal.tag U U (L a) := by
  cases he : L a with
  | none => simp [tag,TaggedLocal.tag]
  | some b =>
    rcases hL a b he with hb | hb
    · simp [tag,TaggedLocal.tag,hb,hb.trans_lt hUR]
    · simp [tag,TaggedLocal.tag,not_lt.mpr hb,not_le.mpr (hUR.trans_le hb)]

theorem lowerPart_eq_original {M : ℕ} {U R : ℝ} (hUR : U< R) (L : LocalList M)
    (hL : OriginalList U R L) : lowerPart R L=Hybrid.broadcastPart U L := by
  funext a
  simp only [lowerPart,Hybrid.broadcastPart,TaggedLocal.lowList,tag_eq_original hUR L hL a]

theorem upperPart_eq_original {M : ℕ} {U R : ℝ} (hUR : U< R) (L : LocalList M)
    (hL : OriginalList U R L) : upperPart R L=Hybrid.upperPart U L := by
  funext a
  simp only [upperPart,Hybrid.upperPart,tag_eq_original hUR L hL a]

theorem upperSet_eq_original {M : ℕ} {U R : ℝ} (hUR : U< R) (L : LocalList M)
    (hL : OriginalList U R L) : upperSet R L=Hybrid.upperSet U L := by
  ext a
  simp only [upperSet,Hybrid.upperSet,Finset.mem_filter,tag_eq_original hUR L hL a]

theorem localCount_eq_original {M : ℕ} {U R : ℝ} (hUR : U< R) (L : LocalList M)
    (hL : OriginalList U R L) (k : Fin 4) :
    localCount R L k=TaggedLocal.localCount U U L k := by
  apply Finset.sum_congr rfl
  intro a _
  rw [tag_eq_original hUR L hL a]

theorem observedContext_eq_original {M : ℕ} {U R : ℝ} (hUR : U< R) (j : Fin 2)
    (L : LocalList M) (hL : OriginalList U R L) :
    observedContext R j L=Hybrid.observedContext U j L := by
  simp only [observedContext,Hybrid.observedContext,lowerPart_eq_original hUR L hL,
    localCount_eq_original hUR L hL]

end FCAppendix.Affine.UniformFinite.Late.Strict
