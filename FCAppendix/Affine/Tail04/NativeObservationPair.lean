import FCAppendix.Affine.Tail04.NativePrivatePosterior
import FCAppendix.Affine.Tail04.CompletedNativePolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeObservationPair
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy
open OriginalPopulation OriginalValues NativePrivatePosterior
open scoped BigOperators

variable (E : Observable.Regions) {m c : ℕ}

def CompatibleEntry (a b : Option ℝ) : Prop :=
  (a=b ∧ (E.localTag a=0 ∨ E.localTag a=1)) ∨
  (E.localTag a=2 ∧ b=none) ∨ (a=none ∧ E.localTag b=2)

def Compatible (L K : LocalList m) : Prop := ∀ i,(CompatibleEntry E) (L i) (K i)

lemma measurableSet_compatible (L : LocalList m) :
    MeasurableSet {K : LocalList m | (Compatible E) L K} := by
  simp only [Compatible,Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hcommon : MeasurableSet {K : LocalList m | E.localTag (L i)=0 ∨ E.localTag (L i)=1} := by
    by_cases h : E.localTag (L i)=0 ∨ E.localTag (L i)=1 <;> simp [h]
  have hprivate : MeasurableSet {K : LocalList m | E.localTag (L i)=2} := by
    by_cases h : E.localTag (L i)=2 <;> simp [h]
  have hnone : MeasurableSet {K : LocalList m | L i=none} := by
    by_cases h : L i=none <;> simp [h]
  simp only [CompatibleEntry,Set.setOf_or,Set.setOf_and]
  exact ((measurableSet_eq_fun measurable_const (measurable_pi_apply i)).inter hcommon).union
    ((hprivate.inter (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)).union
      (hnone.inter (measurableSet_eq_fun (E.measurable_localTag.comp (measurable_pi_apply i)) measurable_const)))

lemma compatibleEntry_symm {a b : Option ℝ} (h : (CompatibleEntry E) a b) :
    (CompatibleEntry E) b a := by
  rcases h with ⟨he,ht⟩ | ⟨ht,he⟩ | ⟨he,ht⟩
  · exact Or.inl ⟨he.symm,he ▸ ht⟩
  · exact Or.inr (Or.inr ⟨he,ht⟩)
  · exact Or.inr (Or.inl ⟨ht,he⟩)

lemma compatible_symm {L K : LocalList m} (h : (Compatible E) L K) :
    (Compatible E) K L := fun i => (compatibleEntry_symm E) (h i)

lemma localTag_absent (a : Option ℝ) : E.localTag a=3 ↔ a=none := by
  cases a with
  | none => simp [Observable.Regions.localTag]
  | some b => by_cases hl : b≤ E.d <;> by_cases hp : b∈E.privateBids <;>
      simp [Observable.Regions.localTag,hl,hp]

lemma entry_common {a b : Option ℝ} (h : (CompatibleEntry E) a b)
    {k : Fin 4} (hk : k=0 ∨ k=1) (ha : E.localTag a=k) : a=b := by
  rcases h with ⟨he,_⟩ | ⟨ht,he⟩ | ⟨he,ht⟩
  · exact he
  · rcases hk with rfl | rfl <;> simp_all
  · subst a
    rcases hk with rfl | rfl <;> simp [Observable.Regions.localTag] at ha

lemma entry_common_tag {a b : Option ℝ} (h : (CompatibleEntry E) a b)
    {k : Fin 4} (hk : k=0 ∨ k=1) : E.localTag a=k ↔ E.localTag b=k := by
  constructor
  · intro ha; rw [←(entry_common E) h hk ha];exact ha
  · intro hb; rw [←(entry_common E) ((compatibleEntry_symm E) h) hk hb];exact hb

lemma entry_private_other_absent {a b : Option ℝ} (h : (CompatibleEntry E) a b) :
    E.localTag a=2 ↔ b=none := by
  rcases h with ⟨he,ht⟩ | ⟨ht,he⟩ | ⟨he,ht⟩
  · subst b
    rcases ht with ht | ht
    · have hn : a≠none := fun hn => by simp [hn,Observable.Regions.localTag] at ht
      simp [ht,hn]
    · have hn : a≠none := fun hn => by simp [hn,Observable.Regions.localTag] at ht
      simp [ht,hn]
  · simp [ht,he]
  · have hn : b≠none := fun hn => by simp [hn,Observable.Regions.localTag] at ht
    simp [he,Observable.Regions.localTag,hn]

lemma common_ids {L K : LocalList m} (h : (Compatible E) L K)
    {k : Fin 4} (hk : k=0 ∨ k=1) : ids E k L=ids E k K := by
  ext i
  simp only [ids,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (entry_common_tag E) (h i) hk

lemma common_entries {L K : LocalList m} (h : (Compatible E) L K)
    {k : Fin 4} (hk : k=0 ∨ k=1) : ∀ i∈ids E k L,L i=K i :=
  fun i hi => (entry_common E) (h i) hk (Finset.mem_filter.mp hi).2

lemma common_roleList {L K : LocalList m} (h : (Compatible E) L K)
    {k : Fin 4} (hk : k=0 ∨ k=1) : E.roleList k L=E.roleList k K := by
  funext i
  have ht := (entry_common_tag E) (h i) hk
  by_cases hi : E.localTag (L i)=k
  · simp only [Observable.Regions.roleList,if_pos hi,if_pos (ht.mp hi)]
    exact (entry_common E) (h i) hk hi
  · simp [Observable.Regions.roleList,hi,show E.localTag (K i)≠k from fun hh=> hi (ht.mpr hh)]

lemma private_ids_missing {L K : LocalList m} (h : (Compatible E) L K) :
    ids E 2 K=ids E 3 L := by
  ext i
  simp only [ids,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [(entry_private_other_absent E) ((compatibleEntry_symm E) (h i)),(localTag_absent E)]

lemma localCount_partition (L : LocalList m) :
    E.localCount L 0+E.localCount L 1+E.localCount L 2+E.localCount L 3=m := by
  simp only [Observable.Regions.localCount,←Finset.sum_add_distrib]
  calc
    (∑ i : Fin m,((if E.localTag (L i)=0 then 1 else 0)+
      (if E.localTag (L i)=1 then 1 else 0)+(if E.localTag (L i)=2 then 1 else 0)+
      (if E.localTag (L i)=3 then 1 else 0)))=∑ _i : Fin m,1 := by
        apply Finset.sum_congr rfl
        intro i _
        generalize E.localTag (L i)=k
        fin_cases k <;> decide
    _=m := by simp

lemma otherPrivateCount_eq_missing (L : LocalList m) :
    E.otherPrivateCount L=(ids E 3 L).card := by
  have hp := (localCount_partition E) L
  rw [ids_card]
  unfold Observable.Regions.otherPrivateCount
  omega

lemma otherPrivateCount_pair {L K : LocalList m} (h : (Compatible E) L K) :
    E.otherPrivateCount L=(ids E 2 K).card := by
  rw [(otherPrivateCount_eq_missing E),←(private_ids_missing E) h]

lemma common_count {L K : LocalList m} (h : (Compatible E) L K)
    {k : Fin 4} (hk : k=0 ∨ k=1) : E.localCount L k=E.localCount K k := by
  rw [←ids_card,←ids_card,(common_ids E) h hk]

lemma context_pair {L K : LocalList m} (h : (Compatible E) L K) (j : Fin 2) :
    E.context j L=E.context (Hybrid.otherProposer j) K := by
  have hlo := (common_roleList E) h (k:=0) (Or.inl rfl)
  have hac := (common_roleList E) h (k:=1) (Or.inr rfl)
  have hH0 := (otherPrivateCount_pair E) h
  have hH1 := (otherPrivateCount_pair E) ((compatible_symm E) h)
  rw [ids_card] at hH0 hH1
  fin_cases j <;> simp [Observable.Regions.context,Hybrid.otherProposer,hlo,hac,hH0,hH1]

lemma lowContext_pair {L K : LocalList m} (h : (Compatible E) L K) (j : Fin 2) :
    Observable.Regions.lowContext E j L=
      Observable.Regions.lowContext E (Hybrid.otherProposer j) K := by
  have hc := (common_count E) h (k:=1) (Or.inr rfl)
  simp only [Observable.Regions.lowContext,(context_pair E) h j,hc]

lemma activeBids_pair {L K : LocalList m} (h : (Compatible E) L K) :
    activeBids E (ids E 1 L) L=activeBids E (ids E 1 L) K := by
  have hb : ∀ i∈ids E 1 L,bidVector L i=bidVector K i :=
    fun i hi => congrArg entryBid ((common_entries E) h (Or.inr rfl) i hi)
  have he := enumerate_congr (ids E 1 L) (bidVector L) (bidVector K) hb
  funext a
  apply Subtype.ext
  simp only [activeBids,he]
  congr 1
  exact hb _ (enumerate (ids E 1 L) (bidVector K) a).2

lemma parameter_pair (D : Data m c) {L K : LocalList m} (h : (Compatible D.E) L K)
    (H0 H1 : Fin (m+1)) :
    D.parameter (ids D.E 1 L) H0 H1 L=D.parameter (ids D.E 1 L) H0 H1 K := by
  simp only [Data.parameter,(activeBids_pair D.E) h,
    (common_roleList D.E) h (k:=0) (Or.inl rfl)]

lemma key_pair (D : Data m c) {L K : LocalList m} (h : (Compatible D.E) L K) :
    key D.E K=((ids D.E 1 L,ids D.E 3 L),D.finiteCount (ids D.E 2 L)) := by
  have ha := ((common_ids D.E) h (k:=1) (Or.inr rfl)).symm
  have hp := (private_ids_missing D.E) h
  have hc : (key D.E K).2=D.finiteCount (ids D.E 2 L) := by
    apply Fin.ext
    exact (otherPrivateCount_pair D.E) ((compatible_symm D.E) h)
  exact Prod.ext (Prod.ext ha hp) hc

lemma key_self (D : Data m c) (L : LocalList m) :
    key D.E L=((ids D.E 1 L,ids D.E 2 L),D.finiteCount (ids D.E 3 L)) := by
  apply Prod.ext
  · rfl
  apply Fin.ext
  exact (otherPrivateCount_eq_missing D.E) L

lemma source_compatible (P : ValueParameters) (t : ℝ) (x : UserDraw 2)
    (hx : sourceBands P E t x.1) (j : Fin 2) :
    (CompatibleEntry E) (observedEntry j x) (observedEntry (Hybrid.otherProposer j) x) := by
  rcases hx with hx | hx | hx | hx
  · apply Or.inl
    simp [observedEntry,hx.2.2,Hybrid.firstK_full_two,Observable.Regions.localTag,hx.2.1]
  · have hp : x.1.2.bid∈E.privateBids := Or.inl hx.2.1
    have ht : E.localTag (some x.1.2.bid)=2 := by
      simp [Observable.Regions.localTag,not_le.mpr (E.private_above_low hp),hp]
    by_cases hj : j∈firstK x.2 1
    · have ho : Hybrid.otherProposer j∉firstK x.2 1 :=
        fun ho => (singleton_missing_iff_other x.2 j).mpr ho hj
      exact Or.inr (Or.inl (by simpa [observedEntry,hx.2.2,hj,ho] using ht))
    · have ho := (singleton_missing_iff_other x.2 j).mp hj
      exact Or.inr (Or.inr (by simpa [observedEntry,hx.2.2,hj,ho] using ht))
  · have hn : x.1.2.bid∉E.privateBids := by
      rintro (hh | hh)
      · linarith [hh.2,hx.2.1.1,E.Rp_lt_one]
      · have hh' : E.H ≤ x.1.2.bid := hh
        linarith [hh',hx.2.1.2,E.U_lt_H]
    have hl : ¬x.1.2.bid≤ E.d := by linarith [hx.2.1.1,E.d_lt_one]
    apply Or.inl
    simp [observedEntry,hx.2.2,Hybrid.firstK_full_two,Observable.Regions.localTag,hl,hn]
  · have hp : x.1.2.bid∈E.privateBids := Or.inr hx.2.1
    have ht : E.localTag (some x.1.2.bid)=2 := by
      simp [Observable.Regions.localTag,not_le.mpr (E.private_above_low hp),hp]
    by_cases hj : j∈firstK x.2 1
    · have ho : Hybrid.otherProposer j∉firstK x.2 1 :=
        fun ho => (singleton_missing_iff_other x.2 j).mpr ho hj
      exact Or.inr (Or.inl (by simpa [observedEntry,hx.2.2,hj,ho] using ht))
    · have ho := (singleton_missing_iff_other x.2 j).mp hj
      exact Or.inr (Or.inr (by simpa [observedEntry,hx.2.2,hj,ho] using ht))

lemma source_list_compatible (P : ValueParameters) (t : ℝ) (d : UserProfile m 2)
    (hd : ∀ i,sourceBands P E t (d i).1) (j : Fin 2) :
    (Compatible E) (observe (drawsRealization d) j)
      (observe (drawsRealization d) (Hybrid.otherProposer j)) :=
  fun i => (source_compatible E) P t (d i) (hd i) j

lemma source_active_box (P : ValueParameters) (t : ℝ) (x : UserDraw 2)
    (hx : sourceBands P E t x.1) (j : Fin 2)
    (ha : E.localTag (observedEntry j x)=1) :
    entryBid (observedEntry j x)∈Icc (1:ℝ) E.U := by
  have hj : j∈firstK x.2 x.1.2.routeCount := by
    by_contra hj
    simp [observedEntry,hj,Observable.Regions.localTag] at ha
  rw [observedEntry,if_pos hj]
  rcases hx with hx | hx | hx | hx
  · simp [observedEntry,hj,Observable.Regions.localTag,hx.2.1] at ha
  · have hp : x.1.2.bid∈E.privateBids := Or.inl hx.2.1
    simp [observedEntry,hj,Observable.Regions.localTag,
      not_le.mpr (E.private_above_low hp),hp] at ha
  · exact hx.2.1
  · have hp : x.1.2.bid∈E.privateBids := Or.inr hx.2.1
    simp [observedEntry,hj,Observable.Regions.localTag,
      not_le.mpr (E.private_above_low hp),hp] at ha

lemma source_on_menu (D : Data m c) (P : ValueParameters) (t : ℝ) (d : UserProfile m 2)
    (hd : ∀ i,sourceBands P D.E t (d i).1) (j : Fin 2) :
    D.offCommon (observe (drawsRealization d) j)=∅ := by
  apply (D.offCommon_eq_empty_iff _).mpr
  intro i hi
  exact (source_active_box D.E) P t (d i) (hd i) j hi

end FCAppendix.Affine.Tail04.NativeObservationPair

namespace FCAppendix.Affine.Tail04.Observable.Regions
abbrev CompatibleEntry := @FCAppendix.Affine.Tail04.NativeObservationPair.CompatibleEntry
abbrev Compatible := @FCAppendix.Affine.Tail04.NativeObservationPair.Compatible
abbrev measurableSet_compatible := @FCAppendix.Affine.Tail04.NativeObservationPair.measurableSet_compatible
abbrev compatibleEntry_symm := @FCAppendix.Affine.Tail04.NativeObservationPair.compatibleEntry_symm
abbrev compatible_symm := @FCAppendix.Affine.Tail04.NativeObservationPair.compatible_symm
abbrev localTag_absent := @FCAppendix.Affine.Tail04.NativeObservationPair.localTag_absent
abbrev entry_common := @FCAppendix.Affine.Tail04.NativeObservationPair.entry_common
abbrev entry_common_tag := @FCAppendix.Affine.Tail04.NativeObservationPair.entry_common_tag
abbrev entry_private_other_absent := @FCAppendix.Affine.Tail04.NativeObservationPair.entry_private_other_absent
abbrev common_ids := @FCAppendix.Affine.Tail04.NativeObservationPair.common_ids
abbrev common_entries := @FCAppendix.Affine.Tail04.NativeObservationPair.common_entries
abbrev private_ids_missing := @FCAppendix.Affine.Tail04.NativeObservationPair.private_ids_missing
abbrev localCount_partition := @FCAppendix.Affine.Tail04.NativeObservationPair.localCount_partition
abbrev otherPrivateCount_eq_missing := @FCAppendix.Affine.Tail04.NativeObservationPair.otherPrivateCount_eq_missing
abbrev otherPrivateCount_pair := @FCAppendix.Affine.Tail04.NativeObservationPair.otherPrivateCount_pair
abbrev common_count := @FCAppendix.Affine.Tail04.NativeObservationPair.common_count
abbrev context_pair := @FCAppendix.Affine.Tail04.NativeObservationPair.context_pair
abbrev lowContext_pair := @FCAppendix.Affine.Tail04.NativeObservationPair.lowContext_pair
abbrev activeBids_pair := @FCAppendix.Affine.Tail04.NativeObservationPair.activeBids_pair
abbrev source_compatible := @FCAppendix.Affine.Tail04.NativeObservationPair.source_compatible
abbrev source_list_compatible := @FCAppendix.Affine.Tail04.NativeObservationPair.source_list_compatible
abbrev source_active_box := @FCAppendix.Affine.Tail04.NativeObservationPair.source_active_box
end FCAppendix.Affine.Tail04.Observable.Regions

namespace FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
abbrev parameter_pair := @FCAppendix.Affine.Tail04.NativeObservationPair.parameter_pair
abbrev key_pair := @FCAppendix.Affine.Tail04.NativeObservationPair.key_pair
abbrev key_self := @FCAppendix.Affine.Tail04.NativeObservationPair.key_self
abbrev source_on_menu := @FCAppendix.Affine.Tail04.NativeObservationPair.source_on_menu
end FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
