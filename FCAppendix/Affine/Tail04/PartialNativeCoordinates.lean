import FCAppendix.Affine.Tail04.NativeMenuReports
import FCAppendix.Affine.Tail04.NativePartialDeviation
import FCAppendix.Affine.Tail04.ObservedScenario
import FCAppendix.Affine.Tail04.OriginalCommonLaw
import FCAppendix.Affine.Tail04.PartialFocalGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialNativeCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeMenuReports NativePrivatePosterior NativeObservationPair
open LocalCoordinates SortedCoordinates OriginalPopulation OriginalValues Hybrid
open scoped BigOperators

variable (E : Observable.Regions)

lemma menu_private_route (x : UserDraw 2) (hx : MenuAction E x.1.2)
    (hp : x.1.2.bid∈E.privateBids) : x.1.2.routeCount=1 := by
  rcases hx with ⟨hl | ha,hk⟩ | ⟨_,hk⟩
  · exact False.elim ((not_lt.mpr hl) (E.private_above_low hp))
  · rcases hp with hp | hp
    · exact False.elim ((not_le.mpr E.Rp_lt_one) (ha.1.trans hp.2))
    · exact False.elim ((not_le.mpr E.U_lt_H) (hp.trans ha.2))
  · exact hk

lemma menu_common_route (x : UserDraw 2) (hx : MenuAction E x.1.2)
    (hp : x.1.2.bid∉E.privateBids) : x.1.2.routeCount=2 := by
  rcases hx with ⟨_,hk⟩ | ⟨hh,_⟩
  · exact hk
  · exact False.elim (hp hh)

lemma observed_private_tag (x : UserDraw 2) (hx : MenuAction E x.1.2) (j : Fin 2) :
    E.localTag (observedEntry j x)=2 ↔ E.coarseTag x=NativeContinuation.upperTag j := by
  have he := Set.ext_iff.mp (OriginalPrivateEntry.private_tag_event E j) x
  change (E.coarseTag x=NativeContinuation.upperTag j ↔
    x.1.2.bid∈E.privateBids ∧ j∈firstK x.2 1) at he
  rw [he]
  by_cases hp : x.1.2.bid∈E.privateBids
  · have hk := menu_private_route E x hx hp
    have hl := not_le.mpr (E.private_above_low hp)
    by_cases hj : j∈firstK x.2 1 <;>
      simp [observedEntry,hk,hj,Observable.Regions.localTag,hl,hp]
  · by_cases hj : j∈firstK x.2 x.1.2.routeCount
    · by_cases hl : x.1.2.bid≤ E.d <;>
        simp [observedEntry,hj,Observable.Regions.localTag,hl,hp]
    · simp [observedEntry,hj,Observable.Regions.localTag,hp]

lemma observed_absent_tag (x : UserDraw 2) (hx : MenuAction E x.1.2) (j : Fin 2) :
    E.localTag (observedEntry j x)=3 ↔
      E.coarseTag x=NativeContinuation.upperTag (otherProposer j) := by
  rw [E.localTag_absent]
  have h := E.entry_private_other_absent (menu_compatible E x hx (otherProposer j))
  simp only [otherProposer_other] at h
  exact h.symm.trans (observed_private_tag E x hx (otherProposer j))

lemma observed_low_tag (x : UserDraw 2) (hx : MenuAction E x.1.2) (j : Fin 2) :
    E.localTag (observedEntry j x)=0 ↔ E.coarseTag x=0 := by
  rw [ObservedScenario.coarseTag_low_iff E x]
  by_cases hl : x.1.2.bid≤ E.d
  · have hp : x.1.2.bid∉E.privateBids :=
      fun hp => (not_lt.mpr hl) (E.private_above_low hp)
    have hk := menu_common_route E x hx hp
    simp [observedEntry,hk,firstK_full_two,Observable.Regions.localTag,hl]
  · by_cases hj : j∈firstK x.2 x.1.2.routeCount
    · by_cases hp : x.1.2.bid∈E.privateBids <;>
        simp [observedEntry,hj,Observable.Regions.localTag,hl,hp]
    · simp [observedEntry,hj,Observable.Regions.localTag,hl]

lemma observed_active_tag (x : UserDraw 2) (hx : MenuAction E x.1.2) (j : Fin 2) :
    E.localTag (observedEntry j x)=1 ↔ E.coarseTag x=1 := by
  have he := Set.ext_iff.mp (OriginalCommonLaw.coarse_common_event E) x
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_prod,OriginalCommonLaw.event,Set.mem_setOf_eq,Set.mem_univ,and_true] at he
  rw [he]
  by_cases hl : x.1.2.bid≤ E.d
  · by_cases hj : j∈firstK x.2 x.1.2.routeCount <;>
      simp [observedEntry,hj,Observable.Regions.localTag,hl,not_lt.mpr hl]
  · by_cases hp : x.1.2.bid∈E.privateBids
    · by_cases hj : j∈firstK x.2 x.1.2.routeCount <;>
        simp [observedEntry,hj,Observable.Regions.localTag,hl,hp]
    · have hk := menu_common_route E x hx hp
      simp [observedEntry,hk,firstK_full_two,Observable.Regions.localTag,hl,hp,lt_of_not_ge hl]

section Focal
variable {N c : ℕ} {Seed : Type*}

def rivalKinds (i : Fin (N+1)) (ω : Background (N+1) 2 Seed) : Fin N→ Fin 4 :=
  fun r => E.coarseTag (ω.1 (i.succAbove r))

lemma measurable_rivalKinds [MeasurableSpace Seed] (i : Fin (N+1)) : Measurable (rivalKinds E (Seed:=Seed) i) :=
  measurable_pi_lambda _ (fun r => E.measurable_coarseTag.comp
    ((measurable_pi_apply (i.succAbove r)).comp measurable_fst))

lemma present_other_observed (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
    (b : ℝ) (j : Fin 2) (r : Fin N) :
    presentList ω i b j (i.succAbove r)=observedEntry j (ω.1 (i.succAbove r)) := by
  rw [presentList_other ω i _ (Fin.succAbove_ne i r) b j]
  rfl

def rivalSet (i : Fin (N+1)) (kind : Fin N→ Fin 4) (k : Fin 4) : Finset (Fin (N+1)) :=
  (Finset.univ.filter fun r => kind r=k).image i.succAbove

lemma focal_not_mem_rivalSet (i : Fin (N+1)) (kind : Fin N→ Fin 4) (k : Fin 4) :
    i∉rivalSet i kind k := by
  simp only [rivalSet,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    not_exists,not_and]
  exact fun r _ => Fin.succAbove_ne i r

lemma mem_rivalSet_succAbove (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (k : Fin 4) (r : Fin N) : i.succAbove r∈rivalSet i kind k ↔ kind r=k := by
  constructor
  · rintro h
    obtain ⟨s,hs,he⟩ := Finset.mem_image.mp h
    have hsr : s=r := Fin.succAbove_right_injective he
    simpa only [hsr,Finset.mem_filter,Finset.mem_univ,true_and] using hs
  · intro h
    exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ r,h⟩,rfl⟩

lemma rivalSet_card (i : Fin (N+1)) (kind : Fin N→ Fin 4) (k : Fin 4) :
    (rivalSet i kind k).card=categoryCount k kind := by
  rw [rivalSet,Finset.card_image_of_injective _ Fin.succAbove_right_injective]
  simp only [categoryCount,LowBody.hitCount,Finset.card_filter]
  exact Finset.sum_congr rfl (fun _ _ => by split_ifs <;> rfl)

lemma rivalSet_card_filter (i : Fin (N+1)) (kind : Fin N→ Fin 4) (k : Fin 4) :
    (rivalSet i kind k).card=(Finset.univ.filter fun r : Fin N => kind r=k).card := by
  exact Finset.card_image_of_injective _ Fin.succAbove_right_injective

lemma rivalSet_card_subtype (i : Fin (N+1)) (kind : Fin N→ Fin 4) (k : Fin 4) :
    (rivalSet i kind k).card=Fintype.card {r : Fin N // kind r=k} := by
  rw [rivalSet_card_filter]
  simp only [Fintype.card_subtype]

def rivalSetEquiv (i : Fin (N+1)) (kind : Fin N→ Fin 4) (k : Fin 4) :
    {r : Fin N // kind r=k} ≃ {l : Fin (N+1) // l∈rivalSet i kind k} where
  toFun r := ⟨i.succAbove r.val,(mem_rivalSet_succAbove i kind k r.val).mpr r.property⟩
  invFun l := by
    have hl : l.val≠i := fun he => focal_not_mem_rivalSet i kind k (by simpa only [he] using l.property)
    let r := Classical.choose (Fin.exists_succAbove_eq hl)
    have hr : i.succAbove r=l.val := Classical.choose_spec (Fin.exists_succAbove_eq hl)
    exact ⟨r,(mem_rivalSet_succAbove i kind k r).mp (hr.symm ▸ l.property)⟩
  left_inv r := by
    apply Subtype.ext
    apply Fin.succAbove_right_injective
    exact Classical.choose_spec (Fin.exists_succAbove_eq (Fin.succAbove_ne i r.val))
  right_inv l := by
    apply Subtype.ext
    exact Classical.choose_spec (Fin.exists_succAbove_eq
      (fun he => focal_not_mem_rivalSet i kind k (by simpa only [he] using l.property)))

theorem present_count (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
    (b : ℝ) (j : Fin 2) (k : Fin 4) :
    E.localCount (presentList ω i b j) k=
      (if E.localTag (some b)=k then 1 else 0)+
        ∑ r : Fin N,if E.localTag (observedEntry j (ω.1 (i.succAbove r)))=k then 1 else 0 := by
  unfold Observable.Regions.localCount
  rw [Fin.sum_univ_succAbove _ i,presentList_self]
  simp_rw [present_other_observed]

variable (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
    (hr : ∀ r : Fin N,MenuAction E (ω.1 (i.succAbove r)).1.2)

include hr in
theorem partial_ids (b : Icc E.R E.Rp) (j : Fin 2) :
    ids E 0 (presentList ω i b j)=rivalSet i (rivalKinds E i ω) 0 ∧
    ids E 1 (presentList ω i b j)=rivalSet i (rivalKinds E i ω) 1 ∧
    ids E 2 (presentList ω i b j)=insert i
      (rivalSet i (rivalKinds E i ω) (NativeContinuation.upperTag j)) ∧
    ids E 3 (presentList ω i b j)=
      rivalSet i (rivalKinds E i ω) (NativeContinuation.upperTag (otherProposer j)) := by
  have hb : E.localTag (some (b:ℝ))=2 := by
    simp [Observable.Regions.localTag,
      not_le.mpr (E.private_above_low (Or.inl b.2)),show (b:ℝ)∈E.privateBids from Or.inl b.2]
  have hf (k : Fin 4) := focal_not_mem_rivalSet i (rivalKinds E i ω) k
  refine ⟨?_,?_,?_,?_⟩ <;> ext l <;> by_cases hl : l=i
  all_goals try { subst l; simp [ids,presentList_self,hb,hf] }
  all_goals obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_low_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_active_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      Finset.mem_insert,Fin.succAbove_ne,false_or,mem_rivalSet_succAbove,rivalKinds] using
      observed_private_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_absent_tag E _ (hr r) j

include hr in
theorem active_ids (b : Icc (1:ℝ) E.U) (j : Fin 2) :
    ids E 0 (presentList ω i b j)=rivalSet i (rivalKinds E i ω) 0 ∧
    ids E 1 (presentList ω i b j)=insert i (rivalSet i (rivalKinds E i ω) 1) ∧
    ids E 2 (presentList ω i b j)=
      rivalSet i (rivalKinds E i ω) (NativeContinuation.upperTag j) ∧
    ids E 3 (presentList ω i b j)=
      rivalSet i (rivalKinds E i ω) (NativeContinuation.upperTag (otherProposer j)) := by
  have hb := tag_common E b.2
  have hf (k : Fin 4) := focal_not_mem_rivalSet i (rivalKinds E i ω) k
  refine ⟨?_,?_,?_,?_⟩ <;> ext l <;> by_cases hl : l=i
  all_goals try { subst l; simp [ids,presentList_self,hb,hf] }
  all_goals obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_low_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      Finset.mem_insert,Fin.succAbove_ne,false_or,mem_rivalSet_succAbove,rivalKinds] using
      observed_active_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_private_tag E _ (hr r) j
  · simpa only [ids,Finset.mem_filter,Finset.mem_univ,true_and,present_other_observed,
      mem_rivalSet_succAbove,rivalKinds] using observed_absent_tag E _ (hr r) j

include hr in
theorem partial_counts (b : Icc E.R E.Rp) (j : Fin 2) :
    E.localCount (presentList ω i b j) 0=categoryCount 0 (rivalKinds E i ω) ∧
    E.localCount (presentList ω i b j) 1=categoryCount 1 (rivalKinds E i ω) ∧
    E.localCount (presentList ω i b j) 2=
      categoryCount (NativeContinuation.upperTag j) (rivalKinds E i ω)+1 ∧
    E.localCount (presentList ω i b j) 3=
      categoryCount (NativeContinuation.upperTag (otherProposer j)) (rivalKinds E i ω) := by
  obtain ⟨h0,h1,h2,h3⟩ := partial_ids E i ω hr b j
  simp only [←ids_card,h0,h1,h2,h3,
    Finset.card_insert_of_notMem (focal_not_mem_rivalSet i (rivalKinds E i ω)
      (NativeContinuation.upperTag j)),rivalSet_card]
  exact ⟨trivial,trivial,trivial,trivial⟩

def orderedCounts (D : Data (N+1) c) (j : Fin 2) (L : LocalList (N+1)) : ℕ×ℕ :=
  if j=0 then ((ids D.E 2 L).card,(ids D.E 3 L).card)
  else ((ids D.E 3 L).card,(ids D.E 2 L).card)

include hr in
theorem partial_orderedCounts (D : Data (N+1) c) (hE : D.E=E)
    (b : Icc E.R E.Rp) (j : Fin 2) :
    orderedCounts D j (presentList ω i b j)=
      (categoryCount 2 (rivalKinds E i ω)+MenuError.partialOffset j 0,
       categoryCount 3 (rivalKinds E i ω)+MenuError.partialOffset j 1) := by
  fin_cases j
  · have h := partial_counts E i ω hr b 0
    change ((ids D.E 2 _).card,(ids D.E 3 _).card)=_
    apply Prod.ext
    · simpa only [hE,ids_card,NativeContinuation.upperTag,MenuError.partialOffset]
        using! h.2.2.1
    · simpa only [hE,ids_card,NativeContinuation.upperTag,otherProposer,
        MenuError.partialOffset,Nat.add_zero,if_pos,if_neg] using! h.2.2.2
  · have h := partial_counts E i ω hr b 1
    change ((ids D.E 3 _).card,(ids D.E 2 _).card)=_
    apply Prod.ext
    · simpa only [hE,ids_card,NativeContinuation.upperTag,otherProposer,
        MenuError.partialOffset,Nat.add_zero,if_pos,if_neg] using! h.2.2.2
    · simpa only [hE,ids_card,NativeContinuation.upperTag,MenuError.partialOffset]
        using! h.2.2.1

include hr in
theorem partial_private_tie_iff (D : Data (N+1) c) (hE : D.E=E)
    (b : Icc E.R E.Rp) (j : Fin 2) :
    (ids D.E 2 (presentList ω i b j)).card=(ids D.E 3 (presentList ω i b j)).card ↔
      categoryCount 2 (rivalKinds E i ω)+MenuError.partialOffset j 0=
        categoryCount 3 (rivalKinds E i ω)+MenuError.partialOffset j 1 := by
  have h := partial_orderedCounts E i ω hr D hE b j
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  fin_cases j <;> simp only [orderedCounts] at h0 h1 <;> simp_all [eq_comm]

include hr in
theorem common_roleList (b : Icc E.R E.Rp) (j : Fin 2) (k : Fin 4) (hk : k=0 ∨ k=1) :
    E.roleList k (presentList ω i b j)=E.roleList k (presentList ω i b (otherProposer j)) := by
  funext l
  by_cases hl : l=i
  · subst l
    have hb : E.localTag (some (b:ℝ))=2 := by
      simp [Observable.Regions.localTag,
        not_le.mpr (E.private_above_low (Or.inl b.2)),show (b:ℝ)∈E.privateBids from Or.inl b.2]
    simp only [Observable.Regions.roleList,presentList_self,hb]
  · obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
    simp only [Observable.Regions.roleList,present_other_observed]
    have hc := menu_compatible E (ω.1 (i.succAbove r)) (hr r) j
    have ht := E.entry_common_tag hc hk
    by_cases htag : E.localTag (observedEntry j (ω.1 (i.succAbove r)))=k
    · simp only [if_pos htag,if_pos (ht.mp htag)]
      exact E.entry_common hc hk htag
    · simp only [if_neg htag,if_neg (fun hh => htag (ht.mpr hh))]

include hr in
theorem low_list_deleted (b : Icc E.R E.Rp) (j : Fin 2) :
    E.roleList 0 (presentList ω i b j)=
      fun l => if l=i then none else
        if E.coarseTag (ω.1 l)=0 then some (ω.1 l).1.2.bid else none := by
  funext l
  by_cases hl : l=i
  · subst l
    have hb : ¬(b:ℝ)≤ E.d := not_le.mpr (E.d_lt_R.trans_le b.2.1)
    simp [Observable.Regions.roleList,presentList_self,Observable.Regions.localTag,hb,
      show (b:ℝ)∈E.privateBids from Or.inl b.2]
  · obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
    have ht := observed_low_tag E _ (hr r) j
    have hn := Fin.succAbove_ne i r
    simp only [if_neg hn,Observable.Regions.roleList,present_other_observed,ht]
    by_cases h0 : E.coarseTag (ω.1 (i.succAbove r))=0
    · have hl0 := (ObservedScenario.coarseTag_low_iff E _).mp h0
      have hp : (ω.1 (i.succAbove r)).1.2.bid∉E.privateBids :=
        fun hp => (not_lt.mpr hl0) (E.private_above_low hp)
      have hk := menu_common_route E _ (hr r) hp
      simp [h0,observedEntry,hk,firstK_full_two]
    · simp [h0]

include hr in
theorem low_list_rivalSet (b : Icc E.R E.Rp) (j : Fin 2) :
    E.roleList 0 (presentList ω i b j)=fun l =>
      if l∈rivalSet i (rivalKinds E i ω) 0 then some (ω.1 l).1.2.bid else none := by
  rw [low_list_deleted E i ω hr b j]
  funext l
  by_cases hl : l=i
  · subst l
    simp [focal_not_mem_rivalSet]
  · obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
    simp [Fin.succAbove_ne,mem_rivalSet_succAbove,rivalKinds]

include hr in
theorem low_seed_enumeration (b : Icc E.R E.Rp) (j : Fin 2) (μL : Measure ℝ)
    (n : ℕ) (e : Fin (n+1) ≃ {r : Fin N // rivalKinds E i ω r=0}) :
    Hybrid.seedOnList μL (E.roleList 0 (presentList ω i b j))=
      some (conditionalMinimumSeed μL n
        (fun l => (ω.1 (i.succAbove (e l).val)).1.2.bid)) := by
  have h := Hybrid.seedOnList_enumeration μL
    (fun l => l∈rivalSet i (rivalKinds E i ω) 0)
    (e.trans (rivalSetEquiv i (rivalKinds E i ω) 0))
    (fun l => (ω.1 l).1.2.bid) (E.roleList 0 (presentList ω i b j))
    (fun l => congrFun (low_list_rivalSet E i ω hr b j) l)
  exact h

include hr in
theorem no_low_seed (b : Icc E.R E.Rp) (j : Fin 2) (μL : Measure ℝ)
    (hl : ∀ r : Fin N,rivalKinds E i ω r≠0) :
    Hybrid.seedOnList μL (E.roleList 0 (presentList ω i b j))=none := by
  have he : rivalSet i (rivalKinds E i ω) 0=∅ := by
    simp only [rivalSet]
    have hf : (Finset.univ.filter fun r => rivalKinds E i ω r=0)=∅ := by
      ext r
      simp [hl r]
    rw [hf,Finset.image_empty]
  rw [low_list_rivalSet E i ω hr b j,he]
  simp

lemma low_roleList_change_nonlow (b b' : ℝ) (hb : E.localTag (some b)≠0)
    (hb' : E.localTag (some b')≠0) (j : Fin 2) :
    E.roleList 0 (presentList ω i b j)=E.roleList 0 (presentList ω i b' j) := by
  funext l
  by_cases hl : l=i
  · subst l
    simp only [Observable.Regions.roleList,presentList_self,if_neg hb,if_neg hb']
  · simp only [Observable.Regions.roleList,presentList,if_neg hl]

include hr in
theorem active_low_seed_enumeration (b : Icc (1:ℝ) E.U) (j : Fin 2) (μL : Measure ℝ)
    (n : ℕ) (e : Fin (n+1) ≃ {r : Fin N // rivalKinds E i ω r=0}) :
    Hybrid.seedOnList μL (E.roleList 0 (presentList ω i b j))=
      some (conditionalMinimumSeed μL n
        (fun l => (ω.1 (i.succAbove (e l).val)).1.2.bid)) := by
  let r : Icc E.R E.Rp := ⟨E.R,le_rfl,E.R_le_Rp⟩
  have hb : E.localTag (some (b:ℝ))≠0 := by rw [tag_common E b.2];decide
  have hr0 : E.localTag (some (r:ℝ))≠0 := by
    simp [r,Observable.Regions.localTag,not_le.mpr E.d_lt_R,
      show E.R∈E.privateBids from Or.inl ⟨le_rfl,E.R_le_Rp⟩]
  rw [low_roleList_change_nonlow E i ω b r hb hr0 j]
  exact low_seed_enumeration E i ω hr r j μL n e

include hr in
theorem active_no_low_seed (b : Icc (1:ℝ) E.U) (j : Fin 2) (μL : Measure ℝ)
    (hl : ∀ r : Fin N,rivalKinds E i ω r≠0) :
    Hybrid.seedOnList μL (E.roleList 0 (presentList ω i b j))=none := by
  let r : Icc E.R E.Rp := ⟨E.R,le_rfl,E.R_le_Rp⟩
  have hb : E.localTag (some (b:ℝ))≠0 := by rw [tag_common E b.2];decide
  have hr0 : E.localTag (some (r:ℝ))≠0 := by
    simp [r,Observable.Regions.localTag,not_le.mpr E.d_lt_R,
      show E.R∈E.privateBids from Or.inl ⟨le_rfl,E.R_le_Rp⟩]
  rw [low_roleList_change_nonlow E i ω b r hb hr0 j]
  exact no_low_seed E i ω hr r j μL hl

include hr in
theorem partial_on_menu (D : Data (N+1) c) (hE : D.E=E)
    (b : Icc E.R E.Rp) (j : Fin 2) : D.offCommon (presentList ω i b j)=∅ := by
  apply (D.offCommon_eq_empty_iff _).mpr
  intro l hl
  by_cases hli : l=i
  · subst l
    have hp : (b:ℝ)∈E.privateBids := Or.inl b.2
    simp [hE,presentList_self,Observable.Regions.localTag,not_le.mpr (E.private_above_low hp),hp] at hl
  · obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hli
    rw [hE,present_other_observed] at hl ⊢
    exact menu_active_box E _ (hr r) j hl

end Focal
end FCAppendix.Affine.Tail04.PartialNativeCoordinates
