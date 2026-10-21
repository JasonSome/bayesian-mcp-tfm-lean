import FCAppendix.Affine.Tail04.NativeFocalCoordinates
import FCAppendix.Affine.Tail04.NativeSamplerCountLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeMenuReports
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativePrivatePosterior NativeObservationPair
open NativeCountCoordinates NativeFocalCoordinates LocalCoordinates SortedCoordinates
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy LocalHighCommon
open OriginalValues OriginalPopulation Hybrid

variable {m c : ℕ} (E : Observable.Regions)

def MenuAction (a : JointAction 2) : Prop :=
  ((a.bid≤ E.d ∨ a.bid∈Icc (1:ℝ) E.U) ∧ a.routeCount=2) ∨
    (a.bid∈E.privateBids ∧ a.routeCount=1)

lemma source_menu (P : ValueParameters) (t : ℝ) (x : ℝ×JointAction 2)
    (hx : sourceBands P E t x) : MenuAction E x.2 := by
  rcases hx with hx | hx | hx | hx
  · exact Or.inl ⟨Or.inl hx.2.1,hx.2.2⟩
  · exact Or.inr ⟨Or.inl hx.2.1,hx.2.2⟩
  · exact Or.inl ⟨Or.inr hx.2.1,hx.2.2⟩
  · exact Or.inr ⟨Or.inr hx.2.1,hx.2.2⟩

lemma tag_common {b : ℝ} (hb : b∈Icc (1:ℝ) E.U) : E.localTag (some b)=1 := by
  have hd : ¬b≤ E.d := not_le.mpr (E.d_lt_one.trans_le hb.1)
  have hp : b∉E.privateBids := by
    rintro (h | h)
    · exact not_le_of_gt E.Rp_lt_one (hb.1.trans h.2)
    · exact not_le_of_gt E.U_lt_H (h.trans hb.2)
  simp [Observable.Regions.localTag,hd,hp]

lemma menu_compatible (x : UserDraw 2) (hx : MenuAction E x.1.2) (j : Fin 2) :
    E.CompatibleEntry (observedEntry j x) (observedEntry (otherProposer j) x) := by
  rcases hx with ⟨hl | ha,hk⟩ | ⟨hp,hk⟩
  · apply Or.inl
    simp [observedEntry,hk,firstK_full_two,Observable.Regions.localTag,hl]
  · apply Or.inl
    simp [observedEntry,hk,firstK_full_two,tag_common E ha]
  · have ht : E.localTag (some x.1.2.bid)=2 := by
      simp [Observable.Regions.localTag,not_le.mpr (E.private_above_low hp),hp]
    by_cases hj : j∈firstK x.2 1
    · have ho : otherProposer j∉firstK x.2 1 :=
        fun ho => (singleton_missing_iff_other x.2 j).mpr ho hj
      exact Or.inr (Or.inl (by simp [observedEntry,hk,hj,ho,ht]))
    · have ho := (singleton_missing_iff_other x.2 j).mp hj
      exact Or.inr (Or.inr (by simp [observedEntry,hk,hj,ho,ht]))

lemma menu_active_box (x : UserDraw 2) (hx : MenuAction E x.1.2) (j : Fin 2)
    (ha : E.localTag (observedEntry j x)=1) :
    entryBid (observedEntry j x)∈Icc (1:ℝ) E.U := by
  have hj : j∈firstK x.2 x.1.2.routeCount := by
    by_contra hj
    simp [observedEntry,hj,Observable.Regions.localTag] at ha
  rcases hx with ⟨hl | hb,hk⟩ | ⟨hp,hk⟩
  · simp [observedEntry,hj,Observable.Regions.localTag,hl] at ha
  · simpa [observedEntry,hj,entryBid] using hb
  · simp [observedEntry,hj,Observable.Regions.localTag,
      not_le.mpr (E.private_above_low hp),hp] at ha

section Deviation
variable {Seed : Type*}

def deviationDraws (i : Fin m) (a : JointAction 2) (ω : Sample m 2 Seed) : UserProfile m 2 :=
  Function.update ω.1.1 i ((0,a),ω.2)

lemma observe_deviationDraws (i : Fin m) (a : JointAction 2) (ω : Sample m 2 Seed) (j : Fin 2) :
    observe (drawsRealization (deviationDraws i a ω)) j=observe (deviated i a ω) j := by
  funext k
  by_cases hk : k=i
  · subst k
    simp only [observe,drawsRealization,deviationDraws,Function.update_self,
      deviated_recipients_self,deviated_bid_self]
  · simp only [observe,drawsRealization,deviationDraws,Function.update_of_ne hk,
      deviated_recipients_other i k hk,deviated_bid_other i k hk]

lemma deviationDraws_menu (i : Fin m) (a : JointAction 2) (ω : Sample m 2 Seed)
    (ha : MenuAction E a) (hr : ∀ k,k≠i → MenuAction E (ω.1.1 k).1.2) :
    ∀ k,MenuAction E (deviationDraws i a ω k).1.2 := by
  intro k
  by_cases hk : k=i
  · simpa [deviationDraws,hk] using ha
  · simpa [deviationDraws,Function.update_of_ne hk] using hr k hk

theorem compatible_deviation (i : Fin m) (a : JointAction 2) (ω : Sample m 2 Seed)
    (ha : MenuAction E a) (hr : ∀ k,k≠i → MenuAction E (ω.1.1 k).1.2) :
    E.Compatible (observe (deviated i a ω) 0) (observe (deviated i a ω) 1) := by
  rw [←observe_deviationDraws i a ω 0,←observe_deviationDraws i a ω 1]
  intro k
  simpa [otherProposer,observedEntry,observe,drawsRealization] using
    menu_compatible E (deviationDraws i a ω k) (deviationDraws_menu E i a ω ha hr k) 0

end Deviation

variable (D : NativeLocalPolicy.Data m c)

theorem onMenu_deviation {Seed : Type*} (i : Fin m) (a : JointAction 2) (ω : Sample m 2 Seed)
    (ha : MenuAction D.E a) (hr : ∀ k,k≠i → MenuAction D.E (ω.1.1 k).1.2) (j : Fin 2) :
    D.offCommon (observe (deviated i a ω) j)=∅ := by
  rw [←observe_deviationDraws i a ω j]
  apply (D.offCommon_eq_empty_iff _).mpr
  intro k hk
  exact menu_active_box D.E (deviationDraws i a ω k)
    (deviationDraws_menu D.E i a ω ha hr k) j hk

lemma active_report_menu (b : Icc (1:ℝ) D.E.U) :
    MenuAction D.E (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2) :=
  Or.inl ⟨Or.inr b.2,rfl⟩

lemma private_report_menu (b : ℝ) (hb : b∈D.E.privateBids) :
    MenuAction D.E (RawRoutes.action b
      (D.E.d_nonneg.trans (D.E.private_above_low hb).le) 1) :=
  Or.inr ⟨hb,rfl⟩

lemma active_focal_present {Seed : Type*} (i : Fin m) (b : Icc (1:ℝ) D.E.U) (ω : Sample m 2 Seed)
    (j : Fin 2) :
    i∈ids D.E 1 (observe (deviated i
      (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2) ω) j) := by
  have ho : observe (deviated i
      (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2) ω) j i=some (b:ℝ) := by
    simp only [observe,deviated_recipients_self,deviated_bid_self]
    change (if j ∈ firstK ω.2 2 then some (b : ℝ) else none) = some (b : ℝ)
    simp only [firstK_full_two,Finset.mem_univ,if_pos]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,by rw [ho];exact tag_common D.E b.2⟩

theorem native_active_focal_count (P : ValueParameters) (t : ℝ)
    (Γ : FiniteGame m 2 c NativeLocalPolicy.Seed)
    (hpolicy : Γ.policy=D.completedPolicy) (i : Fin m) (b : Icc (1:ℝ) D.E.U)
    (ω : Sample m 2 NativeLocalPolicy.Seed)
    (hr : ∀ k,k≠i → sourceBands P D.E t (ω.1.1 k).1) :
    let a := RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2
    let x := deviated i a ω
    let L := observe x 0
    let hi := active_focal_present D i b ω 0
    focalCount Γ i a ω=
      originalPairCount
        (D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)))
        (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
          (D.finiteCount (ids D.E 3 L)) L)
        (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
        (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
        ((privateRow D.E (ids D.E 2 L) L,(ω.1.2 0).1),
          (privateRow D.E (ids D.E 3 L) (observe x 1),(ω.1.2 1).1)) := by
  dsimp only
  change Game.boundedCount _ Γ.policy _ _=_
  rw [hpolicy]
  exact native_common_count D _
    (compatible_deviation D.E i _ ω (active_report_menu D b)
      (fun k hk => source_menu D.E P t _ (hr k hk)))
    (onMenu_deviation D i _ ω (active_report_menu D b)
      (fun k hk => source_menu D.E P t _ (hr k hk)))
    ω.1.2 i (active_focal_present D i b ω 0)

lemma partial_present_ids {Seed : Type*} (i : Fin m) (b : Icc D.E.R D.E.Rp)
    (ω : Background m 2 Seed) (j : Fin 2) :
    i∈ids D.E 2 (presentList ω i b j) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ i,by rw [presentList_self];exact PrivateUpdate.tag_partial D b.2⟩

theorem onMenu_present_partial {Seed : Type*} (P : ValueParameters) (t : ℝ)
    (i : Fin m) (b : Icc D.E.R D.E.Rp) (ω : Background m 2 Seed)
    (hr : ∀ k,k≠i → sourceBands P D.E t (ω.1 k).1) (j : Fin 2) :
    D.offCommon (presentList ω i b j)=∅ := by
  apply (D.offCommon_eq_empty_iff _).mpr
  intro k hk
  by_cases hki : k=i
  · subst k
    rw [presentList_self,PrivateUpdate.tag_partial D b.2] at hk
    exact (by decide : (2:Fin 4)≠1) hk |>.elim
  · have ho : presentList ω i b j k=observedEntry j (ω.1 k) :=
      presentList_other ω i k hki b j
    rw [ho] at hk ⊢
    exact D.E.source_active_box P t (ω.1 k) (hr k hki) j hk

def privateZeroAccept (i : Fin m) (b : Icc D.E.R D.E.Rp)
    (ω : Background m 2 NativeLocalPolicy.Seed) : Bool :=
  let L := presentList ω i b 0
  decide (Sum.inr (rankFin (ids D.E 2 L) (privateKey D.E L)
    ⟨i,partial_present_ids D i b ω 0⟩)∈
    D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
      (D.finiteCount (ids D.E 3 L))
      (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 3 L)) L,privateRow D.E (ids D.E 2 L) L) (ω.2 0).1)

def privateOneAccept (i : Fin m) (b : Icc D.E.R D.E.Rp)
    (ω : Background m 2 NativeLocalPolicy.Seed) : Bool :=
  let L := presentList ω i b 1
  decide (Sum.inr (rankFin (ids D.E 2 L) (privateKey D.E L)
    ⟨i,partial_present_ids D i b ω 1⟩)∈
    D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 3 L))
      (D.finiteCount (ids D.E 2 L))
      (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 3 L))
        (D.finiteCount (ids D.E 2 L)) L,privateRow D.E (ids D.E 2 L) L) (ω.2 1).1)

lemma privateZeroAccept_eq (P : ValueParameters) (t : ℝ)
    (i : Fin m) (b : Icc D.E.R D.E.Rp) (ω : Background m 2 NativeLocalPolicy.Seed)
    (hr : ∀ k,k≠i → sourceBands P D.E t (ω.1 k).1) :
    privateZeroAccept D i b ω=decide (i∈(D.completedPolicy 0 (presentList ω i b 0) (ω.2 0)).val) := by
  simp only [D.completed_on_menu 0 _ (onMenu_present_partial D P t i b ω hr 0),
    own_zero_private D _ i (partial_present_ids D i b ω 0) (ω.2 0)]
  rfl

lemma privateOneAccept_eq (P : ValueParameters) (t : ℝ)
    (i : Fin m) (b : Icc D.E.R D.E.Rp) (ω : Background m 2 NativeLocalPolicy.Seed)
    (hr : ∀ k,k≠i → sourceBands P D.E t (ω.1 k).1) :
    privateOneAccept D i b ω=decide (i∈(D.completedPolicy 1 (presentList ω i b 1) (ω.2 1)).val) := by
  simp only [D.completed_on_menu 1 _ (onMenu_present_partial D P t i b ω hr 1),
    own_one_private D _ i (partial_present_ids D i b ω 1) (ω.2 1)]
  rfl

theorem native_partial_focal_count (P : ValueParameters) (t : ℝ)
    (Γ : FiniteGame m 2 c NativeLocalPolicy.Seed) (hpolicy : Γ.policy=D.completedPolicy)
    (i : Fin m) (b : Icc D.E.R D.E.Rp) (k : Fin 3)
    (ω : Sample m 2 NativeLocalPolicy.Seed)
    (hr : ∀ l,l≠i → sourceBands P D.E t (ω.1.1 l).1) :
    focalCount Γ i (RawRoutes.action b ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b.2.1) k) ω=
      boolPairCount
        ((if (0:Fin 2)∈firstK ω.2 k.val then privateZeroAccept D i b ω.1 else false),
          (if (1:Fin 2)∈firstK ω.2 k.val then privateOneAccept D i b ω.1 else false)) := by
  rw [privateZeroAccept_eq D P t i b ω.1 hr,privateOneAccept_eq D P t i b ω.1 hr]
  apply Fin.ext
  simp only [focalCount,Game.boundedCount,inclusionCount_eq_sum,Fin.sum_univ_two,boolPairCount]
  simp only [mem_allocation_deviated_iff Γ i _ ω 0,
    mem_allocation_deviated_iff Γ i _ ω 1]
  simp only [Accepts,hpolicy,RawRoutes.action]
  by_cases h0 : (0:Fin 2)∈firstK ω.2 k.val <;>
    by_cases h1 : (1:Fin 2)∈firstK ω.2 k.val <;>
      simp [h0,h1]

end FCAppendix.Affine.Tail04.NativeMenuReports
