import FCAppendix.Affine.Tail04.OrderedNativePolicy
import FCAppendix.Affine.Tail04.NativePartialInclusion
import FCAppendix.Affine.Tail04.NativePartialReports
import FCAppendix.Affine.Tail04.NativeMenuReports

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomPartialCarrier
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open NativeLocalPolicy NativeMenuReports NativePartialReports NativePartialInclusion
open OriginalValues OriginalPopulation LocalCoordinates
open scoped BigOperators

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

theorem role_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    OrderedNativePolicy.role D.E j (Function.update L i (some b'))=
      OrderedNativePolicy.role D.E j L := by
  unfold OrderedNativePolicy.role
  rw [PrivateUpdate.count_update D L i hi hb hb',
    PrivateUpdate.otherCount_update D L i hi hb hb']

lemma present_nonnegative (ω : Bayes.Background m 2 Seed) (i : Fin m)
    (b : ℝ) (hb : 0≤ b) (j : Fin 2) : NonnegativeList (presentList ω i b j) := by
  intro k
  cases h : presentList ω i b j k with
  | none => simp only [entryBid];exact le_rfl
  | some x => exact presentList_bid_nonneg ω i b hb j k x h

theorem present_inclusion_mono (hlow : D.E.d<1-D.ξ)
    (P : ValueParameters) (t : ℝ) (ω : Bayes.Background m 2 Seed) (i : Fin m)
    (b b' : Icc D.E.R D.E.Rp) (hbb : (b:ℝ)< b')
    (hr : ∀ k,k≠i → sourceBands P D.E t (ω.1 k).1)
    (j : Fin 2) (u u' : Seed)
    (ha : i∈(OrderedNativePolicy.policy D j (presentList ω i b j) u).val) :
    i∈(OrderedNativePolicy.policy D j (presentList ω i b' j) u').val := by
  rw [OrderedNativePolicy.policy_on_menu D j _
    (onMenu_present_partial D P t i b ω hr j)] at ha
  rw [OrderedNativePolicy.policy_on_menu D j _
    (onMenu_present_partial D P t i b' ω hr j),presentList_update ω i b b' j]
  rw [role_update D j _ i (presentList_self ω i b j) b.2 b'.2]
  exact NativePartialInclusion.policy_inclusion_mono D hlow
    (OrderedNativePolicy.role D.E j (presentList ω i b j)) _
    (present_nonnegative ω i b ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b.2.1) j)
    i (presentList_self ω i b j) b.2 b'.2 hbb u u' ha

theorem focal_count_mono (hlow : D.E.d<1-D.ξ) (P : ValueParameters) (t : ℝ)
    (Γ : FiniteGame m 2 c Seed) (hpolicy : Γ.policy=OrderedNativePolicy.policy D)
    (ω : Sample m 2 Seed) (i : Fin m) (b b' : Icc D.E.R D.E.Rp)
    (hbb : (b:ℝ)< b') (k : Fin 3)
    (hr : ∀ l,l≠i → sourceBands P D.E t (ω.1.1 l).1) :
    ((focalCount Γ i (RawRoutes.action b
      ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b.2.1) k) ω).val:ℝ)≤
      (focalCount Γ i (RawRoutes.action b'
        ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b'.2.1) k) ω).val := by
  rw [focalCount_val_eq,focalCount_val_eq]
  apply Finset.sum_le_sum
  intro j _
  have hi : (if Accepts Γ i b j ω.1 then (1:ℝ) else 0)≤
      if Accepts Γ i b' j ω.1 then 1 else 0 := by
    by_cases ha : Accepts Γ i b j ω.1
    · have ha' : Accepts Γ i b' j ω.1 := by
        change i∈(Γ.policy j _ _).val at ha ⊢
        rw [hpolicy] at ha ⊢
        exact present_inclusion_mono D hlow P t ω.1 i b b' hbb hr j _ _ ha
      simp only [if_pos ha,if_pos ha',le_refl]
    · simp only [if_neg ha]
      split_ifs <;> norm_num
  exact mul_le_mul_of_nonneg_left hi (by split_ifs <;> norm_num)

lemma all_partial_list (row : UserProfile m 2) (seed : Fin 2 → Seed)
    (j : Fin 2) (hroute : ∀ l,(row l).1.2.routeCount=1)
    (hsame : ∀ l,j∈firstK (row l).2 1) (i : Fin m) :
    ∀ l,presentList (row,seed) i (row i).1.2.bid j l=some (row l).1.2.bid := by
  intro l
  by_cases hli : l=i
  · subst l;exact presentList_self _ _ _ _
  · simp only [presentList_other _ _ _ hli,hroute l,if_pos (hsame l)]

theorem above_all_partial_included (hlow : D.E.d<1-D.ξ) (hc : 0< c)
    (Γ : FiniteGame m 2 c Seed) (hpolicy : Γ.policy=OrderedNativePolicy.policy D)
    (row : UserProfile m 2) (seed : Fin 2 → Seed) (j : Fin 2)
    (hbid : ∀ l,(row l).1.2.bid∈Icc D.E.R D.E.Rp)
    (hroute : ∀ l,(row l).1.2.routeCount=1)
    (hsame : ∀ l,j∈firstK (row l).2 1)
    (i : Fin m) (b' : Icc D.E.R D.E.Rp)
    (hbetter : ∀ l,(row l).1.2.bid<(b':ℝ)) :
    (focalCount Γ i (RawRoutes.action b'
      ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b'.2.1) 1)
        ((row,seed),(row i).2)).val=1 := by
  let L := presentList (row,seed) i (row i).1.2.bid j
  have hL := all_partial_list row seed j hroute hsame i
  let r := OrderedNativePolicy.role D.E j (presentList (row,seed) i b' j)
  have hnew : i∈(D.policy r (Function.update L i (some (b':ℝ))) (seed j)).val :=
    NativePartialInclusion.policy_above_partial_cluster D hlow hc r L
      (fun l => (row l).1.2.bid) hL hbid i b'.2 hbetter (seed j)
  have hmenu : D.offCommon (presentList (row,seed) i b' j)=∅ := by
    apply (D.offCommon_eq_empty_iff _).mpr
    intro l hl
    have hp : (presentList (row,seed) i b' j l)=
        some (if l=i then (b':ℝ) else (row l).1.2.bid) := by
      rw [presentList_update (row,seed) i (row i).1.2.bid b' j]
      by_cases hh : l=i
      · subst l;simp
      · simp [hL l,hh]
    have hb : (if l=i then (b':ℝ) else (row l).1.2.bid)∈Icc D.E.R D.E.Rp := by
      split_ifs
      · exact b'.2
      · exact hbid l
    rw [hp,PrivateUpdate.tag_partial D hb] at hl
    exact (by decide : (2:Fin 4)≠1) hl |>.elim
  have ha : Accepts Γ i b' j (row,seed) := by
    change i∈(Γ.policy j _ _).val
    rw [hpolicy,OrderedNativePolicy.policy_on_menu D j _ hmenu]
    change i∈(D.policy r (presentList (row,seed) i b' j) (seed j)).val
    rw [presentList_update (row,seed) i (row i).1.2.bid b' j]
    exact hnew
  have hin := (mem_allocation_deviated_iff Γ i
    (RawRoutes.action b' ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b'.2.1) 1)
      ((row,seed),(row i).2) j).mpr ⟨hsame i,ha⟩
  have hpos : 0<(focalCount Γ i
      (RawRoutes.action b' ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b'.2.1) 1)
        ((row,seed),(row i).2)).val := by
    change 0<(accepted _ Γ.policy seed i).card
    exact Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hin⟩⟩
  have hle := focalCount_le Γ i
    (RawRoutes.action b' ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b'.2.1) 1)
      ((row,seed),(row i).2)
  change _≤1 at hle
  omega

lemma own_observation (row : UserProfile m 2) (seed : Fin 2 → Seed)
    (i : Fin m) (j : Fin 2) :
    observe (deviated i (row i).1.2 ((row,seed),(row i).2)) j=
      observe (drawsRealization row) j := by
  funext l
  by_cases hli : l=i
  · subst l;simp only [observe,deviated_recipients_self,deviated_bid_self,drawsRealization]
  · simp only [observe,deviated_recipients_other i l hli,deviated_bid_other i l hli,drawsRealization]

lemma own_count (Γ : FiniteGame m 2 c Seed) (row : UserProfile m 2)
    (seed : Fin 2 → Seed) (i : Fin m) :
    focalCount Γ i (row i).1.2 ((row,seed),(row i).2)=
      boundedCount (drawsRealization row) Γ.policy seed i := by
  apply Fin.ext
  change inclusionCount _ _ _ _=inclusionCount _ _ _ _
  rw [inclusionCount_eq_sum,inclusionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [allocation]
  exact congrArg (fun L : LocalList m =>
    if i∈(Γ.policy j L (seed j)).val then (1:ℕ) else 0) (own_observation row seed i j)

theorem all_partial_old_capacity (Γ : FiniteGame m 2 c Seed)
    (row : UserProfile m 2) (seed : Fin 2 → Seed) (j : Fin 2)
    (hroute : ∀ l,(row l).1.2.routeCount=1)
    (hsame : ∀ l,j∈firstK (row l).2 1) :
    (∑ i : Fin m,((focalCount Γ i (row i).1.2 ((row,seed),(row i).2)).val:ℝ))≤ c := by
  let x := drawsRealization row
  have hrec (i : Fin m) : x.recipients i={j} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_,?_⟩
    · simpa only [x,drawsRealization,hroute i] using hsame i
    · intro l hl
      have hc : (x.recipients i).card=1 := by simpa only [x,drawsRealization,hroute i] using x.chosen_size i
      obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hc
      have hj : j∈x.recipients i := by simpa only [x,drawsRealization,hroute i] using hsame i
      rw [hq] at hl hj
      exact (Finset.mem_singleton.mp hl).trans (Finset.mem_singleton.mp hj).symm
  have hcount (i : Fin m) : ((boundedCount x Γ.policy seed i).val:ℝ)=
      if i∈allocation x Γ.policy seed j then 1 else 0 := by
    have hs := accepted_subset_recipients x Γ.policy seed i
    rw [hrec i] at hs
    by_cases hi : i∈allocation x Γ.policy seed j
    · have he : accepted x Γ.policy seed i={j} := Finset.Subset.antisymm hs
        (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hi⟩))
      simp [boundedCount,inclusionCount,he,hi]
    · have he : accepted x Γ.policy seed i=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro l hl
        have hj := Finset.mem_singleton.mp (hs hl)
        subst l
        exact hi (Finset.mem_filter.mp hl).2
      simp [boundedCount,inclusionCount,he,hi]
  simp_rw [own_count]
  change (∑ i : Fin m,((boundedCount x Γ.policy seed i).val:ℝ))≤c
  simp_rw [hcount]
  have he : (∑ i : Fin m,if i∈allocation x Γ.policy seed j then (1:ℝ) else 0)=
      ((allocation x Γ.policy seed j).card:ℝ) := by simp
  rw [he]
  exact_mod_cast (Γ.policy j (observe x j) (seed j)).property.1

end FCAppendix.Affine.Tail04.OrderedAtomPartialCarrier
