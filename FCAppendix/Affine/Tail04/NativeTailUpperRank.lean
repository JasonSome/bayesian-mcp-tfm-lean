import FCAppendix.Affine.Tail04.CompletedNativePolicy
import FCAppendix.Affine.Tail04.NativeObservationPair
import FCAppendix.Finite.ReceiptBounds

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeTailUpperRank
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy
open OriginalValues OriginalPopulation
open scoped BigOperators

variable {m c : ℕ} (K : Data m c)

lemma upper_tag (y : ℝ) (hy : K.E.H≤ y) : K.E.localTag (some y)=2 := by
  have hp : y∈K.E.privateBids := Or.inr hy
  simp only [Observable.Regions.localTag,if_neg
    (not_le.mpr (K.E.private_above_low hp)),if_pos hp]

lemma upper_ids (L : LocalList m) (i : Fin m) (y : ℝ)
    (hi : L i=some y) (hy : K.E.H≤ y) : i∈ids K.E 2 L := by
  simp only [ids,Finset.mem_filter,Finset.mem_univ,true_and,hi,upper_tag K y hy]

lemma oppositeMean_nonneg (j : Fin 2) (L : LocalList m)
    (k : Fin (ids K.E 1 L).card) : 0≤ K.oppositeActiveMean j L k := by
  by_cases hj : j=0
  · simp only [Data.oppositeActiveMean,if_pos hj]
    convert!
      (K.zeroMean_bounds _ _ _ _ k).1 using 1
  · simp only [Data.oppositeActiveMean,if_neg hj]
    convert!
      (K.oneMean_bounds _ _ _ _ k).1 using 1

lemma highReceipt_le_cap (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∉ids K.E 2 L) : K.highReceipt j L i≤ K.E.U := by
  by_cases ha : i∈ids K.E 1 L
  · rw [K.highReceipt_active_clipped j L i ha]
    have hb := LocalCoordinates.clamp_mem (x:=entryBid (L i)) K.E.one_le_U
    have hq := oppositeMean_nonneg K j L
      (rankFin (ids K.E 1 L) (bidVector L) ⟨i,ha⟩)
    have hfac : 1-K.ξ*K.oppositeActiveMean j L
        (rankFin (ids K.E 1 L) (bidVector L) ⟨i,ha⟩)≤1 := by
      nlinarith [mul_nonneg K.xi_pos.le hq]
    exact (mul_le_of_le_one_right ((by norm_num : (0:ℝ)≤1).trans hb.1) hfac).trans hb.2
  · rw [K.highReceipt_zero j L i (by simp only [Finset.mem_union,not_or];exact ⟨ha,hi⟩)]
    exact (by norm_num : (0:ℝ)≤1).trans K.E.one_le_U

lemma nonprivate_bid_lt_floor (L : LocalList m) (i : Fin m)
    (hi : i∉ids K.E 2 L) : entryBid (L i)< K.E.H := by
  cases he : L i with
  | none => simpa only [entryBid] using
      ((by norm_num : (0:ℝ)<1).trans_le K.E.one_le_U).trans K.E.U_lt_H
  | some y =>
    by_contra hn
    exact hi (upper_ids K L i y he (le_of_not_gt hn))

lemma upper_receipt_comparison (j : Fin 2) (L : LocalList m)
    (y : ℝ) (hy : K.E.H≤ y) (i : Fin m) :
    y< K.highReceipt j L i ↔ y< entryBid (L i) := by
  by_cases hi : i∈ids K.E 2 L
  · rw [K.highReceipt_private j L i hi]
  · have hr := (highReceipt_le_cap K j L i hi).trans_lt (K.E.U_lt_H.trans_le hy)
    have hb := (nonprivate_bid_lt_floor K L i hi).trans_le hy
    exact iff_of_false (not_lt.mpr hr.le) (not_lt.mpr hb.le)

theorem local_upper_rank (j : Fin 2) (L : LocalList m) (u : Seed)
    (i : Fin m) (y : ℝ) (hy : K.E.H≤ y) (hi : L i=some y)
    (hno : ∀ k,k≠i→ L k≠some y) :
    i∈(K.policy j L u).val ↔
      (Finset.univ.filter fun k=> y< entryBid (L k)).card< c := by
  have hip := upper_ids K L i y hi hy
  have hit : K.E.localTag (L i)≠0 := by rw [hi,upper_tag K y hy];decide
  rw [K.policy_high_iff j L u i hit]
  have hr : K.highReceipt j L i=y := by rw [K.highReceipt_private j L i hip,hi];rfl
  have hy0 : 0< y := ((by norm_num : (0:ℝ)<1).trans_le K.E.one_le_U).trans
    (K.E.U_lt_H.trans_le hy)
  have hn : ∀ k,k≠i→ K.highReceipt j L k≠y := by
    intro k hki
    by_cases hkp : k∈ids K.E 2 L
    · rw [K.highReceipt_private j L k hkp]
      have hp := ids_present K.E 2 (by decide) L k hkp
      cases he : L k with
      | none => exact (hp he).elim
      | some b =>
        intro hb
        exact hno k hki (he.trans (congrArg some hb))
    · exact ne_of_lt ((highReceipt_le_cap K j L k hkp).trans_lt
        (K.E.U_lt_H.trans_le hy))
  have hb : (Finset.univ.filter fun k=> K.highReceipt j L i< K.highReceipt j L k)=
      Finset.univ.filter fun k=> y< entryBid (L k) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hr,
      upper_receipt_comparison K j L y hy k]
  have hc : (Finset.univ.filter fun k=> k≠i ∧ K.highReceipt j L i≤ K.highReceipt j L k)=
      Finset.univ.filter fun k=> y< entryBid (L k) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hr]
    rw [←upper_receipt_comparison K j L y hy k]
    constructor
    · intro hk
      exact lt_of_le_of_ne hk.2 (hn k hk.1).symm
    · intro hk
      exact ⟨fun he=> by subst k;rw [hr] at hk;exact lt_irrefl _ hk,hk.le⟩
  have ho := K.high_numerical_optimal j L u.1
  constructor
  · intro hs
    by_contra hh
    exact (Finite.excluded_of_many_better c _ _ ho i
      (by rw [hb];exact le_of_not_gt hh)) hs
  · intro hs
    exact Finite.included_of_few_competitors c _ _ ho i (by simpa only [hr] using hy0)
      (by simpa only [hc] using hs)

theorem completed_local_upper_rank (j : Fin 2) (L : LocalList m)
    (hmenu : K.offCommon L=∅) (u : Seed) (i : Fin m) (y : ℝ)
    (hy : K.E.H≤ y) (hi : L i=some y) (hno : ∀ k,k≠i→ L k≠some y) :
    i∈(K.completedPolicy j L u).val ↔
      (Finset.univ.filter fun k=> y< entryBid (L k)).card< c := by
  rw [K.completed_on_menu j L hmenu u]
  exact local_upper_rank K j L u i y hy hi hno

variable (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (t : ℝ)

lemma source_present_on_menu (i : Fin m) (ω : Background m 2 Seed)
    (hband : ∀ k,k≠i→ sourceBands P K.E t (ω.1 k).1)
    (j : Fin 2) (y : ℝ) (hy : K.E.H≤ y) :
    K.offCommon (presentList ω i y j)=∅ := by
  apply (K.offCommon_eq_empty_iff _).mpr
  intro k hk
  by_cases hki : k=i
  · subst k
    simp only [presentList_self,upper_tag K y hy] at hk
    contradiction
  · have he : presentList ω i y j k=NativePrivatePosterior.observedEntry j (ω.1 k) :=
      presentList_other ω i k hki y j
    rw [he] at hk ⊢
    exact NativeObservationPair.source_active_box K.E P t (ω.1 k) (hband k hki) j hk

theorem native_upper_accepts_iff_rank
    (hpolicy : ∀ j L,NonnegativeList L→∀ u,Γ.policy j L u=K.completedPolicy j L u)
    (hband : ∀ᵐ x ∂userLaw Γ,sourceBands P K.E t x.1)
    (hatom : ∀ (j : Fin 2) (y : ℝ),K.E.H≤ y→
      userLaw Γ {x | j∈firstK x.2 x.1.2.routeCount ∧ x.1.2.bid=y}=0)
    (i : Fin m) (j : Fin 2) (y : ℝ) (hy : K.E.H≤ y) :
    ∀ᵐ ω ∂backgroundLaw Γ,
      Accepts Γ i y j ω ↔ rivals i (aboveAt j y) ω< c := by
  have hsingle := measure_eq_zero_iff_ae_notMem.mp (hatom j y hy)
  have hall : ∀ᵐ d ∂userProfileLaw Γ,∀ k,
      sourceBands P K.E t (d k).1 ∧
        ¬(j∈firstK (d k).2 (d k).1.2.routeCount ∧ (d k).1.2.bid=y) :=
    ae_all_iff.mpr (fun k=>(measurePreserving_eval (fun _ : Fin m=> userLaw Γ) k).quasiMeasurePreserving.ae (hband.and hsingle))
  have hback := (measurePreserving_fst (μ:=userProfileLaw Γ)
    (ν:=Measure.pi fun _ : Fin 2 => Γ.seedLaw)).quasiMeasurePreserving.ae hall
  filter_upwards [hback] with ω hω
  let L := presentList ω i y j
  have hy0 : 0≤ y := ((by norm_num : (0:ℝ)≤1).trans K.E.one_le_U).trans
    (K.E.U_lt_H.le.trans hy)
  have hL : NonnegativeList L := by
    intro k
    cases he : L k with
    | none => exact le_rfl
    | some b => exact presentList_bid_nonneg ω i y hy0 j k b he
  have hn : ∀ k,k≠i→ L k≠some y := fun k hk he=>
    (hω k).2 (presentList_other_some ω i k hk y j y he)
  have hm := source_present_on_menu K P t i ω (fun k _=>(hω k).1) j y hy
  have hs := completed_local_upper_rank K j L hm (ω.2 j) i y hy
    (presentList_self ω i y j) hn
  have heq : (Finset.univ.filter fun k=> y< entryBid (L k))=
      (Finset.univ.erase i).filter fun k=> ω.1 k∈aboveAt j y := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true,
      aboveAt,mem_setOf_eq]
    by_cases hk : k=i
    · subst k
      simp only [L,presentList_self,entryBid,lt_self_iff_false,ne_eq,not_true_eq_false,false_and]
    · rw [show L k=if j∈firstK (ω.1 k).2 (ω.1 k).1.2.routeCount
          then some (ω.1 k).1.2.bid else none from presentList_other ω i k hk y j]
      by_cases hj : j∈firstK (ω.1 k).2 (ω.1 k).1.2.routeCount
      · simp [hj,entryBid,hk]
      · simp [hj,entryBid,not_lt.mpr hy0]
  rw [heq] at hs
  change i∈(Γ.policy j L (ω.2 j)).val ↔ _
  rw [hpolicy j L hL (ω.2 j)]
  simpa only [rivals_eq_card] using hs

end FCAppendix.Affine.Tail04.NativeTailUpperRank
