import FCAppendix.Affine.Tail04.NativeLocalPolicy
import FCAppendix.Affine.Tail04.PairedRawPolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalCoordinates SortedCoordinates
open scoped BigOperators

local instance nativeRawFallbackTopologicalSpace (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance nativeRawFallbackDiscreteTopology (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance nativeRawFallbackMeasurableSpace (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance nativeRawFallbackBorelSpace (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

def rawCommon (L : LocalList m) : Finset (Fin m) := ids D.E 0 L ∪ ids D.E 1 L

lemma measurable_rawCommon : Measurable D.rawCommon :=
  (measurable_of_countable (fun z : Finset (Fin m)×Finset (Fin m) => z.1∪z.2)).comp
    ((measurable_ids D.E 0).prodMk (measurable_ids D.E 1))

lemma rawCommon_private_disjoint (L : LocalList m) :
    Disjoint (D.rawCommon L) (ids D.E 2 L) := by
  apply Finset.disjoint_left.mpr
  intro i hi hp
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (0:Fin 4)≠2) L) hi hp
  · exact Finset.disjoint_left.mp (ids_disjoint D.E (by decide : (1:Fin 4)≠2) L) hi hp

include D in
lemma rawCommon_present (L : LocalList m) (i : Fin m) (hi : i∈D.rawCommon L) : L i≠none := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact ids_present D.E 0 (by decide) L i hi
  · exact ids_present D.E 1 (by decide) L i hi

lemma rawCommon_lt_upper (L : LocalList m) (i : Fin m) (hi : i∈D.rawCommon L) :
    entryBid (L i)< D.E.H := by
  have hp := D.rawCommon_present L i hi
  cases he : L i with
  | none => exact (hp he).elim
  | some b =>
    rcases Finset.mem_union.mp hi with hi | hi
    · have ht := (Finset.mem_filter.mp hi).2
      have hb : b≤ D.E.d := by
        by_contra hn
        by_cases hpr : b∈D.E.privateBids <;>
          simp [he,Observable.Regions.localTag,hn,hpr] at ht
      exact (show entryBid (some b)≤ D.E.d from hb).trans_lt D.E.d_lt_H
    · have ht := (Finset.mem_filter.mp hi).2
      have hb : b< D.E.H := by
        by_contra hn
        have hu : D.E.H≤ b := le_of_not_gt hn
        have hpr : b∈D.E.privateBids := Or.inr hu
        have hd : ¬b≤ D.E.d := not_le.mpr (D.E.d_lt_H.trans_le hu)
        simp [he,Observable.Regions.localTag,hd,hpr] at ht
      exact hb

def rawBids (_D : NativeLocalPolicy.Data m c) (C : Finset (Fin m)) (L : LocalList m) : Fin C.card → ℝ :=
  fun i => entryBid (L (enumerate C (bidVector L) i))

lemma measurable_rawBids (C : Finset (Fin m)) : Measurable (D.rawBids C) := by
  apply measurable_pi_iff.mpr
  intro i
  have hi := measurable_subtype_coe.comp
    (measurable_enumerate C bidVector
      (fun k => measurable_entryBid.comp (measurable_pi_apply k)) i)
  exact measurable_finite_eval
    (fun L : LocalList m => (enumerate C (bidVector L) i).val)
    (fun L k => entryBid (L k)) hi
    (fun k => measurable_entryBid.comp (measurable_pi_apply k))

@[simp] lemma rawBids_rank (C : Finset (Fin m)) (L : LocalList m)
    (i : {i // i∈C}) : D.rawBids C L (rankFin C (bidVector L) i)=entryBid (L i) := by
  simp only [rawBids,enumerate_rank]

def rawParameter (C : Finset (Fin m)) (H0 H1 : Fin (m+1)) (L : LocalList m) :
    PairedRawPolicy.Parameters C.card H0.val H1.val D.E.R D.E.Rp :=
  (D.rawBids C L,(D.signalLaw H0,D.signalLaw H1))

lemma measurable_rawParameter (C : Finset (Fin m)) (H0 H1 : Fin (m+1)) :
    Measurable (D.rawParameter C H0 H1) :=
  (D.measurable_rawBids C).prodMk measurable_const

def rawKey (L : LocalList m) : LocalCoordinates.Key m :=
  ((D.rawCommon L,ids D.E 2 L),⟨D.E.otherPrivateCount L,by
    unfold Observable.Regions.otherPrivateCount
    omega⟩)

lemma measurable_rawKey : Measurable D.rawKey := by
  change Measurable (fun L : LocalList m =>
    ((D.rawCommon L,ids D.E 2 L),(LocalCoordinates.key D.E L).2))
  exact (D.measurable_rawCommon.prodMk (measurable_ids D.E 2)).prodMk
    (LocalCoordinates.measurable_key D.E).snd

def rawFallbackAtKey (j : Fin 2) (K : LocalCoordinates.Key m) (L : LocalList m)
    (u : unitInterval) : Finset (Fin m) :=
  if hCP : Disjoint K.1.1 K.1.2 then
    if j=0 then
      transport K.1.1 K.1.2 hCP (bidVector L) (privateKey D.E L)
        (PairedRawPolicy.zero K.1.1.card K.1.2.card K.2.val c D.E.R D.E.Rp D.E.H D.ξ
          (D.rawParameter K.1.1 (D.finiteCount K.1.2) K.2 L,
            privateRow D.E K.1.2 L) u)
    else
      transport K.1.1 K.1.2 hCP (bidVector L) (privateKey D.E L)
        (PairedRawPolicy.one K.1.1.card K.2.val K.1.2.card c D.E.R D.E.Rp D.E.H D.ξ
          (D.rawParameter K.1.1 K.2 (D.finiteCount K.1.2) L,
            privateRow D.E K.1.2 L) u)
  else ∅

set_option maxHeartbeats 600000 in
lemma rawFallbackAtKey_measurable (j : Fin 2) (K : LocalCoordinates.Key m) :
    Measurable (Function.uncurry (D.rawFallbackAtKey j K)) := by
  change Measurable (fun z : LocalList m × unitInterval => D.rawFallbackAtKey j K z.1 z.2)
  by_cases hd : Disjoint K.1.1 K.1.2
  · by_cases hj : j=0
    · simp only [rawFallbackAtKey,dif_pos hd,if_pos hj]
      apply measurable_transport K.1.1 K.1.2 hd
        (fun z : LocalList m×unitInterval => bidVector z.1)
        (fun z => privateKey D.E z.1)
        (fun i => (measurable_pi_apply i).comp (measurable_bidVector.comp measurable_fst))
        (fun i => (measurable_pi_apply i).comp ((measurable_privateKey D.E).comp measurable_fst))
      have hh := (PairedRawPolicy.measurable_zero K.1.1.card K.1.2.card K.2.val c
        D.E.R D.E.Rp D.E.H D.ξ).comp
        ((((D.measurable_rawParameter K.1.1 (D.finiteCount K.1.2) K.2).comp measurable_fst).prodMk
          ((measurable_privateRow D.E K.1.2).comp measurable_fst)).prodMk measurable_snd)
      simp only [Function.comp_def,Function.uncurry,rawParameter,finiteCount] at hh
      convert! hh using 1
    · simp only [rawFallbackAtKey,dif_pos hd,if_neg hj]
      apply measurable_transport K.1.1 K.1.2 hd
        (fun z : LocalList m×unitInterval => bidVector z.1)
        (fun z => privateKey D.E z.1)
        (fun i => (measurable_pi_apply i).comp (measurable_bidVector.comp measurable_fst))
        (fun i => (measurable_pi_apply i).comp ((measurable_privateKey D.E).comp measurable_fst))
      have hh := (PairedRawPolicy.measurable_one K.1.1.card K.2.val K.1.2.card c
        D.E.R D.E.Rp D.E.H D.ξ).comp
        ((((D.measurable_rawParameter K.1.1 K.2 (D.finiteCount K.1.2)).comp measurable_fst).prodMk
          ((measurable_privateRow D.E K.1.2).comp measurable_fst)).prodMk measurable_snd)
      simp only [Function.comp_def,Function.uncurry,rawParameter,finiteCount] at hh
      convert! hh using 1
  · simpa only [rawFallbackAtKey,dif_neg hd] using
      (measurable_const : Measurable (fun _ : LocalList m×unitInterval => (∅ : Finset (Fin m))))

lemma rawFallbackAtKey_capacity (j : Fin 2) (K : LocalCoordinates.Key m)
    (L : LocalList m) (u : unitInterval) : (D.rawFallbackAtKey j K L u).card≤ c := by
  unfold rawFallbackAtKey
  split_ifs with hd hj
  · simpa only [transport_card] using PairedRawPolicy.zero_capacity
      K.1.1.card K.1.2.card K.2.val c D.E.R D.E.Rp D.E.H D.ξ _ _ u
  · simpa only [transport_card] using PairedRawPolicy.one_capacity
      K.1.1.card K.2.val K.1.2.card c D.E.R D.E.Rp D.E.H D.ξ _ _ u
  · simp

lemma rawFallbackAtKey_subset (j : Fin 2) (K : LocalCoordinates.Key m)
    (L : LocalList m) (u : unitInterval) : D.rawFallbackAtKey j K L u⊆K.1.1∪K.1.2 := by
  unfold rawFallbackAtKey
  split_ifs <;> first | exact transport_subset _ _ _ _ _ _ | exact Finset.empty_subset _

def rawSelection (j : Fin 2) (L : LocalList m) (u : unitInterval) : Finset (Fin m) :=
  D.rawFallbackAtKey j (D.rawKey L) L u

lemma rawSelection_measurable (j : Fin 2) : Measurable (Function.uncurry (D.rawSelection j)) := by
  have h : Measurable (fun z : LocalCoordinates.Key m×(LocalList m×unitInterval) =>
      D.rawFallbackAtKey j z.1 z.2.1 z.2.2) :=
    measurable_from_prod_countable_right (D.rawFallbackAtKey_measurable j)
  exact h.comp ((D.measurable_rawKey.comp measurable_fst).prodMk measurable_id)

lemma rawSelection_capacity (j : Fin 2) (L : LocalList m) (u : unitInterval) :
    (D.rawSelection j L u).card≤ c := D.rawFallbackAtKey_capacity j _ L u

include D in
lemma rawSelection_present (j : Fin 2) (L : LocalList m) (u : unitInterval) (i : Fin m)
    (hi : i∈D.rawSelection j L u) : L i≠none := by
  rcases Finset.mem_union.mp (D.rawFallbackAtKey_subset j (D.rawKey L) L u hi) with hi | hi
  · exact D.rawCommon_present L i hi
  · exact ids_present D.E 2 (by decide) L i hi

def rawFallback (j : Fin 2) : LocalPolicy m c NativeLocalPolicy.Seed :=
  fun L u => ⟨D.rawSelection j L u.1,D.rawSelection_capacity j L u.1,
    D.rawSelection_present j L u.1⟩

theorem rawFallback_measurable (j : Fin 2) :
    Measurable (fun z : LocalList m×NativeLocalPolicy.Seed => (D.rawFallback j z.1 z.2).val) := by
  change Measurable (fun z : LocalList m × NativeLocalPolicy.Seed => D.rawSelection j z.1 z.2.1)
  have h := (D.rawSelection_measurable j).comp
    (show Measurable (fun z : LocalList m × NativeLocalPolicy.Seed => (z.1,z.2.1)) from
      measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  simpa only [Function.comp_def,Function.uncurry] using h

def rawReceiptAtKey (j : Fin 2) (K : LocalCoordinates.Key m) (L : LocalList m) : Fin m → ℝ :=
  if j=0 then
    receiptTransport K.1.1 K.1.2 (bidVector L) (privateKey D.E L)
      (receipt (D.rawBids K.1.1 L)
        (PairedRawPolicy.mean1 K.1.1.card K.1.2.card K.2.val c D.E.R D.E.Rp D.ξ
          (D.rawParameter K.1.1 (D.finiteCount K.1.2) K.2 L)) D.ξ
        (privateRow D.E K.1.2 L))
  else
    receiptTransport K.1.1 K.1.2 (bidVector L) (privateKey D.E L)
      (receipt (D.rawBids K.1.1 L)
        (PairedRawPolicy.mean0 K.1.1.card K.2.val K.1.2.card c D.E.R D.E.Rp D.ξ
          (D.rawParameter K.1.1 K.2 (D.finiteCount K.1.2) L)) D.ξ
        (privateRow D.E K.1.2 L))

def rawNumericalReceipt (j : Fin 2) (L : LocalList m) : Fin m → ℝ :=
  D.rawReceiptAtKey j (D.rawKey L) L

def rawOppositeMean (j : Fin 2) (L : LocalList m) : Fin (D.rawCommon L).card → ℝ :=
  let K := D.rawKey L
  if j=0 then
    PairedRawPolicy.mean1 K.1.1.card K.1.2.card K.2.val c D.E.R D.E.Rp D.ξ
      (D.rawParameter K.1.1 (D.finiteCount K.1.2) K.2 L)
  else
    PairedRawPolicy.mean0 K.1.1.card K.2.val K.1.2.card c D.E.R D.E.Rp D.ξ
      (D.rawParameter K.1.1 K.2 (D.finiteCount K.1.2) L)

lemma rawNumericalReceipt_common (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈D.rawCommon L) :
    D.rawNumericalReceipt j L i=entryBid (L i)*(1-D.ξ*D.rawOppositeMean j L
      (rankFin (D.rawCommon L) (bidVector L) ⟨i,hi⟩)) := by
  by_cases hj : j=0 <;>
    simp only [rawNumericalReceipt,rawReceiptAtKey,rawKey,hj,if_true,if_false,
      receiptTransport,dif_pos hi,receipt,rawOppositeMean,rawBids,enumerate_rank]

lemma rawNumericalReceipt_private (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 2 L) : D.rawNumericalReceipt j L i=entryBid (L i) := by
  have hn : i∉D.rawCommon L := fun hc =>
    Finset.disjoint_left.mp (D.rawCommon_private_disjoint L) hc hi
  have hd := numerical_decode D.E (private_ids_band D.E L i hi)
  by_cases hj : j=0 <;>
    simpa only [rawNumericalReceipt,rawReceiptAtKey,rawKey,hj,if_true,if_false,
      receiptTransport,dif_neg hn,dif_pos hi,receipt,privateRow,enumerate_rank] using hd

lemma rawNumericalReceipt_absent (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : L i=none) : D.rawNumericalReceipt j L i=0 := by
  have hn : i∉D.rawCommon L∪ids D.E 2 L := by
    simp [rawCommon,ids,hi,Observable.Regions.localTag]
  unfold rawNumericalReceipt rawReceiptAtKey
  split_ifs <;> exact receiptTransport_zero _ _ _ _ _ i hn

lemma rawBids_bounded (L : LocalList m) (hL : NonnegativeList L) :
    ∃ V : ℝ,1≤ V ∧ V< D.E.H ∧ ∀ i,D.rawBids (D.rawCommon L) L i∈Icc (0:ℝ) V := by
  have h1 : (1:ℝ)< D.E.H := D.E.one_le_U.trans_lt D.E.U_lt_H
  let b := D.rawBids (D.rawCommon L) L
  have hb : ∀ i,b i< D.E.H := fun i =>
    D.rawCommon_lt_upper L _ (enumerate (D.rawCommon L) (bidVector L) i).2
  have haux : ∀ S : Finset (Fin (D.rawCommon L).card),
      ∃ V : ℝ,1≤ V ∧ V< D.E.H ∧ ∀ i∈S,b i≤ V := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,le_rfl,h1,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨V,hV1,hVH,hV⟩ := ih
      refine ⟨max V (b i),hV1.trans (le_max_left _ _),max_lt hVH (hb i),?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact le_max_right _ _
      · exact (hV k hk).trans (le_max_left _ _)
  obtain ⟨V,hV1,hVH,hV⟩ := haux Finset.univ
  exact ⟨V,hV1,hVH,fun i => ⟨hL _,hV i (Finset.mem_univ _)⟩⟩

theorem rawFallback_numerical_optimal (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) (u : NativeLocalPolicy.Seed) :
    Finite.Optimal c (D.rawNumericalReceipt j L) ((D.rawFallback j L u).val) := by
  let K := D.rawKey L
  have hd : Disjoint K.1.1 K.1.2 := D.rawCommon_private_disjoint L
  obtain ⟨V,hV1,hVH,hV⟩ := D.rawBids_bounded L hL
  have hR : 0≤ D.E.R := D.E.d_nonneg.trans D.E.d_lt_R.le
  have hRp : D.E.Rp≤ V := D.E.Rp_lt_one.le.trans hV1
  have hH : 0< D.E.H := (by norm_num : (0:ℝ)<1).trans
    (D.E.one_le_U.trans_lt D.E.U_lt_H)
  change Finite.Optimal c (D.rawReceiptAtKey j K L) (D.rawFallbackAtKey j K L u.1)
  by_cases hj : j=0
  · simp only [rawReceiptAtKey,rawFallbackAtKey,dif_pos hd,if_pos hj]
    apply receiptTransport_optimal _ _ hd _ _ c _ _
    exact PairedRawPolicy.zero_optimal K.1.1.card K.1.2.card K.2.val c
      (D.rawParameter K.1.1 (D.finiteCount K.1.2) K.2 L)
      (privateRow D.E K.1.2 L) u.1 ⟨D.xi_pos.le,D.xi_lt_one.le⟩ hV hR hRp hVH hH
  · simp only [rawReceiptAtKey,rawFallbackAtKey,dif_pos hd,if_neg hj]
    apply receiptTransport_optimal _ _ hd _ _ c _ _
    exact PairedRawPolicy.one_optimal K.1.1.card K.2.val K.1.2.card c
      (D.rawParameter K.1.1 K.2 (D.finiteCount K.1.2) L)
      (privateRow D.E K.1.2 L) u.1 ⟨D.xi_pos.le,D.xi_lt_one.le⟩ hV hR hRp hVH hH

theorem rawMean0_original (C : Finset (Fin m)) (H0 H1 : Fin (m+1))
    (L : LocalList m) (i : Fin C.card) :
    LocalSamplerMean.mean
      (PairedRawPolicy.zero C.card H0.val H1.val c D.E.R D.E.Rp D.E.H D.ξ)
      (D.rawParameter C H0 H1 L) (D.originalPrivateRow H0) (Sum.inl i)=
        PairedRawPolicy.mean0 C.card H0.val H1.val c D.E.R D.E.Rp D.ξ
          (D.rawParameter C H0 H1 L) i :=
  PairedRawPolicy.original_zero_mean C.card H0.val H1.val c D.E.R D.E.Rp D.E.H D.ξ
    (D.rawParameter C H0 H1 L) (D.originalPrivateRow H0) (D.signalLaw_exact H0) i

theorem rawMean1_original (C : Finset (Fin m)) (H0 H1 : Fin (m+1))
    (L : LocalList m) (i : Fin C.card) :
    LocalSamplerMean.mean
      (PairedRawPolicy.one C.card H0.val H1.val c D.E.R D.E.Rp D.E.H D.ξ)
      (D.rawParameter C H0 H1 L) (D.originalPrivateRow H1) (Sum.inl i)=
        PairedRawPolicy.mean1 C.card H0.val H1.val c D.E.R D.E.Rp D.ξ
          (D.rawParameter C H0 H1 L) i :=
  PairedRawPolicy.original_one_mean C.card H0.val H1.val c D.E.R D.E.Rp D.E.H D.ξ
    (D.rawParameter C H0 H1 L) (D.originalPrivateRow H1) (D.signalLaw_exact H1) i

end FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
