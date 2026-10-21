import FCAppendix.Affine.Tail04.FocalIdentity
import FCAppendix.Affine.Tail04.FocalInsertionGuard
import FCAppendix.Affine.Tail04.NativeLocalPolicy
import FCAppendix.Exclusive.MarkerConstruction

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalCoordinates SortedCoordinates JoinedHighPolicy
open scoped BigOperators

local instance nativeFocalInsertionTopologicalSpace (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance nativeFocalInsertionDiscreteTopology (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance nativeFocalInsertionMeasurableSpace (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance nativeFocalInsertionBorelSpace (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

def offCommon (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter fun i => D.E.localTag (L i)=1 ∧ entryBid (L i)∉Icc (1:ℝ) D.E.U

lemma measurable_offCommon : Measurable D.offCommon :=
  Exclusive.Marker.measurable_filter Finset.univ _ (fun i =>
    (measurableSet_eq_fun (D.E.measurable_localTag.comp (measurable_pi_apply i)) measurable_const).inter
      ((measurableSet_Icc.preimage (measurable_entryBid.comp (measurable_pi_apply i))).compl))

lemma offCommon_mem (L : LocalList m) (i : Fin m) :
    i∈D.offCommon L ↔ i∈ids D.E 1 L ∧ entryBid (L i)∉Icc (1:ℝ) D.E.U := by
  simp [offCommon,ids]

lemma old_common_box (L : LocalList m) (i : Fin m) (h : D.offCommon L={i}) :
    ∀ j∈(ids D.E 1 L).erase i,entryBid (L j)∈Icc (1:ℝ) D.E.U := by
  intro j hj
  obtain ⟨hji,hjA⟩ := Finset.mem_erase.mp hj
  by_contra hb
  have hm := (D.offCommon_mem L j).mpr ⟨hjA,hb⟩
  rw [h,Finset.mem_singleton] at hm
  exact hji hm

abbrev FocalKey (m : ℕ) := Fin m × LocalCoordinates.Key m

def focalKey (i : Fin m) (L : LocalList m) : FocalKey m :=
  (i,(((ids D.E 1 L).erase i,ids D.E 2 L),(LocalCoordinates.key D.E L).2))

lemma measurable_focalKey (i : Fin m) : Measurable (D.focalKey i) :=
  measurable_const.prodMk
    ((((measurable_of_countable (fun A : Finset (Fin m) => A.erase i)).comp
      (measurable_ids D.E 1)).prodMk (measurable_ids D.E 2)).prodMk (measurable_key D.E).snd)

def zeroFocal (N : ℕ) (H0 H1 : Fin (m+1)) :
    ((Parameters N H0.val D.E.R D.E.Rp D.E.U × ℝ) × Row H0.val D.E.R D.E.Rp D.E.H) →
      unitInterval → Finset (FocalInsertion.Target N H0.val) :=
  fun z u => FocalInsertion.zeroSampler N H0.val H1.val c D.ξ D.E.R D.E.Rp D.E.H
    (regime z.1.1.1.1) (owner0 z.1.1.1.1) (owner1 z.1.1.1.1) (mixed z.1.1.1.1)
    (D.marksLaw H0) (D.marksLaw H1) ((publicBids z.1.1,z.1.2),z.2) u

def oneFocal (N : ℕ) (H0 H1 : Fin (m+1)) :
    ((Parameters N H0.val D.E.R D.E.Rp D.E.U × ℝ) × Row H1.val D.E.R D.E.Rp D.E.H) →
      unitInterval → Finset (FocalInsertion.Target N H1.val) :=
  fun z u => FocalInsertion.oneSampler N H0.val H1.val c D.ξ D.E.R D.E.Rp D.E.H
    (regime z.1.1.1.1) (owner0 z.1.1.1.1) (owner1 z.1.1.1.1) (mixed z.1.1.1.1)
    (D.marksLaw H0) (D.marksLaw H1) ((publicBids z.1.1,z.1.2),z.2) u

lemma measurable_zeroFocal (N : ℕ) (H0 H1 : Fin (m+1)) :
    Measurable (Function.uncurry (D.zeroFocal N H0 H1)) := by
  have hf : Measurable (fun z : Scenario N ×
      ((FocalInsertion.Public N × Row H0.val D.E.R D.E.Rp D.E.H) × unitInterval) =>
      FocalInsertion.zeroSampler N H0.val H1.val c D.ξ D.E.R D.E.Rp D.E.H
        (regime z.1) (owner0 z.1) (owner1 z.1) (mixed z.1)
        (D.marksLaw H0) (D.marksLaw H1) z.2.1 z.2.2) :=
    measurable_from_prod_countable_right fun s => FocalInsertion.measurable_zeroSampler _ _ _ _ _ _ _ _
      (regime s) (owner0 s) (owner1 s) (mixed s) (D.marksLaw H0) (D.marksLaw H1)
  let Ω := (((Parameters N H0.val D.E.R D.E.Rp D.E.U × ℝ) × Row H0.val D.E.R D.E.Rp D.E.H) × unitInterval)
  have hp : Measurable (fun z : Ω => z.1.1.1) := measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hy : Measurable (fun z : Ω => z.1.1.2) := measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hr : Measurable (fun z : Ω => z.1.2) := measurable_snd.comp measurable_fst
  have h := hf.comp (hp.fst.fst.prodMk
    ((((measurable_publicBids.comp hp).prodMk hy).prodMk hr).prodMk measurable_snd))
  change Measurable (fun z : Ω => D.zeroFocal N H0 H1 z.1 z.2)
  simpa only [Function.comp_def,Function.uncurry,zeroFocal] using h

lemma measurable_oneFocal (N : ℕ) (H0 H1 : Fin (m+1)) :
    Measurable (Function.uncurry (D.oneFocal N H0 H1)) := by
  have hf : Measurable (fun z : Scenario N ×
      ((FocalInsertion.Public N × Row H1.val D.E.R D.E.Rp D.E.H) × unitInterval) =>
      FocalInsertion.oneSampler N H0.val H1.val c D.ξ D.E.R D.E.Rp D.E.H
        (regime z.1) (owner0 z.1) (owner1 z.1) (mixed z.1)
        (D.marksLaw H0) (D.marksLaw H1) z.2.1 z.2.2) :=
    measurable_from_prod_countable_right fun s => FocalInsertion.measurable_oneSampler _ _ _ _ _ _ _ _
      (regime s) (owner0 s) (owner1 s) (mixed s) (D.marksLaw H0) (D.marksLaw H1)
  let Ω := (((Parameters N H0.val D.E.R D.E.Rp D.E.U × ℝ) × Row H1.val D.E.R D.E.Rp D.E.H) × unitInterval)
  have hp : Measurable (fun z : Ω => z.1.1.1) := measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hy : Measurable (fun z : Ω => z.1.1.2) := measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hr : Measurable (fun z : Ω => z.1.2) := measurable_snd.comp measurable_fst
  have h := hf.comp (hp.fst.fst.prodMk
    ((((measurable_publicBids.comp hp).prodMk hy).prodMk hr).prodMk measurable_snd))
  change Measurable (fun z : Ω => D.oneFocal N H0 H1 z.1 z.2)
  simpa only [Function.comp_def,Function.uncurry,oneFocal] using h

def FocalUse (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) : Prop :=
  FocalInsertion.Use N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.width
    (D.marksLaw H0) (D.marksLaw H1) p

lemma measurableSet_focalUse (N : ℕ) (H0 H1 : Fin (m+1)) :
    MeasurableSet {p | D.FocalUse N H0 H1 p} :=
  FocalInsertion.measurableSet_use _ _ _ _ _ _ _ _ _ _ _

lemma focal_card (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (y : ℝ) (hp : D.FocalUse N H0 H1 p) :
    (∀ row u,(D.zeroFocal N H0 H1 ((p,y),row) u).card=c) ∧
    (∀ row u,(D.oneFocal N H0 H1 ((p,y),row) u).card=c) := by
  obtain ⟨hs,hg0,hg1,hp0,hp1⟩ := hp.2
  exact FocalInsertion.pair_sampler_card N H0.val H1.val c (regime p.1.1)
    (owner0 p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) y
    (D.marksLaw H0) (D.marksLaw H1) D.xi_pos D.xi_lt_one.le
    (fun i => (p.1.2 i).2) hs hg0 hg1

def FocalUseAtKey (j : Fin 2) (K : FocalKey m) (L : LocalList m) : Prop :=
  if j=0 then D.FocalUse K.2.1.1.card (D.finiteCount K.2.1.2) K.2.2
    (D.parameter K.2.1.1 (D.finiteCount K.2.1.2) K.2.2 L)
  else D.FocalUse K.2.1.1.card K.2.2 (D.finiteCount K.2.1.2)
    (D.parameter K.2.1.1 K.2.2 (D.finiteCount K.2.1.2) L)

lemma measurableSet_focalUseAtKey (j : Fin 2) (K : FocalKey m) :
    MeasurableSet {L | D.FocalUseAtKey j K L} := by
  by_cases hj : j=0
  · simpa only [FocalUseAtKey,if_pos hj,Set.preimage_setOf_eq] using
      (D.measurableSet_focalUse K.2.1.1.card (D.finiteCount K.2.1.2) K.2.2).preimage
        (D.parameter_measurable K.2.1.1 (D.finiteCount K.2.1.2) K.2.2)
  · simpa only [FocalUseAtKey,if_neg hj,Set.preimage_setOf_eq] using
      (D.measurableSet_focalUse K.2.1.1.card K.2.2 (D.finiteCount K.2.1.2)).preimage
        (D.parameter_measurable K.2.1.1 K.2.2 (D.finiteCount K.2.1.2))

def focalAtKey (j : Fin 2) (K : FocalKey m) (L : LocalList m) (u : unitInterval) : Finset (Fin m) :=
  if hAP : Disjoint K.2.1.1 K.2.1.2 then
    if hi : K.1∉K.2.1.1∪K.2.1.2 then
      if D.FocalUseAtKey j K L then
        if j=0 then
          FocalIdentity.transport K.1 K.2.1.1 K.2.1.2 hAP hi (bidVector L) (privateKey D.E L)
            (D.zeroFocal K.2.1.1.card (D.finiteCount K.2.1.2) K.2.2
              ((D.parameter K.2.1.1 (D.finiteCount K.2.1.2) K.2.2 L,entryBid (L K.1)),
                privateRow D.E K.2.1.2 L) u)
        else
          FocalIdentity.transport K.1 K.2.1.1 K.2.1.2 hAP hi (bidVector L) (privateKey D.E L)
            (D.oneFocal K.2.1.1.card K.2.2 (D.finiteCount K.2.1.2)
              ((D.parameter K.2.1.1 K.2.2 (D.finiteCount K.2.1.2) L,entryBid (L K.1)),
                privateRow D.E K.2.1.2 L) u)
      else ∅
    else ∅
  else ∅

lemma focalAtKey_capacity (j : Fin 2) (K : FocalKey m) (L : LocalList m) (u : unitInterval) :
    (D.focalAtKey j K L u).card≤ c := by
  by_cases hd : Disjoint K.2.1.1 K.2.1.2
  · by_cases hi : K.1∉K.2.1.1∪K.2.1.2
    · by_cases hu : D.FocalUseAtKey j K L
      · by_cases hj : j=0
        · simp only [focalAtKey,dif_pos hd,dif_pos hi,if_pos hu,if_pos hj,FocalIdentity.transport_card]
          exact ((D.focal_card K.2.1.1.card (D.finiteCount K.2.1.2) K.2.2 _ _
            (by simpa [FocalUseAtKey,hj] using hu)).1 _ u).le
        · simp only [focalAtKey,dif_pos hd,dif_pos hi,if_pos hu,if_neg hj,FocalIdentity.transport_card]
          exact ((D.focal_card K.2.1.1.card K.2.2 (D.finiteCount K.2.1.2) _ _
            (by simpa [FocalUseAtKey,hj] using hu)).2 _ u).le
      · simp [focalAtKey,hd,hi,hu]
    · simp only [focalAtKey,dif_pos hd,dif_neg hi,Finset.card_empty,Nat.zero_le]
  · simp only [focalAtKey,dif_neg hd,Finset.card_empty,Nat.zero_le]

lemma focalAtKey_subset (j : Fin 2) (K : FocalKey m) (L : LocalList m) (u : unitInterval) :
    D.focalAtKey j K L u⊆insert K.1 (K.2.1.1∪K.2.1.2) := by
  unfold focalAtKey
  split_ifs <;> first | exact FocalIdentity.transport_subset _ _ _ _ _ _ _ _ | exact Finset.empty_subset _

lemma focalAtKey_measurable (j : Fin 2) (K : FocalKey m) :
    Measurable (Function.uncurry (D.focalAtKey j K)) := by
  change Measurable (fun z : LocalList m×unitInterval => D.focalAtKey j K z.1 z.2)
  by_cases hd : Disjoint K.2.1.1 K.2.1.2
  · by_cases hi : K.1∉K.2.1.1∪K.2.1.2
    · simp only [focalAtKey,dif_pos hd,dif_pos hi]
      apply Measurable.ite ((D.measurableSet_focalUseAtKey j K).preimage measurable_fst) _ measurable_const
      by_cases hj : j=0
      · simp only [if_pos hj]
        have hm : Measurable (fun z : LocalList m×unitInterval =>
            (((D.parameter K.2.1.1 (D.finiteCount K.2.1.2) K.2.2 z.1,entryBid (z.1 K.1)),
              privateRow D.E K.2.1.2 z.1),z.2)) :=
          (((((D.parameter_measurable K.2.1.1 (D.finiteCount K.2.1.2) K.2.2).comp measurable_fst).prodMk
            ((measurable_entryBid.comp (measurable_pi_apply K.1)).comp measurable_fst)).prodMk
              ((measurable_privateRow D.E K.2.1.2).comp measurable_fst)).prodMk measurable_snd)
        have hs := (D.measurable_zeroFocal K.2.1.1.card (D.finiteCount K.2.1.2) K.2.2).comp hm
        have hsel : Measurable (fun z : LocalList m×unitInterval =>
            D.zeroFocal K.2.1.1.card (D.finiteCount K.2.1.2) K.2.2
              ((D.parameter K.2.1.1 (D.finiteCount K.2.1.2) K.2.2 z.1,entryBid (z.1 K.1)),
                privateRow D.E K.2.1.2 z.1) z.2) := by
          simp only [Function.comp_def,Function.uncurry] at hs
          convert! hs using 1
        exact FocalIdentity.measurable_transport K.1 K.2.1.1 K.2.1.2 hd hi
          (fun z : LocalList m×unitInterval => bidVector z.1) (fun z => privateKey D.E z.1)
          (fun i => (measurable_pi_apply i).comp (measurable_bidVector.comp measurable_fst))
          (fun i => (measurable_pi_apply i).comp ((measurable_privateKey D.E).comp measurable_fst)) _ hsel
      · simp only [if_neg hj]
        have hm : Measurable (fun z : LocalList m×unitInterval =>
            (((D.parameter K.2.1.1 K.2.2 (D.finiteCount K.2.1.2) z.1,entryBid (z.1 K.1)),
              privateRow D.E K.2.1.2 z.1),z.2)) :=
          (((((D.parameter_measurable K.2.1.1 K.2.2 (D.finiteCount K.2.1.2)).comp measurable_fst).prodMk
            ((measurable_entryBid.comp (measurable_pi_apply K.1)).comp measurable_fst)).prodMk
              ((measurable_privateRow D.E K.2.1.2).comp measurable_fst)).prodMk measurable_snd)
        have hs := (D.measurable_oneFocal K.2.1.1.card K.2.2 (D.finiteCount K.2.1.2)).comp hm
        have hsel : Measurable (fun z : LocalList m×unitInterval =>
            D.oneFocal K.2.1.1.card K.2.2 (D.finiteCount K.2.1.2)
              ((D.parameter K.2.1.1 K.2.2 (D.finiteCount K.2.1.2) z.1,entryBid (z.1 K.1)),
                privateRow D.E K.2.1.2 z.1) z.2) := by
          simp only [Function.comp_def,Function.uncurry] at hs
          convert! hs using 1
        exact FocalIdentity.measurable_transport K.1 K.2.1.1 K.2.1.2 hd hi
          (fun z : LocalList m×unitInterval => bidVector z.1) (fun z => privateKey D.E z.1)
          (fun i => (measurable_pi_apply i).comp (measurable_bidVector.comp measurable_fst))
          (fun i => (measurable_pi_apply i).comp ((measurable_privateKey D.E).comp measurable_fst)) _ hsel
    · simp only [focalAtKey,dif_pos hd,dif_neg hi]
      exact measurable_const
  · simp only [focalAtKey,dif_neg hd]
    exact measurable_const

def UseFocal (j : Fin 2) (i : Fin m) (L : LocalList m) : Prop :=
  D.offCommon L={i} ∧ D.FocalUseAtKey j (D.focalKey i L) L

lemma measurableSet_useFocal (j : Fin 2) (i : Fin m) : MeasurableSet {L | D.UseFocal j i L} := by
  apply (measurableSet_eq_fun D.measurable_offCommon measurable_const).inter
  change MeasurableSet {L : LocalList m | D.FocalUseAtKey j (D.focalKey i L) L}
  have he : {L | D.FocalUseAtKey j (D.focalKey i L) L}=
      ⋃ K : FocalKey m,{L | D.focalKey i L=K}∩{L | D.FocalUseAtKey j K L} := by
    ext L
    simp
  rw [he]
  exact MeasurableSet.iUnion fun K =>
    (measurableSet_eq_fun (D.measurable_focalKey i) measurable_const).inter (D.measurableSet_focalUseAtKey j K)

def focalSelection (j : Fin 2) (i : Fin m) (L : LocalList m) (u : unitInterval) : Finset (Fin m) :=
  if D.UseFocal j i L then D.focalAtKey j (D.focalKey i L) L u else ∅

lemma focalSelection_capacity (j : Fin 2) (i : Fin m) (L : LocalList m) (u : unitInterval) :
    (D.focalSelection j i L u).card≤ c := by
  unfold focalSelection
  split_ifs
  · exact D.focalAtKey_capacity j _ L u
  · simp

lemma focalSelection_present (j : Fin 2) (i : Fin m) (L : LocalList m) (u : unitInterval)
    (k : Fin m) (hk : k∈D.focalSelection j i L u) : L k≠none := by
  by_cases hu : D.UseFocal j i L
  · simp only [focalSelection,if_pos hu] at hk
    have hs := D.focalAtKey_subset j (D.focalKey i L) L u hk
    have hi : i∈ids D.E 1 L := ((D.offCommon_mem L i).mp (by rw [hu.1];simp)).1
    rcases Finset.mem_insert.mp hs with hkf | hs
    · have hki : k=i := hkf
      subst k
      exact ids_present D.E 1 (by decide) L i hi
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact ids_present D.E 1 (by decide) L k (Finset.mem_of_mem_erase hs)
      · exact ids_present D.E 2 (by decide) L k hs
  · simp [focalSelection,hu] at hk

def focalPolicy (j : Fin 2) (i : Fin m) : LocalPolicy m c NativeLocalPolicy.Seed :=
  fun L u => ⟨D.focalSelection j i L u.1,D.focalSelection_capacity j i L u.1,
    D.focalSelection_present j i L u.1⟩

lemma focalPolicy_measurable (j : Fin 2) (i : Fin m) :
    Measurable (fun z : LocalList m×NativeLocalPolicy.Seed => (D.focalPolicy j i z.1 z.2).val) := by
  change Measurable (fun z : LocalList m×NativeLocalPolicy.Seed => D.focalSelection j i z.1 z.2.1)
  have hk : Measurable (fun z : FocalKey m×(LocalList m×unitInterval) => D.focalAtKey j z.1 z.2.1 z.2.2) :=
    measurable_from_prod_countable_right (D.focalAtKey_measurable j)
  have hm : Measurable (fun z : LocalList m×NativeLocalPolicy.Seed =>
      (D.focalKey i z.1,(z.1,z.2.1))) :=
    ((D.measurable_focalKey i).comp measurable_fst).prodMk
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hf : Measurable (fun z : LocalList m×NativeLocalPolicy.Seed =>
      D.focalAtKey j (D.focalKey i z.1) z.1 z.2.1) := by
    simpa only [Function.comp_def] using hk.comp hm
  exact Measurable.ite ((D.measurableSet_useFocal j i).preimage measurable_fst) hf measurable_const

end FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
