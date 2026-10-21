import FCAppendix.Affine.Tail04.NativeFullReceipts

noncomputable section
namespace FCAppendix.Affine.Tail04.PrivateUpdate
open MeasureTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalCoordinates SortedCoordinates JoinedHighPolicy
open FCAppendix.Affine.Hybrid

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

lemma tag_partial {b : ℝ} (hb : b∈Icc D.E.R D.E.Rp) : D.E.localTag (some b)=2 := by
  have hd : ¬ b≤ D.E.d := not_le.mpr (D.E.d_lt_R.trans_le hb.1)
  have hp : b∈D.E.privateBids := Or.inl hb
  simp [Observable.Regions.localTag,hd,hp]

lemma tag_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    (fun k => D.E.localTag (Function.update L i (some b') k))=
      fun k => D.E.localTag (L k) := by
  funext k
  by_cases hk : k=i
  · subst k
    simp [hi,tag_partial D hb,tag_partial D hb']
  · simp [Function.update_of_ne hk]

lemma ids_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) (t : Fin 4) :
    ids D.E t (Function.update L i (some b'))=ids D.E t L := by
  unfold ids
  congr 1
  funext k
  rw [congrFun (tag_update D L i hi hb hb') k]

lemma count_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) (t : Fin 4) :
    D.E.localCount (Function.update L i (some b')) t=D.E.localCount L t := by
  rw [←ids_card,←ids_card,ids_update D L i hi hb hb' t]

lemma roleList_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp)
    (t : Fin 4) (ht : t≠2) :
    D.E.roleList t (Function.update L i (some b'))=D.E.roleList t L := by
  funext k
  by_cases hk : k=i
  · subst k
    simp [Observable.Regions.roleList,hi,tag_partial D hb,tag_partial D hb',Ne.symm ht]
  · simp [Observable.Regions.roleList,Function.update_of_ne hk]

lemma otherCount_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    D.E.otherPrivateCount (Function.update L i (some b'))=D.E.otherPrivateCount L := by
  simp only [Observable.Regions.otherPrivateCount,count_update D L i hi hb hb']

lemma key_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    LocalCoordinates.key D.E (Function.update L i (some b'))=LocalCoordinates.key D.E L := by
  apply Prod.ext
  · exact Prod.ext (ids_update D L i hi hb hb' 1) (ids_update D L i hi hb hb' 2)
  · exact Fin.ext (otherCount_update D L i hi hb hb')

lemma update_eq_on_active (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (k : Fin m) (hk : k∈ids D.E 1 L) :
    Function.update L i (some b') k=L k := by
  have hn : k≠i := by
    intro he
    subst k
    have ht := (Finset.mem_filter.mp hk).2
    simp [hi,tag_partial D hb] at ht
  exact Function.update_of_ne hn _ _

lemma activeBids_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) :
    activeBids D.E (ids D.E 1 L) (Function.update L i (some b'))=
      activeBids D.E (ids D.E 1 L) L := by
  have hbids : ∀ k∈ids D.E 1 L,
      bidVector (Function.update L i (some b')) k=bidVector L k := by
    intro k hk
    simp only [bidVector,update_eq_on_active D L i hi hb k hk]
  have he := enumerate_congr (ids D.E 1 L) _ _ hbids
  funext k
  apply Subtype.ext
  change clamp 1 D.E.U (entryBid (Function.update L i (some b')
    (enumerate (ids D.E 1 L) (bidVector (Function.update L i (some b'))) k)))=_
  rw [he,update_eq_on_active D L i hi hb _ (enumerate (ids D.E 1 L) (bidVector L) k).2]
  rfl

lemma parameter_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp)
    (H0 H1 : Fin (m+1)) :
    D.parameter (ids D.E 1 L) H0 H1 (Function.update L i (some b'))=
      D.parameter (ids D.E 1 L) H0 H1 L := by
  simp only [NativeLocalPolicy.Data.parameter,activeBids_update D L i hi hb,
    roleList_update D L i hi hb hb' 0 (by decide)]

lemma highReceipt_other (j : Fin 2) (L : LocalList m) (i k : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp)
    (hik : k≠i) :
    D.highReceipt j (Function.update L i (some b')) k=D.highReceipt j L k := by
  let L' := Function.update L i (some b')
  have ha := ids_update D L i hi hb hb' 1
  have hp := ids_update D L i hi hb hb' 2
  have hk : L' k=L k := Function.update_of_ne hik _ _
  by_cases hkP : k∈ids D.E 2 L
  · have hkP' : k∈ids D.E 2 L' := by simpa only [L',ha,hp] using hkP
    rw [D.highReceipt_private j L' k hkP',D.highReceipt_private j L k hkP,hk]
  · by_cases hkA : k∈ids D.E 1 L
    · have hkA' : k∈ids D.E 1 L' := by simpa only [L',ha] using hkA
      have hr : rankFin (ids D.E 1 L) (bidVector L')=rankFin (ids D.E 1 L) (bidVector L) :=
        rankFin_congr _ _ _ (fun t ht => congrArg entryBid (update_eq_on_active D L i hi hb t ht))
      have hc := congrArg (fun K : LocalCoordinates.Key m=>K.2)
        (key_update D L i hi hb hb')
      dsimp only [LocalCoordinates.key] at hc
      rw [D.highReceipt_active_clipped j L' k hkA',D.highReceipt_active_clipped j L k hkA,hk]
      dsimp only [L'] at hr hkA' ⊢
      simp only [NativeLocalPolicy.Data.oppositeActiveMean,LocalCoordinates.key]
      revert hkA'
      rw [ha,hp,hc]
      intro hkA'
      simp only [parameter_update D L i hi hb hb',hr]
    · have hn : k∉ids D.E 1 L∪ids D.E 2 L := by simp [hkA,hkP]
      have hn' : k∉ids D.E 1 L'∪ids D.E 2 L' := by simpa only [L',ha,hp] using hn
      rw [D.highReceipt_zero j L' k hn',D.highReceipt_zero j L k hn]

lemma highReceipt_focal (j : Fin 2) (L : LocalList m) (i : Fin m) {b' : ℝ}
    (hb' : b'∈Icc D.E.R D.E.Rp) :
    D.highReceipt j (Function.update L i (some b')) i=b' := by
  have hi : i∈ids D.E 2 (Function.update L i (some b')) := by
    simp [ids,tag_partial D hb']
  rw [D.highReceipt_private j _ i hi]
  simp [entryBid]

lemma lowContext_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    Observable.Regions.lowContext D.E j (Function.update L i (some b'))=
      Observable.Regions.lowContext D.E j L := by
  simp only [Observable.Regions.lowContext,Observable.Regions.context,
    roleList_update D L i hi hb hb' 0 (by decide),roleList_update D L i hi hb hb' 1 (by decide),
    count_update D L i hi hb hb',otherCount_update D L i hi hb hb']

lemma lowReceipt_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    D.lowReceipt j (Function.update L i (some b'))=D.lowReceipt j L := by
  simp only [NativeLocalPolicy.Data.lowReceipt,lowContext_update D j L i hi hb hb']

theorem numericalReceipt_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    D.numericalReceipt j (Function.update L i (some b'))=
      Function.update (D.numericalReceipt j L) i b' := by
  funext k
  by_cases hk : k=i
  · subst k
    have hf : i∈ids D.E 2 (Function.update L i (some b')) := by simp [ids,tag_partial D hb']
    rw [D.numericalReceipt_private j _ i hf]
    simp [entryBid]
  · simp only [Function.update_of_ne hk,NativeLocalPolicy.Data.numericalReceipt,
      highReceipt_other D j L i k hi hb hb' hk,lowReceipt_update D j L i hi hb hb']

end FCAppendix.Affine.Tail04.PrivateUpdate
