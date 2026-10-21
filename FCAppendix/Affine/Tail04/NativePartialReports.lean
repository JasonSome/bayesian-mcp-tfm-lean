import FCAppendix.Affine.Tail04.PrivateUpdate
import FCAppendix.Affine.Tail04.NativePolicyFactor
import FCAppendix.Affine.Tail04.JoinedPartialNoisy
import FCAppendix.Affine.Tail04.RawRouteCounts
import FCAppendix.Affine.Tail04.NativeDeletedCounts

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePartialReports
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair
open JoinedHighPolicy EqualPrivateSignal EqualPrivateUpper Hybrid
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (D : Data m c)

def regimeAtKey (j : Fin 2) (K : Key m) (L : LocalList m) : Bool :=
  if j=0 then JoinedHighPolicy.regime
    (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L).1.1
  else JoinedHighPolicy.regime
    (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L).1.1

def goodAtKey (j : Fin 2) (K : Key m) (L : LocalList m) : Prop :=
  D.finiteCount K.1.2≠K.2 ∧
    if j=0 then UseTypical K.1.1.card K.1.2.card K.2.val c D.ξ D.E.U D.E.R D.E.Rp D.width
      (D.marksLaw (D.finiteCount K.1.2)) (D.marksLaw K.2)
      (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L)
    else UseTypical K.1.1.card K.2.val K.1.2.card c D.ξ D.E.U D.E.R D.E.Rp D.width
      (D.marksLaw K.2) (D.marksLaw (D.finiteCount K.1.2))
      (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L)

def localRegime (j : Fin 2) (L : LocalList m) : Bool :=
  regimeAtKey D j (key D.E L) L

def localGood (j : Fin 2) (L : LocalList m) : Prop :=
  D.offCommon L=∅ ∧ goodAtKey D j (key D.E L) L

lemma measurable_regimeAtKey (j : Fin 2) (K : Key m) : Measurable (regimeAtKey D j K) := by
  change Measurable (fun L : LocalList m => regimeAtKey D j K L)
  by_cases hj : j=0
  · simp only [regimeAtKey,if_pos hj]
    exact measurable_fst.comp ((D.parameter_measurable K.1.1 (D.finiteCount K.1.2) K.2).fst.fst)
  · simp only [regimeAtKey,if_neg hj]
    exact measurable_fst.comp ((D.parameter_measurable K.1.1 K.2 (D.finiteCount K.1.2)).fst.fst)

lemma measurableSet_goodAtKey (j : Fin 2) (K : Key m) : MeasurableSet {L | goodAtKey D j K L} := by
  have hconst : MeasurableSet {L : LocalList m | D.finiteCount K.1.2≠K.2} := by
    by_cases hn : D.finiteCount K.1.2=K.2 <;> simp [hn]
  by_cases hj : j=0
  · simp only [goodAtKey,if_pos hj]
    convert! hconst.inter ((measurableSet_useTypical _ _ _ _ _ _ _ _ _ _ _).preimage
      (D.parameter_measurable K.1.1 (D.finiteCount K.1.2) K.2)) using 1
  · simp only [goodAtKey,if_neg hj]
    convert! hconst.inter ((measurableSet_useTypical _ _ _ _ _ _ _ _ _ _ _).preimage
      (D.parameter_measurable K.1.1 K.2 (D.finiteCount K.1.2))) using 1

lemma measurable_localRegime (j : Fin 2) : Measurable (localRegime D j) := by
  have hf : Measurable (fun z : Key m×LocalList m => regimeAtKey D j z.1 z.2) :=
    measurable_from_prod_countable_right (measurable_regimeAtKey D j)
  exact hf.comp ((measurable_key D.E).prodMk measurable_id)

lemma measurableSet_localGood (j : Fin 2) : MeasurableSet {L | localGood D j L} := by
  apply (measurableSet_eq_fun D.measurable_offCommon measurable_const).inter
  change MeasurableSet {L | goodAtKey D j (key D.E L) L}
  have he : {L | goodAtKey D j (key D.E L) L}=
      ⋃ K : Key m,{L | key D.E L=K}∩{L | goodAtKey D j K L} := by
    ext L
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun K =>
    (measurableSet_eq_fun (measurable_key D.E) measurable_const).inter
      (measurableSet_goodAtKey D j K))

lemma offCommon_update (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    D.offCommon (Function.update L i (some b'))=D.offCommon L := by
  ext k
  by_cases hk : k=i
  · subst k
    simp [Data.offCommon,hi,PrivateUpdate.tag_partial D hb,PrivateUpdate.tag_partial D hb']
  · simp [Data.offCommon,Function.update_of_ne hk]

lemma localRegime_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    localRegime D j (Function.update L i (some b'))=localRegime D j L := by
  unfold localRegime
  rw [PrivateUpdate.key_update D L i hi hb hb']
  unfold regimeAtKey
  dsimp only [LocalCoordinates.key]
  split_ifs <;> rw [PrivateUpdate.parameter_update D L i hi hb hb']

lemma localGood_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    localGood D j (Function.update L i (some b')) ↔ localGood D j L := by
  unfold localGood
  rw [offCommon_update D L i hi hb hb',PrivateUpdate.key_update D L i hi hb hb']
  unfold goodAtKey
  dsimp only [LocalCoordinates.key]
  split_ifs <;> rw [PrivateUpdate.parameter_update D L i hi hb hb']

lemma decode_partial (b : Icc D.E.R D.E.Rp) : LocalCoordinates.decode D.E b=Sum.inr b := by
  have hn : ¬D.E.H≤(b:ℝ) := not_le.mpr
    (b.2.2.trans_lt (D.E.Rp_lt_one.trans_le D.E.one_le_U |>.trans D.E.U_lt_H))
  simp only [LocalCoordinates.decode,if_neg hn]
  congr 1
  exact Subtype.ext (clamp_eq b.2)

lemma mem_transport_private (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (b k : Fin m → ℝ) (S : Finset (Target A.card P.card)) (i : Fin m) (hi : i∈P) :
    i∈transport A P hAP b k S ↔ Sum.inr (rankFin P k ⟨i,hi⟩)∈S := by
  simpa [targetEmbedding]
    using mem_transport A P hAP b k S (Sum.inr (rankFin P k ⟨i,hi⟩))

theorem completed_private_on_good (j : Fin 2) (L : LocalList m)
    (i : Fin m) (price : Icc D.E.R D.E.Rp) (hi : L i=some price)
    (hg : localGood D j L) (u : Seed) :
    (i∈(D.completedPolicy j L u).val) ↔ localRegime D j L=false := by
  have ht : D.E.localTag (L i)=2 := by rw [hi];exact PrivateUpdate.tag_partial D price.2
  have hiP : i∈ids D.E 2 L := by simp [ids,ht]
  have hd : Disjoint (ids D.E 1 L) (ids D.E 2 L) := ids_disjoint D.E (by decide) L
  let H0 := D.finiteCount (ids D.E 2 L)
  let H1 := D.finiteCount (ids D.E 3 L)
  have hkey : (key D.E L).2=D.finiteCount (ids D.E 3 L) :=
    congrArg Prod.snd (D.key_self L)
  let k : Fin (ids D.E 2 L).card := rankFin (ids D.E 2 L) (privateKey D.E L) ⟨i,hiP⟩
  have hreg : localRegime D j L=regimeAtKey D j ((ids D.E 1 L,ids D.E 2 L),D.finiteCount (ids D.E 3 L)) L := by
    unfold localRegime
    rw [D.key_self L]
  have hrow : privateRow D.E (ids D.E 2 L) L k=Sum.inr price := by
    simp only [privateRow,k,enumerate_rank]
    rw [hi]
    exact decode_partial D price
  have hgKey := hg.2
  unfold goodAtKey at hgKey
  rw [hkey] at hgKey
  dsimp only [LocalCoordinates.key] at hgKey
  have hneq : H0≠H1 := by
    simpa only [goodAtKey,hkey,LocalCoordinates.key,H0,H1] using hgKey.1
  rw [D.completed_on_menu j L hg.1 u,D.policy_high_iff j L u i (by simp [ht])]
  unfold Data.high
  rw [D.key_self L]
  by_cases hj : j=0
  · have htyp : UseTypical (ids D.E 1 L).card H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.width
      (D.marksLaw H0) (D.marksLaw H1) (D.parameter (ids D.E 1 L) H0 H1 L) := by
      simpa only [goodAtKey,hkey,LocalCoordinates.key,if_pos hj,H0,H1,Data.finiteCount] using hgKey.2
    simp only [Data.highAtKey,dif_pos hd,if_pos hj]
    rw [mem_transport_private _ _ hd _ _ _ i hiP,
      D.zeroSampler_unequal _ H0 H1 hneq]
    have hh := JoinedPartialNoisy.unequalSide_private (ids D.E 1 L).card H0.val H1.val c
      (D.marksLaw H0) (D.marksLaw H1) false D.xi_pos D.xi_lt_one.le D.width_pos
      (D.parameter (ids D.E 1 L) H0 H1 L) (privateRow D.E (ids D.E 2 L) L) k price hrow u.1
    rw [hreg]
    simp only [JoinedPartialNoisy.unequalSide,htyp,if_pos,regimeAtKey,
      if_pos hj,k,H0,H1] at hh ⊢
    convert! hh using 1
  · have htyp : UseTypical (ids D.E 1 L).card H1.val H0.val c D.ξ D.E.U D.E.R D.E.Rp D.width
      (D.marksLaw H1) (D.marksLaw H0) (D.parameter (ids D.E 1 L) H1 H0 L) := by
      simpa only [goodAtKey,hkey,LocalCoordinates.key,if_neg hj,H0,H1,Data.finiteCount] using hgKey.2
    simp only [Data.highAtKey,dif_pos hd,if_neg hj]
    rw [mem_transport_private _ _ hd _ _ _ i hiP,
      D.oneSampler_unequal _ H1 H0 (Ne.symm hneq)]
    have hh := JoinedPartialNoisy.unequalSide_private (ids D.E 1 L).card H1.val H0.val c
      (D.marksLaw H1) (D.marksLaw H0) true D.xi_pos D.xi_lt_one.le D.width_pos
      (D.parameter (ids D.E 1 L) H1 H0 L) (privateRow D.E (ids D.E 2 L) L) k price hrow u.1
    rw [hreg]
    simp only [JoinedPartialNoisy.unequalSide,htyp,if_pos,regimeAtKey,
      if_neg hj,k,H0,H1] at hh ⊢
    convert! hh using 1

lemma presentList_update (ω : Background m 2 Seed) (i : Fin m) (b b' : ℝ) (j : Fin 2) :
    presentList ω i b' j=Function.update (presentList ω i b j) i (some b') := by
  funext k
  by_cases hk : k=i
  · subst k
    simp only [presentList_self,Function.update_self]
  · simp [presentList,hk]

def goodBackground (i : Fin m) (ω : Background m 2 Seed) : Prop :=
  (∀ j : Fin 2,localGood D j (presentList ω i D.E.R j)) ∧
    localRegime D 0 (presentList ω i D.E.R 0)=
      localRegime D 1 (presentList ω i D.E.R 1)

def backgroundRegime (i : Fin m) (ω : Background m 2 Seed) : Bool :=
  localRegime D 0 (presentList ω i D.E.R 0)

lemma measurableSet_goodBackground (i : Fin m) : MeasurableSet {ω : Background m 2 Seed | goodBackground D i ω} := by
  unfold goodBackground
  apply MeasurableSet.inter
  · convert! MeasurableSet.iInter (fun j : Fin 2 => (measurableSet_localGood D j).preimage
        (measurable_presentList (Seed:=Seed) i D.E.R j)) using 1
    ext ω
    simp
    rfl
  · exact measurableSet_eq_fun
      ((measurable_localRegime D 0).comp (measurable_presentList (Seed:=Seed) i D.E.R 0))
      ((measurable_localRegime D 1).comp (measurable_presentList (Seed:=Seed) i D.E.R 1))

lemma measurable_backgroundRegime (i : Fin m) : Measurable (backgroundRegime D i) :=
  (measurable_localRegime D 0).comp (measurable_presentList (Seed:=Seed) i D.E.R 0)

lemma present_good_all_bids (i : Fin m) (ω : Background m 2 Seed)
    (hg : goodBackground D i ω) (price : Icc D.E.R D.E.Rp) (j : Fin 2) :
    localGood D j (presentList ω i price j) ∧
      localRegime D j (presentList ω i price j)=backgroundRegime D i ω := by
  have hR : D.E.R∈Icc D.E.R D.E.Rp := ⟨le_rfl,D.E.R_le_Rp⟩
  have hi := presentList_self ω i D.E.R j
  constructor
  · rw [presentList_update ω i D.E.R price j,
      localGood_update D j _ i hi hR price.2]
    exact hg.1 j
  · rw [presentList_update ω i D.E.R price j,
      localRegime_update D j _ i hi hR price.2]
    fin_cases j
    · rfl
    · exact hg.2.symm

variable (Γ : FiniteGame m 2 c Seed)
    (hpolicy : ∀ j,Γ.policy j=D.completedPolicy j)

include hpolicy in
theorem accepts_on_good (i : Fin m) (ω : Background m 2 Seed)
    (hg : goodBackground D i ω) (price : Icc D.E.R D.E.Rp) (j : Fin 2) :
    Accepts Γ i price j ω ↔ backgroundRegime D i ω=false := by
  obtain ⟨hg',hr⟩ := present_good_all_bids D i ω hg price j
  change i∈(Γ.policy j (presentList ω i price j) (ω.2 j)).val ↔ _
  rw [hpolicy j,completed_private_on_good D j _ i price (presentList_self _ _ _ _) hg',hr]

include hpolicy in
theorem focalCount_on_good (i : Fin m) (ω : Sample m 2 Seed)
    (hg : goodBackground D i ω.1) (price : Icc D.E.R D.E.Rp) (k : Fin 3) :
    focalCount Γ i (RawRoutes.action price
      ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k) ω=
      if backgroundRegime D i ω.1 then 0 else k := by
  let a := RawRoutes.action price ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k
  have haccept : accepted (deviated i a ω) Γ.policy ω.1.2 i=
      if backgroundRegime D i ω.1 then ∅ else firstK ω.2 k.val := by
    ext j
    have hsub := accepted_subset_recipients (deviated i a ω) Γ.policy ω.1.2 i
    by_cases hj : j∈firstK ω.2 k.val
    · have hlist := observe_deviated_of_mem i a ω j hj
      have hi : j∈accepted (deviated i a ω) Γ.policy ω.1.2 i ↔
          backgroundRegime D i ω.1=false := by
        simp only [accepted,Finset.mem_filter,Finset.mem_univ,true_and,allocation]
        erw [hlist]
        exact accepts_on_good D Γ hpolicy i ω.1 hg price j
      rw [hi]
      cases backgroundRegime D i ω.1 <;> simp [hj]
    · have hn : j∉accepted (deviated i a ω) Γ.policy ω.1.2 i := by
        intro he
        exact hj (by simpa only [deviated_recipients_self,a,RawRoutes.action] using hsub he)
      cases backgroundRegime D i ω.1 <;> simp_all
  apply Fin.ext
  change (accepted (deviated i a ω) Γ.policy ω.1.2 i).card=(if backgroundRegime D i ω.1 then (0:Fin 3) else k).val
  rw [haccept]
  cases backgroundRegime D i ω.1 <;> simp [card_firstK _ _ (show k.val≤2 by omega)]

theorem raw_count_original_deleted {N : ℕ} (D : Data (N+1) c)
    (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1))
    (price : Icc D.E.R D.E.Rp) (k : Fin 3) :
    (problem Γ i).outcome
      (RawRoutes.action price ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k)=
      FiniteLaw.ofMeasure (OriginalFiniteFibers.deletedSampleLaw Γ)
        (NativeDeletedCounts.deletedCount Γ i
          (RawRoutes.action price ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k))
        (NativeDeletedCounts.measurable_deletedCount Γ i _) :=
  NativeDeletedCounts.raw_count_law Γ i _

end FCAppendix.Affine.Tail04.NativePartialReports
