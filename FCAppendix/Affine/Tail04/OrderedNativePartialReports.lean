import FCAppendix.Affine.Tail04.NativePartialReports
import FCAppendix.Affine.Tail04.OrderedNativePrivateCount

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePartialReports
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy Hybrid

variable {m c : ℕ} (D : Data m c)

def localRegime (j : Fin 2) (L : LocalList m) : Bool :=
  NativePartialReports.localRegime D (OrderedNativePolicy.role D.E j L) L

def localGood (j : Fin 2) (L : LocalList m) : Prop :=
  NativePartialReports.localGood D (OrderedNativePolicy.role D.E j L) L

lemma measurable_localRegime (j : Fin 2) : Measurable (localRegime D j) := by
  have hf : Measurable (fun z : Fin 2×LocalList m =>
      NativePartialReports.localRegime D z.1 z.2) :=
    measurable_from_prod_countable_right (NativePartialReports.measurable_localRegime D)
  exact hf.comp ((OrderedNativePolicy.measurable_role D.E j).prodMk measurable_id)

lemma measurableSet_localGood (j : Fin 2) : MeasurableSet {L | localGood D j L} := by
  have he : {L | localGood D j L}=⋃ r : Fin 2,
      {L | OrderedNativePolicy.role D.E j L=r}∩{L | NativePartialReports.localGood D r L} := by
    ext L
    simp [localGood]
  rw [he]
  exact MeasurableSet.iUnion (fun r =>
    (measurableSet_eq_fun (OrderedNativePolicy.measurable_role D.E j) measurable_const).inter
      (NativePartialReports.measurableSet_localGood D r))

lemma role_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    OrderedNativePolicy.role D.E j (Function.update L i (some b'))=
      OrderedNativePolicy.role D.E j L := by
  unfold OrderedNativePolicy.role
  rw [PrivateUpdate.count_update D L i hi hb hb' 2,
    PrivateUpdate.otherCount_update D L i hi hb hb']

lemma localRegime_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    localRegime D j (Function.update L i (some b'))=localRegime D j L := by
  unfold localRegime
  rw [role_update D j L i hi hb hb']
  exact NativePartialReports.localRegime_update D _ L i hi hb hb'

lemma localGood_update (j : Fin 2) (L : LocalList m) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp) :
    localGood D j (Function.update L i (some b')) ↔ localGood D j L := by
  unfold localGood
  rw [role_update D j L i hi hb hb']
  exact NativePartialReports.localGood_update D _ L i hi hb hb'

theorem completed_private_on_good (j : Fin 2) (L : LocalList m)
    (i : Fin m) (price : Icc D.E.R D.E.Rp) (hi : L i=some price)
    (hg : localGood D j L) (u : Seed) :
    (i∈(OrderedNativePolicy.policy D j L u).val) ↔ localRegime D j L=false :=
  NativePartialReports.completed_private_on_good D (OrderedNativePolicy.role D.E j L)
    L i price hi hg u

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
    (hpolicy : ∀ j,Γ.policy j=OrderedNativePolicy.policy D j)

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

end FCAppendix.Affine.Tail04.OrderedNativePartialReports
