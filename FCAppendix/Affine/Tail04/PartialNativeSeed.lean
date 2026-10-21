import FCAppendix.Affine.Tail04.PartialNativeCategoryBounds
import FCAppendix.Affine.Tail04.OriginalFiniteFibers

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialNativeSeed
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativePartialReports NativeObservationPair NativeMenuReports
open PartialNativeCoordinates PartialNativeEvents PartialNativeCategoryBounds
open LocalCoordinates SortedCoordinates Hybrid OriginalFiniteFibers NativeDeletedCounts
open scoped BigOperators

variable {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

abbrev DeletedBackground (N : ℕ) (Seed : Type*) := (Fin N→ UserDraw 2)×(Fin 2→ Seed)

def deletedBackgroundLaw (Γ : FiniteGame (N+1) 2 c Seed) : Measure (DeletedBackground N Seed) :=
  (Measure.pi (fun _ : Fin N => userLaw Γ)).prod (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))

instance (Γ : FiniteGame (N+1) 2 c Seed) : IsProbabilityMeasure (deletedBackgroundLaw Γ) := by
  unfold deletedBackgroundLaw;infer_instance

def deleteBackground (i : Fin (N+1)) (ω : Background (N+1) 2 Seed) : DeletedBackground N Seed :=
  (NativeFlag.deletedUsers i ω.1,ω.2)

def restoreBackground (i : Fin (N+1)) (z : DeletedBackground N Seed) : Background (N+1) 2 Seed :=
  (restoreUsers i z.1,z.2)

lemma deleteBackground_preserving (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1)) :
    MeasurePreserving (deleteBackground (Seed:=Seed) i) (backgroundLaw Γ) (deletedBackgroundLaw Γ) :=
  (NativeFlag.deletedUsers_measurePreserving Γ i).prod (MeasurePreserving.id _)

lemma measurable_restoreBackground (i : Fin (N+1)) : Measurable (restoreBackground (Seed:=Seed) i) :=
  ((measurable_restoreUsers i).comp measurable_fst).prodMk measurable_snd

omit [MeasurableSpace Seed] in
lemma restoreBackground_rival (i : Fin (N+1)) (z : DeletedBackground N Seed) (r : Fin N) :
    (restoreBackground i z).1 (i.succAbove r)=z.1 r := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => UserDraw 2) i
  have h := congrArg (fun q => q.2 r) (e.apply_symm_apply (dummyDraw,z.1))
  exact h

omit [MeasurableSpace Seed] in
lemma present_restore_delete (i : Fin (N+1)) (ω : Background (N+1) 2 Seed)
    (b : ℝ) (j : Fin 2) :
    presentList (restoreBackground i (deleteBackground i ω)) i b j=presentList ω i b j := by
  funext l
  by_cases hl : l=i
  · subst l;simp only [presentList_self]
  · simp only [presentList,if_neg hl,restoreBackground,deleteBackground,restoreUsers_delete,
      observe,drawsRealization,Function.update_of_ne hl]

lemma native_event_deleted (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1))
    (B : Set (Background (N+1) 2 Seed)) (hB : MeasurableSet B)
    (hinv : ∀ ω,restoreBackground i (deleteBackground i ω)∈B ↔ ω∈B) :
    (backgroundLaw Γ).real B=(deletedBackgroundLaw Γ).real (restoreBackground i ⁻¹' B) := by
  have h := congrArg (fun μ : Measure (DeletedBackground N Seed) => μ (restoreBackground i ⁻¹' B))
    (deleteBackground_preserving Γ i).map_eq
  rw [Measure.map_apply (deleteBackground_preserving Γ i).measurable
    (hB.preimage (measurable_restoreBackground i))] at h
  have he : deleteBackground i ⁻¹' (restoreBackground i ⁻¹' B)=B := by
    ext ω;exact hinv ω
  rw [he] at h
  exact congrArg ENNReal.toReal h

section Public
variable (D : Data (N+1) c) (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hpublic : ∀ n z,D.publicChoice n z=PublicScenario.localChoice D.E Q μL n z)

include hpublic in
lemma localBranch_of_seed (j : Fin 2) (L : LocalList (N+1)) (u : unitInterval)
    (hu : Hybrid.seedOnList μL (D.E.roleList 0 L)=some u) :
    localBranch D j L=(PublicScenario.split u).2 := by
  simp only [localBranch,branchAtKey,D.key_self,Data.parameter,hpublic,
    PublicScenario.localChoice,hu,PublicScenario.draw]
  split_ifs <;> rfl

lemma branch_endpoint_null :
    (volume : Measure unitInterval) {u | (PublicScenario.split u).2=(1:unitInterval)}=0 := by
  have hs : MeasurePreserving (fun u : unitInterval => (PublicScenario.split u).2)
      volume volume :=
    measurePreserving_snd.comp ⟨PublicScenario.measurable_split,PublicScenario.split_law⟩
  have h := congrArg (fun μ : Measure unitInterval => μ {1}) hs.map_eq
  rw [Measure.map_apply hs.measurable (measurableSet_singleton 1)] at h
  simpa only [Set.preimage,Set.mem_singleton_iff,measure_singleton] using h

end Public

section Fiber
variable (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed) (D : Data (N+1) c)
    (Q : PublicScenario.Data)
    (hpublic : ∀ n z,D.publicChoice n z=
      PublicScenario.localChoice D.E Q (NativeFlag.nativeLowBidLaw Γ D.E) n z)
    (hcat : ∀ k : Fin 4,(userLaw Γ) (D.E.coarseTag ⁻¹' {k})≠0)
    (hlow : ∀ b,NativeFlag.nativeLowBidLaw Γ D.E {b}=0)
    (hmenu : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,MenuAction D.E x.2)

def fiber (kind : Fin N→ Fin 4) : Measure (DeletedBackground N NativeLocalPolicy.Seed) :=
  cond (deletedBackgroundLaw Γ) (categoryFiber D.E.coarseTag kind×ˢuniv)

lemma fiber_eq (kind : Fin N→ Fin 4) : fiber Γ D kind=
    (Measure.pi (fun r => cond (userLaw Γ) (D.E.coarseTag ⁻¹' {kind r}))).prod
      (Measure.pi (fun _ : Fin 2 => Γ.seedLaw)) := by
  rw [fiber,deletedBackgroundLaw,cond_prod_left,
    conditional_categoryFiber _ _ D.E.measurable_coarseTag]

include hcat in
lemma fiber_isProbabilityMeasure (kind : Fin N→ Fin 4) : IsProbabilityMeasure (fiber Γ D kind) := by
  haveI (r : Fin N) : IsProbabilityMeasure (cond (userLaw Γ) (D.E.coarseTag ⁻¹' {kind r})) :=
    cond_isProbabilityMeasure (hcat (kind r))
  rw [fiber_eq];infer_instance

lemma fiber_shape (kind : Fin N→ Fin 4) :
    ∀ᵐ z ∂fiber Γ D kind,∀ r,D.E.coarseTag (z.1 r)=kind r := by
  have hmem : ∀ᵐ z ∂fiber Γ D kind,z∈categoryFiber D.E.coarseTag kind×ˢuniv := by
    unfold fiber ProbabilityTheory.cond
    apply Measure.ae_smul_measure
    exact ae_restrict_mem ((measurableSet_categoryFiber D.E.coarseTag D.E.measurable_coarseTag kind).prod
      MeasurableSet.univ)
  exact hmem.mono fun z hz r => hz.1 r (mem_univ r)

include hmenu in
lemma fiber_menu (kind : Fin N→ Fin 4) :
    ∀ᵐ z ∂fiber Γ D kind,∀ r,MenuAction D.E (z.1 r).1.2 := by
  have hu : ∀ᵐ x ∂userLaw Γ,MenuAction D.E x.1.2 :=
    (measurePreserving_fst (μ:=Γ.F⊗ₘΓ.σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hmenu
  have hr : ∀ᵐ row ∂Measure.pi (fun _ : Fin N => userLaw Γ),∀ r,MenuAction D.E (row r).1.2 :=
    ae_all_iff.mpr fun r => (measurePreserving_eval (fun _ : Fin N => userLaw Γ) r).quasiMeasurePreserving.ae hu
  have hb : ∀ᵐ z ∂deletedBackgroundLaw Γ,∀ r,MenuAction D.E (z.1 r).1.2 :=
    (measurePreserving_fst (μ:=Measure.pi (fun _ : Fin N => userLaw Γ))
      (ν:=Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).quasiMeasurePreserving.ae hr
  unfold fiber ProbabilityTheory.cond
  exact Measure.ae_smul_measure (ae_restrict_of_ae hb) _

def fiberMinimum (kind : Fin N→ Fin 4) (n : ℕ)
    (e : Fin (n+1)≃{r : Fin N // kind r=0}) (z : DeletedBackground N NativeLocalPolicy.Seed) : unitInterval :=
  conditionalMinimumSeed (NativeFlag.nativeLowBidLaw Γ D.E) n
    (fun r => (z.1 (e r).val).1.2.bid)

lemma measurable_fiberMinimum (kind : Fin N→ Fin 4) (n : ℕ)
    (e : Fin (n+1)≃{r : Fin N // kind r=0}) :
    Measurable (fiberMinimum Γ D kind n e) :=
  (measurable_conditionalMinimumSeed _ n).comp
    (measurable_pi_lambda _ fun r => NativeFlag.measurable_nativeBid.comp
      ((measurable_pi_apply (e r).val).comp measurable_fst))

include hcat hlow in
theorem fiberMinimum_law (kind : Fin N→ Fin 4) (n : ℕ)
    (e : Fin (n+1)≃{r : Fin N // kind r=0}) :
    (fiber Γ D kind).map (fiberMinimum Γ D kind n e)=volume := by
  have h := conditional_low_seed_joint (userLaw Γ) D.E.coarseTag D.E.measurable_coarseTag
    kind 0 (fun r => hcat (kind r)) n e NativeFlag.nativeBid NativeFlag.measurable_nativeBid
    hlow (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))
  haveI (r : {r : Fin N // kind r≠0}) :
      IsProbabilityMeasure (cond (userLaw Γ) (D.E.coarseTag ⁻¹' {kind r.val})) :=
    cond_isProbabilityMeasure (hcat (kind r.val))
  rw [←cond_prod_left] at h
  have he := congrArg (fun μ => μ.map Prod.fst) h
  rw [Measure.map_map measurable_fst (by
    exact ((measurable_fiberMinimum Γ D kind n e).prodMk
      ((measurable_pi_lambda _ fun r : {r : Fin N // kind r≠0} =>
        (measurable_pi_apply r.val).comp measurable_fst).prodMk measurable_snd))),
    Measure.map_fst_prod] at he
  simpa only [fiber,deletedBackgroundLaw,measure_univ,one_smul,Function.comp_def,
    fiberMinimum,NativeFlag.nativeLowBidLaw,NativeFlag.nativeBid] using! he

include hmenu in
theorem fiber_seed_on_present (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (n : ℕ) (e : Fin (n+1)≃{r : Fin N // kind r=0})
    (b : Icc D.E.R D.E.Rp) (side : Fin 2) :
    ∀ᵐ z ∂fiber Γ D kind,
      Hybrid.seedOnList (NativeFlag.nativeLowBidLaw Γ D.E)
        (D.E.roleList 0 (presentList (restoreBackground i z) i b side))=
          some (fiberMinimum Γ D kind n e z) := by
  filter_upwards [fiber_shape Γ D kind,fiber_menu Γ D hmenu kind] with z hz hmz
  have hkind : rivalKinds D.E i (restoreBackground i z)=kind := by
    funext r
    simpa only [rivalKinds,restoreBackground_rival] using hz r
  have hr : ∀ r : Fin N,MenuAction D.E ((restoreBackground i z).1 (i.succAbove r)).1.2 := by
    intro r;simpa only [restoreBackground_rival] using hmz r
  let castLow : {r : Fin N // kind r=0}≃
      {r : Fin N // rivalKinds D.E i (restoreBackground i z) r=0} :=
    { toFun := fun r => ⟨r.val,by rw [hkind];exact r.property⟩
      invFun := fun r => ⟨r.val,by rw [←hkind];exact r.property⟩
      left_inv := fun r => Subtype.ext rfl
      right_inv := fun r => Subtype.ext rfl }
  let e' : Fin (n+1)≃{r : Fin N // rivalKinds D.E i (restoreBackground i z) r=0} := e.trans castLow
  have hs := low_seed_enumeration D.E i (restoreBackground i z) hr b side
    (NativeFlag.nativeLowBidLaw Γ D.E) n e'
  simpa only [e',Equiv.trans_apply,castLow,Equiv.coe_fn_mk,restoreBackground_rival,fiberMinimum] using hs

include Q hpublic hcat hlow hmenu in
theorem positive_low_endpoint_null (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (n : ℕ) (e : Fin (n+1)≃{r : Fin N // kind r=0}) :
    (fiber Γ D kind) (restoreBackground i ⁻¹' endpointEvent D i)=0 := by
  let minSeed := fiberMinimum Γ D kind n e
  have hm := measurable_fiberMinimum Γ D kind n e
  have hLaw := fiberMinimum_law Γ D hcat hlow kind n e
  have he : ∀ᵐ z ∂fiber Γ D kind,
      localBranch D 0 (presentList (restoreBackground i z) i D.E.R 0)=
        (PublicScenario.split (minSeed z)).2 := by
    filter_upwards [fiber_shape Γ D kind,fiber_menu Γ D hmenu kind] with z hz hmz
    have hkind : rivalKinds D.E i (restoreBackground i z)=kind := by
      funext r
      simpa only [rivalKinds,restoreBackground_rival] using hz r
    have hr : ∀ r : Fin N,MenuAction D.E ((restoreBackground i z).1 (i.succAbove r)).1.2 := by
      intro r;simpa only [restoreBackground_rival] using hmz r
    let castLow : {r : Fin N // kind r=0}≃
        {r : Fin N // rivalKinds D.E i (restoreBackground i z) r=0} :=
      { toFun := fun r => ⟨r.val,by rw [hkind];exact r.property⟩
        invFun := fun r => ⟨r.val,by rw [←hkind];exact r.property⟩
        left_inv := fun r => Subtype.ext rfl
        right_inv := fun r => Subtype.ext rfl }
    let e' : Fin (n+1)≃{r : Fin N // rivalKinds D.E i (restoreBackground i z) r=0} :=
      e.trans castLow
    have hs := low_seed_enumeration D.E i (restoreBackground i z) hr
      (⟨D.E.R,le_rfl,D.E.R_le_Rp⟩ : Icc D.E.R D.E.Rp) 0
      (NativeFlag.nativeLowBidLaw Γ D.E) n e'
    have hseed : Hybrid.seedOnList (NativeFlag.nativeLowBidLaw Γ D.E)
        (D.E.roleList 0 (presentList (restoreBackground i z) i D.E.R 0))=some (minSeed z) := by
      simpa only [e',Equiv.trans_apply,castLow,Equiv.coe_fn_mk,restoreBackground_rival,
        minSeed,fiberMinimum] using hs
    exact localBranch_of_seed D Q _ hpublic 0 _ (minSeed z) hseed
  have hset : (restoreBackground i ⁻¹' endpointEvent D i)=ᵐ[fiber Γ D kind]
      {z | (PublicScenario.split (minSeed z)).2=(1:unitInterval)} :=
    he.mono fun z hz => by
      apply propext
      change (localBranch D 0 (presentList (restoreBackground i z) i D.E.R 0)=1) ↔
        (PublicScenario.split (minSeed z)).2=1
      rw [hz]
  rw [measure_congr hset]
  have hs : MeasurableSet {u : unitInterval | (PublicScenario.split u).2=(1:unitInterval)} :=
    measurableSet_eq_fun PublicScenario.measurable_split.snd measurable_const
  have hh := congrArg (fun μ : Measure unitInterval =>
      μ {u | (PublicScenario.split u).2=(1:unitInterval)}) hLaw
  rw [Measure.map_apply hm hs] at hh
  exact hh.trans branch_endpoint_null

include Q hpublic hcat hlow hmenu in
theorem endpoint_off_noLow_null (i : Fin (N+1)) :
    (backgroundLaw Γ) (endpointEvent D i \ noLow D.E i)=0 := by
  let B := endpointEvent D i \ noLow D.E i
  have hB : MeasurableSet B := (measurableSet_endpointEvent D i).diff (measurableSet_noLow D.E i)
  let G := restoreBackground i ⁻¹' B
  have hkzero (kind : Fin N→ Fin 4) : (fiber Γ D kind) G=0 := by
    by_cases hn : ∀ r : Fin N,kind r≠0
    · have he : G=ᵐ[fiber Γ D kind] (∅ : Set (DeletedBackground N NativeLocalPolicy.Seed)) := by
        filter_upwards [fiber_shape Γ D kind] with z hz
        have hnl : restoreBackground i z∈noLow D.E i := by
          intro r
          simpa only [rivalKinds,restoreBackground_rival,hz r] using hn r
        apply propext
        change (restoreBackground i z∈endpointEvent D i ∧ restoreBackground i z∉noLow D.E i) ↔ False
        simp only [hnl,not_true_eq_false,and_false]
      rw [measure_congr he,measure_empty]
    · obtain ⟨r,hr⟩ := not_forall.mp hn
      have hr0 : kind r=0 := not_not.mp hr
      haveI : Nonempty {r : Fin N // kind r=0} := ⟨⟨r,hr0⟩⟩
      have hc : 0< Fintype.card {r : Fin N // kind r=0} := Fintype.card_pos_iff.mpr inferInstance
      obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
      let e : Fin (n+1)≃{r : Fin N // kind r=0} := (Fintype.equivFinOfCardEq hn).symm
      apply le_antisymm _ bot_le
      exact (measure_mono (fun z hz => hz.1)).trans_eq
        (positive_low_endpoint_null Γ D Q hpublic hcat hlow hmenu i kind n e)
  let tag : DeletedBackground N NativeLocalPolicy.Seed→(Fin N→ Fin 4) :=
    fun z r => D.E.coarseTag (z.1 r)
  have ht : Measurable tag := measurable_pi_lambda _ fun r =>
    D.E.measurable_coarseTag.comp ((measurable_pi_apply r).comp measurable_fst)
  have hp (kind : Fin N→ Fin 4) : tag ⁻¹' {kind}=categoryFiber D.E.coarseTag kind×ˢuniv := by
    ext z
    simp only [Set.mem_preimage,Set.mem_singleton_iff,tag,categoryFiber,Set.mem_prod,
      Set.mem_univ_pi,Set.mem_univ,and_true]
    exact ⟨fun h r => congrFun h r,fun h => funext h⟩
  have hgzero : (deletedBackgroundLaw Γ) G=0 := by
    rw [finite_disintegration (deletedBackgroundLaw Γ) tag ht,measure_sum_apply]
    apply Finset.sum_eq_zero
    intro kind _
    rw [Measure.smul_apply,smul_eq_mul,hp]
    change (deletedBackgroundLaw Γ) _*(fiber Γ D kind) G=0
    rw [hkzero,mul_zero]
  have hinv (ω : Background (N+1) 2 NativeLocalPolicy.Seed) :
      restoreBackground i (deleteBackground i ω)∈B ↔ ω∈B := by
    have hn : rivalKinds D.E i (restoreBackground i (deleteBackground i ω))=rivalKinds D.E i ω := by
      funext r
      simp only [rivalKinds,restoreBackground_rival,deleteBackground,NativeFlag.deletedUsers]
    simp only [B,Set.mem_sdiff,endpointEvent,Set.mem_setOf_eq,present_restore_delete,noLow,hn]
  have he := native_event_deleted Γ i B hB hinv
  change (backgroundLaw Γ).real B=(deletedBackgroundLaw Γ).real G at he
  simp only [measureReal_def,hgzero,ENNReal.toReal_zero] at he
  exact ((ENNReal.toReal_eq_zero_iff _).mp he).resolve_right (measure_ne_top _ _)

include Q hpublic hcat hlow hmenu in
theorem endpoint_probability_le_noLow (i : Fin (N+1)) :
    (backgroundLaw Γ).real (endpointEvent D i)≤(backgroundLaw Γ).real (noLow D.E i) := by
  have hz := endpoint_off_noLow_null Γ D Q hpublic hcat hlow hmenu i
  have hs : endpointEvent D i⊆noLow D.E i∪(endpointEvent D i\noLow D.E i) := by
    intro ω hω
    by_cases hn : ω∈noLow D.E i
    · exact Or.inl hn
    · exact Or.inr ⟨hω,hn⟩
  have h := (measureReal_mono (μ:=backgroundLaw Γ) hs).trans (measureReal_union_le _ _)
  simpa only [measureReal_def,hz,ENNReal.toReal_zero,add_zero] using h

end Fiber
end FCAppendix.Affine.Tail04.PartialNativeSeed
