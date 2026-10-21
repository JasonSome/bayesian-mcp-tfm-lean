import FCAppendix.Affine.Tail04.NativeObservationPair
import FCAppendix.Affine.Tail04.PrivateIdentitySort
import FCAppendix.Affine.Tail04.PrivateConditionalRows
import FCAppendix.Game.PosteriorFeasible

noncomputable section
namespace FCAppendix.Affine.Tail04.PrivateFallbackKernel
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalCoordinates PrivateIdentitySort
open NativeObservationPair PrivateRowSorting

variable (E : Observable.Regions) {m : ℕ}

abbrev Entry := Ici E.H ⊕ Icc E.R E.Rp
abbrev Latent (m : ℕ) := Fin m → Entry E

lemma entry_private (x : Entry E) : numericalEntry x∈E.privateBids := by
  cases x with
  | inl x => exact Or.inr x.2
  | inr x => exact Or.inl x.2

lemma entry_nonnegative (x : Entry E) : 0≤ numericalEntry x :=
  E.d_nonneg.trans (E.private_above_low (entry_private E x)).le

lemma decode_numerical (x : Entry E) : LocalCoordinates.decode E (numericalEntry x)=x := by
  cases x with
  | inl x =>
    simp [numericalEntry,LocalCoordinates.decode,show E.H≤(x:ℝ) from x.2]
  | inr x =>
    have hx : ¬E.H≤(x:ℝ) := not_le.mpr (x.2.2.trans_lt E.Rp_lt_H)
    simp [numericalEntry,LocalCoordinates.decode,hx,clamp_eq x.2]

lemma entry_tag (x : Entry E) : E.localTag (some (numericalEntry x))=2 := by
  have hp := entry_private E x
  simp only [Observable.Regions.localTag,
    if_neg (not_le.mpr (E.private_above_low hp)),if_pos hp]

def action (b : ℝ) (k : ℕ) (hk : k≤2) : JointAction 2 :=
  ⟨max b 0,le_max_right _ _,k,hk⟩

lemma measurable_action (k : ℕ) (hk : k≤2) : Measurable (fun b => action b k hk) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun b : ℝ => (max b 0,k)) inferInstance≤_
  exact Measurable.comap_le ((measurable_id.max measurable_const).prodMk measurable_const)

def entry (j : Fin 2) (a : Option ℝ) (x : Entry E) : UserDraw 2 :=
  if a=none then
    ((0,action (numericalEntry x) 1 (by norm_num)),Equiv.swap 0 (Hybrid.otherProposer j))
  else if E.localTag a=2 then
    ((0,action (entryBid a) 1 (by norm_num)),Equiv.swap 0 j)
  else ((0,action (entryBid a) 2 (by norm_num)),Equiv.refl _)

lemma measurable_entry (j : Fin 2) : Measurable (Function.uncurry (entry E j)) := by
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · exact (measurable_const.prodMk ((measurable_action 1 (by norm_num)).comp
      (continuous_numericalEntry.measurable.comp measurable_snd))).prodMk measurable_const
  · apply Measurable.ite (measurableSet_eq_fun (E.measurable_localTag.comp measurable_fst) measurable_const)
    · exact (measurable_const.prodMk ((measurable_action 1 (by norm_num)).comp
        (measurable_entryBid.comp measurable_fst))).prodMk measurable_const
    · exact (measurable_const.prodMk ((measurable_action 2 (by norm_num)).comp
        (measurable_entryBid.comp measurable_fst))).prodMk measurable_const

def profile (j : Fin 2) (L : LocalList m) (x : Latent E m) : UserProfile m 2 :=
  fun i => entry E j (L i) (x i)

lemma measurable_profile (j : Fin 2) : Measurable (Function.uncurry (profile E (m:=m) j)) := by
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun z : LocalList m × Latent E m => entry E j (z.1 i) (z.2 i))
  have ha : Measurable (fun z : LocalList m × Latent E m => (z.1 i,z.2 i)) :=
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  exact (measurable_entry E j).comp ha

def otherList (L : LocalList m) (x : Latent E m) : LocalList m :=
  fun i => if L i=none then some (numericalEntry (x i))
    else if E.localTag (L i)=2 then none else L i

lemma measurable_otherList : Measurable (Function.uncurry (otherList E (m:=m))) := by
  apply measurable_pi_iff.mpr
  intro i
  apply Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst) measurable_const)
  · exact measurable_some.comp (continuous_numericalEntry.measurable.comp
      ((measurable_pi_apply i).comp measurable_snd))
  · exact Measurable.ite (measurableSet_eq_fun
      (E.measurable_localTag.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_const)
      measurable_const ((measurable_pi_apply i).comp measurable_fst)

lemma observe_profile (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L)
    (x : Latent E m) : observe (drawsRealization (profile E j L x)) j=L := by
  funext i
  cases he : L i with
  | none =>
    fin_cases j <;> simp [observe,drawsRealization,profile,entry,he,action,
      mem_firstK,Hybrid.otherProposer]
  | some b =>
    have hb : 0≤ b := by simpa only [he,entryBid] using hL i
    by_cases hp : E.localTag (some b)=2
    · simp [observe,drawsRealization,profile,entry,he,hp,action,
        mem_firstK,entryBid,max_eq_left hb]
    · simp [observe,drawsRealization,profile,entry,he,hp,action,
        mem_firstK,entryBid,max_eq_left hb,j.isLt]

lemma observe_other (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L)
    (x : Latent E m) :
    observe (drawsRealization (profile E j L x)) (Hybrid.otherProposer j)=otherList E L x := by
  funext i
  cases he : L i with
  | none =>
    simp [observe,drawsRealization,profile,entry,otherList,he,action,
      mem_firstK,max_eq_left (entry_nonnegative E (x i))]
  | some b =>
    have hb : 0≤ b := by simpa only [he,entryBid] using hL i
    by_cases hp : E.localTag (some b)=2
    · fin_cases j <;> simp [observe,drawsRealization,profile,entry,otherList,he,hp,
        action,mem_firstK,Hybrid.otherProposer]
    · simp [observe,drawsRealization,profile,entry,otherList,he,hp,action,
        mem_firstK,entryBid,max_eq_left hb,(Hybrid.otherProposer j).isLt]

lemma compatible_otherList (L : LocalList m) (x : Latent E m) :
    E.Compatible L (otherList E L x) := by
  intro i
  by_cases hn : L i=none
  · exact Or.inr (Or.inr ⟨hn,by simp only [otherList,if_pos hn];exact entry_tag E (x i)⟩)
  · by_cases hp : E.localTag (L i)=2
    · exact Or.inr (Or.inl ⟨hp,by simp [otherList,hn,hp]⟩)
    · have h3 : E.localTag (L i)≠3 := fun h => hn ((E.localTag_absent _).mp h)
      have hc : E.localTag (L i)=0 ∨ E.localTag (L i)=1 := by
        generalize E.localTag (L i)=k at *
        fin_cases k <;> simp_all
      exact Or.inl ⟨by simp [otherList,hn,hp],hc⟩

lemma otherList_nonnegative (L : LocalList m) (hL : NonnegativeList L)
    (x : Latent E m) : NonnegativeList (otherList E L x) := by
  intro i
  by_cases hn : L i=none
  · simpa only [otherList,if_pos hn,entryBid] using entry_nonnegative E (x i)
  · by_cases hp : E.localTag (L i)=2
    · simp [otherList,hn,hp,entryBid]
    · simpa [otherList,hn,hp] using hL i

def latentLaw (ρ : ProbabilityMeasure (Entry E)) : Measure (Latent E m) :=
  Measure.pi (fun _ : Fin m => (ρ : Measure (Entry E)))

instance (ρ : ProbabilityMeasure (Entry E)) : IsProbabilityMeasure (latentLaw E (m:=m) ρ) := by
  unfold latentLaw
  infer_instance

def kernel (ρ : ProbabilityMeasure (Entry E)) (j : Fin 2) :
    Kernel (LocalList m) (UserProfile m 2) where
  toFun L := (latentLaw E ρ).map (profile E j L)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun S hS => ?_)
    have hg : MeasurableSet {z : LocalList m×Latent E m | profile E j z.1 z.2∈S} :=
      (measurable_profile E j) hS
    have hm : Measurable (fun L => (Kernel.const (LocalList m) (latentLaw E ρ)) L
        {x | profile E j L x∈S}) := Kernel.measurable_kernel_prodMk_left hg
    have hp (L : LocalList m) : Measurable (profile E j L) :=
      (measurable_profile E j).comp measurable_prodMk_left
    have he : (fun L => ((latentLaw E ρ).map (profile E j L)) S) =
        (fun L => (latentLaw E ρ) {x | profile E j L x∈S}) := by
      funext L
      exact Measure.map_apply (hp L) hS
    rw [he]
    simpa only [Kernel.const_apply] using hm

instance (ρ : ProbabilityMeasure (Entry E)) (j : Fin 2) :
    IsMarkovKernel (kernel E (m:=m) ρ j) where
  isProbabilityMeasure _ := Measure.isProbabilityMeasure_map
    ((measurable_profile E j).comp measurable_prodMk_left).aemeasurable

lemma kernel_feasible (ρ : ProbabilityMeasure (Entry E)) (j : Fin 2)
    (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂kernel E ρ j L,observe (drawsRealization d) j=L := by
  apply (ae_map_iff ((measurable_profile E j).comp measurable_prodMk_left).aemeasurable
    (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
  exact ae_of_all _ (observe_profile E j L ((feasibleObservedList_iff_nonnegative j L).mp hL))

lemma kernel_opposite_law (ρ : ProbabilityMeasure (Entry E)) (j : Fin 2)
    (L : LocalList m) (hL : NonnegativeList L) :
    (kernel E ρ j L).map (fun d => observe (drawsRealization d) (Hybrid.otherProposer j))=
      (latentLaw E ρ).map (otherList E L) := by
  change ((latentLaw E ρ).map (profile E j L)).map _=_
  have hp : Measurable (profile E j L) :=
    (measurable_profile E j).comp measurable_prodMk_left
  rw [Measure.map_map (measurable_observe_draws _) hp]
  congr 1
  funext x
  exact observe_other E j L hL x

lemma other_privateRow (L : LocalList m) (x : Latent E m) :
    privateRow E (ids E 3 L) (otherList E L x)=
      sortRow E (ids E 3 L).card (fun k => x (baselineEmbedding (ids E 3 L) k)) := by
  rw [native_privateRow_eq_sorted]
  congr 1
  funext k
  have hk : E.localTag (L (baselineEmbedding (ids E 3 L) k))=3 :=
    (Finset.mem_filter.mp (baseline (ids E 3 L) k).2).2
  have hn := (E.localTag_absent _).mp hk
  simp only [otherList,if_pos hn,entryBid,decode_numerical]

lemma baseline_law (ρ : ProbabilityMeasure (Entry E)) (S : Finset (Fin m)) :
    (latentLaw E ρ).map (fun x => fun k => x (baselineEmbedding S k))=
      Measure.pi (fun _ : Fin S.card => (ρ : Measure (Entry E))) := by
  have h := PrivateConditionalRows.blockSplit_law
    (fun _ : Fin m => (ρ : Measure (Entry E))) (fun i : Fin m => i∈S) S.card
    (baseline S) id measurable_id (ρ : Measure (Entry E)) (fun _ => by simp only [Measure.map_id])
  have hf := congrArg (fun μ => μ.map Prod.fst) h
  rw [Measure.map_map measurable_fst
    (PrivateConditionalRows.measurable_blockSplit _ _ _ _ measurable_id)] at hf
  rw [Measure.map_fst_prod,measure_univ,one_smul] at hf
  exact hf

theorem kernel_privateRow_law (ρ : ProbabilityMeasure (Entry E)) (j : Fin 2)
    (L : LocalList m) (hL : NonnegativeList L) :
    (kernel E ρ j L).map (fun d => privateRow E (ids E 3 L)
      (observe (drawsRealization d) (Hybrid.otherProposer j)))=
      (sortedOriginalIid E (ids E 3 L).card ρ : Measure (Row (ids E 3 L).card E.R E.Rp E.H)) := by
  change (kernel E ρ j L).map
    (privateRow E (ids E 3 L) ∘ fun d => observe (drawsRealization d) (Hybrid.otherProposer j)) = _
  rw [←Measure.map_map (measurable_privateRow E _) (measurable_observe_draws _),
    kernel_opposite_law E ρ j L hL]
  have ho : Measurable (otherList E L) :=
    (measurable_otherList E).comp measurable_prodMk_left
  rw [Measure.map_map (measurable_privateRow E _) ho]
  have hf : (fun x : Latent E m => privateRow E (ids E 3 L) (otherList E L x))=
      (fun x => sortRow E (ids E 3 L).card (fun k => x (baselineEmbedding (ids E 3 L) k))) :=
    funext (other_privateRow E L)
  change (latentLaw E ρ).map (fun x => privateRow E (ids E 3 L) (otherList E L x)) = _
  rw [hf]
  change (latentLaw E ρ).map (sortRow E (ids E 3 L).card ∘
    fun x : Latent E m => fun k => x (baselineEmbedding (ids E 3 L) k)) = _
  have hb : Measurable (fun x : Latent E m => fun k : Fin (ids E 3 L).card =>
      x (baselineEmbedding (ids E 3 L) k)) :=
    measurable_pi_iff.mpr (fun k => measurable_pi_apply _)
  rw [←Measure.map_map (measurable_sortRow E _) hb,baseline_law E ρ]
  rfl

end FCAppendix.Affine.Tail04.PrivateFallbackKernel
