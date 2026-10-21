import FCAppendix.Affine.Uniform07Finishing.Native.SourceNativeGame
import FCAppendix.Affine.Hybrid.ObservedSeed

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open StrictNative

variable {m : ℕ}

lemma cond_ae_of_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A : Set X} (hA:MeasurableSet A) {P : X→ Prop} (hP:∀ᵐx∂μ,P x) :
    ∀ᵐx∂cond μ A,P x := by
  rw [ae_iff] at hP ⊢
  rw [cond_apply hA]
  have hh:μ (A∩{x | ¬P x})=0:=measure_mono_null inter_subset_right hP
  rw [hh,mul_zero]

lemma cond_ae_mem {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A : Set X} (hA:MeasurableSet A) : ∀ᵐx∂cond μ A,x∈A := by
  rw [ae_iff,cond_apply hA]
  have hh:A∩{x | x∉A}=∅:=by ext x;simp
  rw [hh,measure_empty,mul_zero]

def sourceDrawTag (zs U : ℝ) (u : UserDraw 2) : Fin 3 :=
  if u.1.2.bid≤ zs then 0 else if u.1.2.bid≤ U then 1 else 2

lemma measurable_sourceDrawTag (zs U : ℝ) : Measurable (sourceDrawTag zs U) :=
  Measurable.ite (measurableSet_le measurable_draw_bid measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_draw_bid measurable_const) measurable_const measurable_const)

lemma sourceDrawTag_seed (zs U : ℝ) : sourceDrawTag zs U ⁻¹' {0}=sourceSeedCategory zs := by
  ext u
  by_cases h:u.1.2.bid≤ zs <;> by_cases hU:u.1.2.bid≤ U <;>
    simp [sourceDrawTag,sourceSeedCategory,h,hU]

lemma sourceDrawTag_boxes (zs U : ℝ) (d : UserProfile m 2) :
    TaggedLocal.BidBoxes (fun k=>sourceDrawTag zs U (d k)) (drawsRealization d) zs U := by
  intro k
  by_cases hl:(d k).1.2.bid≤ zs
  · simp [sourceDrawTag,hl,drawsRealization]
  · by_cases ha:(d k).1.2.bid≤ U
    · simp [sourceDrawTag,hl,ha,drawsRealization,lt_of_not_ge hl]
    · simp [sourceDrawTag,hl,ha,drawsRealization,lt_of_not_ge ha]

lemma sourceDrawTag_routes {zs U : ℝ} (hzU:zs≤ U) (d : UserProfile m 2)
    (hshape:∀k,((d k).1.2.bid≤ U ∧ (d k).1.2.routeCount=2) ∨
      (U<(d k).1.2.bid ∧ (d k).1.2.routeCount=1)) :
    TaggedLocal.ClassRoutes (fun k=>sourceDrawTag zs U (d k)) (drawsRealization d) := by
  constructor
  · intro k hk
    rcases hshape k with hl|hh
    · change firstK (d k).2 (d k).1.2.routeCount=Finset.univ
      rw [hl.2,StrictNative.firstK_full_two]
    · have he:sourceDrawTag zs U (d k)=2:=by
        simp [sourceDrawTag,not_le.mpr hh.1,not_le.mpr (hzU.trans_lt hh.1)]
      exact (hk he).elim
  · intro k hk
    rcases hshape k with hl|hh
    · have he:sourceDrawTag zs U (d k)≠2:=by
        by_cases hs:(d k).1.2.bid≤ zs <;> simp [sourceDrawTag,hl.1,hs]
      exact (he hk).elim
    · change (firstK (d k).2 (d k).1.2.routeCount).card=1
      rw [hh.2,card_firstK _ _ (by omega)]

lemma low_seed_list_broadcastPart {m : ℕ} {zs U R : ℝ} (hzR:zs< R) (L : LocalList m) :
    TaggedLocal.lowList zs zs (StrictNative.broadcastPart R L)=TaggedLocal.lowList zs U L := by
  funext k
  cases he:L k with
  | none=>simp [TaggedLocal.lowList,TaggedLocal.tag,StrictNative.broadcastPart,StrictTags.lowList,StrictTags.tag,he]
  | some b=>
    by_cases hb:b≤ zs
    · have hbr:b< R:=hb.trans_lt hzR
      simp [TaggedLocal.lowList,TaggedLocal.tag,StrictNative.broadcastPart,StrictTags.lowList,StrictTags.tag,he,hb,hbr]
    · by_cases hbr:b< R <;> by_cases hbU:b≤ U <;>
        simp [TaggedLocal.lowList,TaggedLocal.tag,StrictNative.broadcastPart,StrictTags.lowList,StrictTags.tag,he,hb,hbr,hbU]

lemma sourceSeed_observed {m : ℕ} {zs U R : ℝ} (hzR:zs< R) (μ : Measure ℝ)
    (j : Fin 2) (L : LocalList m) :
    Weighted.sourceSeed μ zs (StrictNative.observedContext R j L)=
      Hybrid.observedLowSeed zs U μ L := by
  unfold Weighted.sourceSeed StrictNative.observedContext Hybrid.observedLowSeed
  rw [low_seed_list_broadcastPart hzR L]

variable {c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_conditional_bid_atomless (Γ : FiniteGame m 2 c Seed)
    [NullSingletonClass (submittedBidMeasure Γ)] {A : Set (UserDraw 2)} (hA:MeasurableSet A) :
    ∀b : ℝ,((cond (userLaw Γ) A).map (fun u : UserDraw 2=>u.1.2.bid)) {b}=0 := by
  intro b
  rw [Measure.map_apply measurable_draw_bid (measurableSet_singleton b)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  exact cond_ae_of_ae (userLaw Γ) hA (actual_draw_bid_ne Γ b)

theorem native_category_shape (Γ : FiniteGame m 2 c Seed)
    {zs U : ℝ} (hzU:zs≤ U)
    (hfull:∀ᵐd∂userProfileLaw Γ,∀k,
      ((d k).1.2.bid≤ U ∧ (d k).1.2.routeCount=2) ∨
      (U<(d k).1.2.bid ∧ (d k).1.2.routeCount=1)) (k : Fin m→ Fin 3) :
    ∀ᵐx∂cond (backgroundLaw Γ) ((Hybrid.categoryFiber (sourceDrawTag zs U) k)×ˢ univ),
      TaggedLocal.BidBoxes k (drawsRealization x.1) zs U ∧
        TaggedLocal.ClassRoutes k (drawsRealization x.1) := by
  have hA : MeasurableSet ((Hybrid.categoryFiber (sourceDrawTag zs U) k) ×ˢ
      (univ : Set (Fin 2 → Seed))) :=
    (Hybrid.measurableSet_categoryFiber _ (measurable_sourceDrawTag zs U) k).prod MeasurableSet.univ
  have hp:∀ᵐx∂backgroundLaw Γ,∀i,
      ((x.1 i).1.2.bid≤ U ∧ (x.1 i).1.2.routeCount=2) ∨
      (U<(x.1 i).1.2.bid ∧ (x.1 i).1.2.routeCount=1) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hfull
  filter_upwards [cond_ae_of_ae (backgroundLaw Γ) hA hp,
    cond_ae_mem (backgroundLaw Γ) hA] with x hx hcat
  have he:(fun i=>sourceDrawTag zs U (x.1 i))=k := by
    funext i
    exact hcat.1 i (mem_univ i)
  rw [←he]
  exact ⟨sourceDrawTag_boxes zs U x.1,sourceDrawTag_routes hzU x.1 hx⟩

theorem actual_observed_seed_joint (Γ : FiniteGame m 2 c Seed)
    [NullSingletonClass (submittedBidMeasure Γ)]
    {zs U R : ℝ} (hzU:zs≤ U) (hzR:zs< R)
    (hfull:∀ᵐd∂userProfileLaw Γ,∀i,
      ((d i).1.2.bid≤ U ∧ (d i).1.2.routeCount=2) ∨
      (U<(d i).1.2.bid ∧ (d i).1.2.routeCount=1))
    (k : Fin m→ Fin 3)
    (hmass:∀i,userLaw Γ (sourceDrawTag zs U ⁻¹' {k i})≠0)
    (n : ℕ) (e:Fin (n+1)≃{i : Fin m // k i=0}) (j : Fin 2) :
    (cond (backgroundLaw Γ) ((Hybrid.categoryFiber (sourceDrawTag zs U) k)×ˢ univ)).map
      (fun x=>(Weighted.sourceSeed
        ((cond (userLaw Γ) (sourceSeedCategory zs)).map (fun u : UserDraw 2=>u.1.2.bid))
        zs (StrictNative.observedContext R j (observe (drawsRealization x.1) j)),
        ((fun i : {i : Fin m // k i≠0}=>x.1 i),x.2)))=
      ((volume : Measure unitInterval).map some).prod
        ((Measure.pi (fun i : {i : Fin m // k i≠0}=>
          cond (userLaw Γ) (sourceDrawTag zs U ⁻¹' {k i}))).prod
          (Measure.pi (fun _ : Fin 2=>Γ.seedLaw))) := by
  have hnull:=actual_conditional_bid_atomless Γ
    ((measurable_sourceDrawTag zs U) (measurableSet_singleton 0))
  have hh:=Hybrid.observedLowSeed_native_joint Γ (sourceDrawTag zs U)
    (measurable_sourceDrawTag zs U) k hmass n e hnull hzU
    (native_category_shape Γ hzU hfull k) j
  simp only [sourceDrawTag_seed] at hh
  simp_rw [sourceSeed_observed (U:=U) hzR]
  exact hh

theorem actual_conditional_original_profile (Γ : FiniteGame m 2 c Seed)
    (zs U : ℝ) (k : Fin m→ Fin 3) :
    cond (userProfileLaw Γ) (Hybrid.categoryFiber (sourceDrawTag zs U) k)=
      Measure.pi (fun i : Fin m=>cond (userLaw Γ) (sourceDrawTag zs U ⁻¹' {k i})) :=
  Hybrid.native_conditional_categoryFiber Γ _ (measurable_sourceDrawTag zs U) k

lemma source_seed_cutoff_lt_bidCap (i : Uniform07.Row) :
    Uniform07.cutoff i/2< Early.bidCap i := by
  have ht:=Uniform07.cutoff_pos i
  cases i <;> norm_num [Early.bidCap,Early.capRatioQ,Uniform07.xQ,
    Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ] at * <;> linarith

section Source
variable [Nonempty (Fin m)]
  (i : Uniform07.Row) (hm:2≤ m) (hc:1≤ Uniform07.capacity m)
  {R Λ : ℝ} (hR:0< R) (hUR:Early.bidCap i< R) (hRt:R< Uniform07.cutoff i) (hΛ:0<Λ)
  (PL : ProbabilityMeasure (ℝ×JointAction 2))
  (hLvalue:(PL : Measure (ℝ×JointAction 2)).map Prod.fst=(sourceLowerValueLaw i : Measure ℝ))
  (hLroute:∀ᵐx∂(PL : Measure (ℝ×JointAction 2)),x.2.bid≤ Early.bidCap i ∧ x.2.routeCount=2)
  (hLatom:∀b : ℝ,(PL : Measure (ℝ×JointAction 2)) {x | x.2.bid=b}=0)
  (α : ClassifiedContext m→ unitInterval) (hα:Measurable α)

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_cap_profile :
    ∀ᵐd∂userProfileLaw (sourceNativeGame i hc R Λ hΛ PL α hα),∀k,
      ((d k).1.2.bid≤ Early.bidCap i ∧ (d k).1.2.routeCount=2) ∨
      (Early.bidCap i<(d k).1.2.bid ∧ (d k).1.2.routeCount=1) := by
  let Γ:=sourceNativeGame i hc R Λ hΛ PL α hα
  have hj:∀ᵐx∂Γ.F⊗ₘΓ.σ,
      (x.2.bid≤ Early.bidCap i ∧ x.2.routeCount=2) ∨
      (Early.bidCap i< x.2.bid ∧ x.2.routeCount=1) := by
    rw [sourceNativeGame_joint_law i hm hc hR hRt hΛ PL hLvalue hLroute α hα]
    exact source_population_action_shape i m hm hc hR hUR hRt PL hLvalue hLroute
  have hu:∀ᵐu∂userLaw Γ,
      (u.1.2.bid≤ Early.bidCap i ∧ u.1.2.routeCount=2) ∨
      (Early.bidCap i< u.1.2.bid ∧ u.1.2.routeCount=1) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hj
  exact ae_all_iff.mpr (fun k=>
    (measurePreserving_eval (fun _ : Fin m=>userLaw Γ) k).quasiMeasurePreserving.ae hu)

include hm hR hUR hRt hLvalue hLroute hLatom in
theorem sourceNativeGame_endogenous_seed_law
    (k : Fin m→ Fin 3)
    (hmass:∀u,userLaw (sourceNativeGame i hc R Λ hΛ PL α hα)
      (sourceDrawTag (Uniform07.cutoff i/2) (Early.bidCap i) ⁻¹' {k u})≠0)
    (n : ℕ) (e:Fin (n+1)≃{u : Fin m // k u=0}) (j : Fin 2) :
    let Γ:=sourceNativeGame i hc R Λ hΛ PL α hα
    (cond (backgroundLaw Γ)
      ((Hybrid.categoryFiber (sourceDrawTag (Uniform07.cutoff i/2) (Early.bidCap i)) k)×ˢ univ)).map
      (fun x=>(Weighted.sourceSeed (sourceSeedMeasure i m hc R PL) (Uniform07.cutoff i/2)
        (StrictNative.observedContext R j (observe (drawsRealization x.1) j)),
        ((fun u : {u : Fin m // k u≠0}=>x.1 u),x.2)))=
      ((volume : Measure unitInterval).map some).prod
        ((Measure.pi (fun u : {u : Fin m // k u≠0}=>
          cond (userLaw Γ) (sourceDrawTag (Uniform07.cutoff i/2) (Early.bidCap i) ⁻¹' {k u}))).prod
            (Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)))) := by
  let Γ:=sourceNativeGame i hc R Λ hΛ PL α hα
  letI : NullSingletonClass (submittedBidMeasure Γ) := by
    unfold submittedBidMeasure
    rw [sourceNativeGame_joint_law i hm hc hR hRt hΛ PL hLvalue hLroute α hα]
    exact source_population_bid_atomless i m hm hc hR hRt PL hLatom
  have hzU:Uniform07.cutoff i/2≤ Early.bidCap i:=(source_seed_cutoff_lt_bidCap i).le
  have hh:=actual_observed_seed_joint Γ hzU (hzU.trans_lt hUR)
    (sourceNativeGame_cap_profile i hm hc hR hUR hRt hΛ PL hLvalue hLroute α hα)
    k hmass n e j
  rw [sourceNativeGame_seed_measure i hm hc hR hRt hΛ PL hLvalue hLroute α hα]
  exact hh

end Source
end FCAppendix.Affine.Uniform07Finishing
