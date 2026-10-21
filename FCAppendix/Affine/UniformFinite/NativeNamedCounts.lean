import FCAppendix.Affine.UniformFinite.NativeRoutes

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05 SourceContinuity Existence.Distributional
open scoped BigOperators

namespace NativeRoutes
variable {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def namedTrace (Γ : FiniteGame M 2 c Seed) (a : Fin M) (b : ℝ)
    (ω : Background M 2 Seed) : Bool×Bool :=
  (if Accepts Γ a b 0 ω then true else false,
    if Accepts Γ a b 1 ω then true else false)

lemma measurable_namedTrace (Γ : FiniteGame M 2 c Seed) (a : Fin M) (b : ℝ) :
    Measurable (namedTrace Γ a b) :=
  (Measurable.ite (measurableSet_accepts Γ a b 0) measurable_const measurable_const).prodMk
    (Measurable.ite (measurableSet_accepts Γ a b 1) measurable_const measurable_const)

def traceOutcome (Γ : FiniteGame M 2 c Seed) (a : Fin M) (b : ℝ) : FiniteLaw (Bool×Bool) :=
  FiniteLaw.ofMeasure (backgroundLaw Γ) (namedTrace Γ a b) (measurable_namedTrace Γ a b)

end NativeRoutes

namespace NativeProfile
variable {M : ℕ} [NeZero M]

def trace (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i)
    (x : (Fin M→ NumericObservation i)×(unitInterval×unitInterval)) : Bool×Bool :=
  NativeRow.focalTrace a (draw i G (insert a own x.1) x.2)

lemma measurable_trace (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i) :
    Measurable (trace i G a own) := by
  convert! (measurable_of_countable (NativeRow.focalTrace a)).comp ((measurable_draw i G).comp
    (((measurable_insert a own).comp measurable_fst).prodMk measurable_snd)) using 1

lemma measurable_trace_joint (i : Row) (G : RestrictedLaw i) (a : Fin M) :
    Measurable (fun x : Bid i×((Fin M→ NumericObservation i)×(unitInterval×unitInterval))=>
      trace i G a x.1 x.2) := by
  convert! (measurable_of_countable (NativeRow.focalTrace a)).comp ((measurable_draw i G).comp
    (((measurable_insert_joint i a).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      measurable_snd.snd)) using 1

def indexedTraceLaw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i) :
    FiniteLaw (Bool×Bool) :=
  FiniteLaw.ofMeasure (law i M G) (trace i G a own) (measurable_trace i G a own)

lemma integrable_trace_test (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (own : Bid i) (f : Bool×Bool→ℝ) :
    Integrable (fun x=> f (trace i G a own x)) (law i M G) :=
  Integrable.of_bound ((measurable_of_countable f).comp (measurable_trace i G a own)).aestronglyMeasurable
    (∑r,‖f r‖) (ae_of_all _ (fun x=> Finset.single_le_sum
      (fun r _=> norm_nonneg (f r)) (Finset.mem_univ (trace i G a own x))))

theorem indexedTraceLaw_expect (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (own : Bid i) (f : Bool×Bool→ℝ) :
    (indexedTraceLaw i G a own).expect f=
      ∫z : Fin M→ NumericObservation i,∫s,f (trace i G a own (z,s))
        ∂((volume : Measure unitInterval).prod volume)
        ∂Measure.pi (fun _ : Fin M=> numericObservationLaw i G) := by
  rw [indexedTraceLaw,FiniteLaw.expect_ofMeasure]
  exact integral_prod _ (integrable_trace_test i G a own f)

lemma measurable_indexedTraceLaw_mass (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (r : Bool×Bool) : Measurable (fun own : Bid i=>(indexedTraceLaw i G a own).mass r) := by
  simp_rw [← FiniteLaw.expect_singleton,indexedTraceLaw,FiniteLaw.expect_ofMeasure]
  convert! ((measurable_of_countable (fun x : Bool×Bool=> if x=r then (1:ℝ) else 0)).comp
    (measurable_trace_joint i G a)).stronglyMeasurable.integral_prod_right'.measurable using 1
  infer_instance

def recipientCount (j : Fin 2) (r : Bool×Bool) : Fin 3 :=
  if (if j=0 then r.1 else r.2) then 1 else 0

def pairRecipientCount (a : Fin M) (j : Fin 2) (P : Allocation M) : Fin 3 :=
  recipientCount j (NativeRow.focalTrace a P)

omit [NeZero M] in
lemma pairRecipientCount_eq (a : Fin M) (j : Fin 2) (P : Allocation M) :
    pairRecipientCount a j P=if a∈(if j=0 then P.1 else P.2) then 1 else 0 := by
  fin_cases j <;> simp [pairRecipientCount,recipientCount,NativeRow.focalTrace]

def indexedRecipientLaw (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (own : Bid i) (j : Fin 2) : CountLaw 2 := (indexedTraceLaw i G a own).map (recipientCount j)

lemma indexedTraceLaw_count (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i) :
    (indexedTraceLaw i G a own).map NativeCounts.traceCount=indexedLaw i G a own := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map,indexedTraceLaw,FiniteLaw.expect_ofMeasure,indexedLaw,
    FiniteLaw.expect_ofMeasure]
  apply integral_congr_ae
  exact ae_of_all _ (fun x=> by simp only [trace,count,NativeCounts.pairCount_trace])

theorem native_accepts_iff_draw (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval)
    (a : Fin M) (own : Bid i) (j : Fin 2) (d : UserProfile M 2)
    (hd : d∈Hybrid.classifiedProfiles M (cap i)) (s : Fin 2→ unitInterval) :
    Accepts (NativeContext.nativeGame i G (NativeSeed.measure i G) Γ) a own j (d,s)↔
      a∈(if j=0 then
        (draw i G (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l))) (s 0,s 1)).1 else
        (draw i G (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l))) (s 0,s 1)).2) := by
  let C:=NativeContext.contextPolicy (M:=M) i G (NativeSeed.measure i G)
  let d':=Function.update d a ((0,Hybrid.lowBroadcast own),Equiv.refl (Fin 2))
  have hd':d'∈Hybrid.classifiedProfiles M (cap i):=inserted_classified i a own 0 d hd _
  have ho : observe (drawsRealization d') j=presentList (d,s) a own j := by
    have h0:=observe_insertDraw a (((0,Hybrid.lowBroadcast own),Equiv.refl (Fin 2)),(d,s)) j
    have h1:=observe_deviated_of_mem a (Hybrid.lowBroadcast own) ((d,s),Equiv.refl (Fin 2)) j
      (by change j∈firstK _ 2;rw [Hybrid.firstK_full_two];simp)
    exact h0.trans h1
  have hA:=C.native_allocation_mem_iff Γ (cap i) d' hd' s j a
    (by simpa only [d',Function.update_self,Hybrid.lowBroadcast] using own.property.2)
  rw [actualContext_numeric i d' hd',show
    (fun l=> OriginalPopulation.numericalDraw i (d' l))=
      insert a own (fun l=> OriginalPopulation.numericalDraw i (d l)) from numerical_insert i a own 0 d _]
    at hA
  have hpair:=context_pair_eq_draw i G (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l))) s
  have hselect : C.select j
      (numericContext i (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l)))) (s j)=
      if j=0 then
        (draw i G (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l))) (s 0,s 1)).1 else
        (draw i G (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l))) (s 0,s 1)).2 := by
    fin_cases j
    · change C.select 0 _ (s 0)=
        (draw i G (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l))) (s 0,s 1)).1
      simpa only [C,Hybrid.ContextPolicy.selectionPair] using congrArg Prod.fst hpair
    · change C.select 1 _ (s 1)=
        (draw i G (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l))) (s 0,s 1)).2
      simpa only [C,Hybrid.ContextPolicy.selectionPair] using congrArg Prod.snd hpair
  rw [hselect] at hA
  unfold allocation at hA
  rw [ho] at hA
  exact hA

theorem native_named_outcome_indexed (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval)
    (hseed : Γ.seedLaw=volume)
    (hfull : ∀ᵐd∂userProfileLaw Γ,d∈Hybrid.classifiedProfiles M (cap i))
    (hrow : (userProfileLaw Γ).map (fun d=> fun l=> OriginalPopulation.numericalDraw i (d l))=
      Measure.pi (fun _ : Fin M=> numericObservationLaw i G))
    (a : Fin M) (own : Bid i) (j : Fin 2) :
    NativeRoutes.namedOutcome (NativeContext.nativeGame i G (NativeSeed.measure i G) Γ) a own j=
      indexedRecipientLaw i G a own j := by
  let C:=NativeContext.nativeGame i G (NativeSeed.measure i G) Γ
  let num : UserProfile M 2→(Fin M→ NumericObservation i):=
    fun d l=> OriginalPopulation.numericalDraw i (d l)
  have hm : Measurable num:=measurable_pi_lambda _
    (fun l=>(OriginalPopulation.measurable_numericalDraw i).comp (measurable_pi_apply l))
  have hnum : MeasurePreserving num (userProfileLaw Γ)
      (Measure.pi (fun _ : Fin M=> numericObservationLaw i G)):=⟨hm,hrow⟩
  have hp : MeasurePreserving (fun s : Fin 2→ unitInterval=>(s 0,s 1))
      (Measure.pi (fun _ : Fin 2=>Γ.seedLaw)) ((volume : Measure unitInterval).prod volume) := by
    rw [hseed]
    exact measurePreserving_piFinTwo (fun _ : Fin 2=>(volume : Measure unitInterval))
  have hproj : MeasurePreserving
      (fun ω : Background M 2 unitInterval=>(num ω.1,(ω.2 0,ω.2 1)))
      (backgroundLaw C) (law i M G):=hnum.prod hp
  have hprofile : ∀ᵐω∂backgroundLaw C,ω.1∈Hybrid.classifiedProfiles M (cap i):=
    (measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=Measure.pi (fun _ : Fin 2=>Γ.seedLaw))).quasiMeasurePreserving.ae hfull
  apply FiniteLaw.ext_expect
  intro f
  rw [NativeRoutes.namedOutcome_expect,indexedRecipientLaw,FiniteLaw.expect_map,
    indexedTraceLaw,FiniteLaw.expect_ofMeasure]
  calc
    _=∫ω,f (recipientCount j (trace i G a own (num ω.1,(ω.2 0,ω.2 1))))∂backgroundLaw C := by
      apply integral_congr_ae
      filter_upwards [hprofile] with ω hω
      have h:=native_accepts_iff_draw i G Γ a own j ω.1 hω ω.2
      congr 1
      change (if Accepts C a own j ω then 1 else 0)=pairRecipientCount a j
        (draw i G (insert a own (num ω.1)) (ω.2 0,ω.2 1))
      rw [pairRecipientCount_eq]
      simp only [C,num,h]
    _=_ := by
      rw [← hproj.map_eq]
      exact (integral_map hproj.measurable.aemeasurable
        ((measurable_of_countable (f∘recipientCount j)).comp
          (measurable_trace i G a own)).aestronglyMeasurable).symm

theorem native_trace_outcome_indexed (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval)
    (hseed : Γ.seedLaw=volume)
    (hfull : ∀ᵐd∂userProfileLaw Γ,d∈Hybrid.classifiedProfiles M (cap i))
    (hrow : (userProfileLaw Γ).map (fun d=> fun l=> OriginalPopulation.numericalDraw i (d l))=
      Measure.pi (fun _ : Fin M=> numericObservationLaw i G))
    (a : Fin M) (own : Bid i) :
    NativeRoutes.traceOutcome (NativeContext.nativeGame i G (NativeSeed.measure i G) Γ) a own=
      indexedTraceLaw i G a own := by
  let C:=NativeContext.nativeGame i G (NativeSeed.measure i G) Γ
  let num : UserProfile M 2→(Fin M→ NumericObservation i):=
    fun d l=> OriginalPopulation.numericalDraw i (d l)
  have hm : Measurable num:=measurable_pi_lambda _
    (fun l=>(OriginalPopulation.measurable_numericalDraw i).comp (measurable_pi_apply l))
  have hnum : MeasurePreserving num (userProfileLaw Γ)
      (Measure.pi (fun _ : Fin M=> numericObservationLaw i G)):=⟨hm,hrow⟩
  have hp : MeasurePreserving (fun s : Fin 2→ unitInterval=>(s 0,s 1))
      (Measure.pi (fun _ : Fin 2=>Γ.seedLaw)) ((volume : Measure unitInterval).prod volume) := by
    rw [hseed]
    exact measurePreserving_piFinTwo (fun _ : Fin 2=>(volume : Measure unitInterval))
  have hproj : MeasurePreserving
      (fun ω : Background M 2 unitInterval=>(num ω.1,(ω.2 0,ω.2 1)))
      (backgroundLaw C) (law i M G):=hnum.prod hp
  have hprofile : ∀ᵐω∂backgroundLaw C,ω.1∈Hybrid.classifiedProfiles M (cap i):=
    (measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=Measure.pi (fun _ : Fin 2=>Γ.seedLaw))).quasiMeasurePreserving.ae hfull
  apply FiniteLaw.ext_expect
  intro f
  rw [NativeRoutes.traceOutcome,FiniteLaw.expect_ofMeasure,indexedTraceLaw,FiniteLaw.expect_ofMeasure]
  calc
    _=∫ω,f (trace i G a own (num ω.1,(ω.2 0,ω.2 1)))∂backgroundLaw C := by
      apply integral_congr_ae
      filter_upwards [hprofile] with ω hω
      have h0:=native_accepts_iff_draw i G Γ a own 0 ω.1 hω ω.2
      have h1:=native_accepts_iff_draw i G Γ a own 1 ω.1 hω ω.2
      simp only [if_neg (by decide : (1:Fin 2)≠0)] at h1
      congr 1
      simp [NativeRoutes.namedTrace,trace,NativeRow.focalTrace,num,h0,h1]
    _=_ := by
      rw [← hproj.map_eq]
      exact (integral_map hproj.measurable.aemeasurable
        ((measurable_of_countable f).comp (measurable_trace i G a own)).aestronglyMeasurable).symm

end NativeProfile

namespace NativeIndexed
variable {M : ℕ} [NeZero M]

theorem indexedTraceLaw_source (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : Bid i) (g : Bool×Bool→ℝ) :
    (NativeProfile.indexedTraceLaw i G a own).expect g=
      (categoryRowLaw i M).expect (fun kind=>
        ∫b : Fin M→ Bid i,
          (continuationLaw i G (fixedRow a kind) (bids i (G,fixedBids i a own kind b))).expect
            (fun P=> g (NativeRow.focalTrace a P))
          ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := by
  let F : (Fin M→ NumericObservation i)→ℝ:=fun z=>
    ∫s,g (NativeProfile.trace i G a own (z,s))∂((volume : Measure unitInterval).prod volume)
  have hm : Measurable F := by
    convert! ((measurable_of_countable g).comp
      (NativeProfile.measurable_trace i G a own)).stronglyMeasurable.integral_prod_right'.measurable using 1
    infer_instance
  have hB : ∀z,|F z|≤∑r,|g r| := by
    intro z
    have hb (privateSeed : unitInterval×unitInterval) :
        |g (NativeProfile.trace i G a own (z,privateSeed))|≤∑r,|g r| :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun r : Bool×Bool=>|g r|)
        (fun r _=>abs_nonneg (g r)) (Finset.mem_univ _)
    simpa only [F,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f:=fun privateSeed : unitInterval×unitInterval=>g (NativeProfile.trace i G a own (z,privateSeed)))
        (ae_of_all ((volume : Measure unitInterval).prod volume)
          (fun privateSeed=>by simpa only [Real.norm_eq_abs] using hb privateSeed))
  have hi : Integrable (fun p=> F (encodeCategoryRow i M p))
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) :=
    Integrable.of_bound (hm.comp (measurable_encodeCategoryRow i M)).aestronglyMeasurable
      (∑r,|g r|) (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hB _))
  rw [NativeProfile.indexedTraceLaw_expect]
  change (∫z,F z∂Measure.pi (fun _ : Fin M=> numericObservationLaw i G))=_
  rw [← encodeCategoryRow_law i G M,integral_map
    (measurable_encodeCategoryRow i M).aemeasurable hm.aestronglyMeasurable,
    integral_prod _ hi,LowBody.integral_probabilityMeasure]
  apply FiniteLaw.expect_congr
  intro kind
  exact fixed_trace_integral i G a own kind g

theorem indexedRecipientLaw_source (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : Bid i) (j : Fin 2) (f : Fin 3→ℝ) :
    (NativeProfile.indexedRecipientLaw i G a own j).expect f=
      (categoryRowLaw i M).expect (fun kind=>
        ∫b : Fin M→ Bid i,
          (continuationLaw i G (fixedRow a kind) (bids i (G,fixedBids i a own kind b))).expect
            (fun P=> f (NativeProfile.pairRecipientCount a j P))
          ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := by
  rw [NativeProfile.indexedRecipientLaw,FiniteLaw.expect_map,indexedTraceLaw_source]
  rfl

end NativeIndexed

namespace OriginalPopulation
variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

theorem game_named_outcome (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : cap i< R) (a : Fin M) (own : Bid i) (j : Fin 2) :
    NativeRoutes.namedOutcome (game E H) a own j=
      NativeProfile.indexedRecipientLaw i E.law a own j := by
  have hfull:=game_profile_support E H hR
  have hrow:=game_numeric_profiles E H hR
  change NativeRoutes.namedOutcome
    (NativeContext.nativeGame i E.law (seedLaw E) (primitiveGame E H)) a own j=_
  rw [seedLaw_eq_native]
  exact NativeProfile.native_named_outcome_indexed i E.law (primitiveGame E H) rfl hfull hrow a own j

theorem game_trace_outcome (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : cap i< R) (a : Fin M) (own : Bid i) :
    NativeRoutes.traceOutcome (game E H) a own=NativeProfile.indexedTraceLaw i E.law a own := by
  have hfull:=game_profile_support E H hR
  have hrow:=game_numeric_profiles E H hR
  change NativeRoutes.traceOutcome
    (NativeContext.nativeGame i E.law (seedLaw E) (primitiveGame E H)) a own=_
  rw [seedLaw_eq_native]
  exact NativeProfile.native_trace_outcome_indexed i E.law (primitiveGame E H) rfl hfull hrow a own

theorem game_singleton_outcome (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : cap i< R) (a : Fin M) (own : Bid i) (act : JointAction 2)
    (hk : act.routeCount=1) (hb : act.bid=(own:ℝ)) (f : Fin 3→ℝ) :
    ((problem (game E H) a).outcome act).expect f=
      ((NativeProfile.indexedRecipientLaw i E.law a own 0).expect f+
        (NativeProfile.indexedRecipientLaw i E.law a own 1).expect f)/2 := by
  rw [NativeRoutes.singleton_outcome_expect _ a act hk,hb,
    game_named_outcome E H hR a own 0,game_named_outcome E H hR a own 1]

def indexedTypeTraceLaw (E : ExactRestrictedLaw i M) (a : Fin M) (v : Value i) :
    FiniteLaw (Bool×Bool) :=
  FiniteLaw.average (E.sigma v)
    (fun q=> NativeProfile.indexedTraceLaw i E.law a (baseBid i (v,q)))
    (fun r=>(NativeProfile.measurable_indexedTraceLaw_mass i E.law a r).comp
      ((continuous_baseBid i).comp (continuous_const.prodMk continuous_id)).measurable)

theorem indexedTypeTraceLaw_actual (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : cap i< R) (a : Fin M) (v : Value i) (f : Bool×Bool→ℝ) :
    (indexedTypeTraceLaw E a v).expect f=
      ∫q,(NativeRoutes.traceOutcome (game E H) a (baseBid i (v,q))).expect f∂E.sigma v := by
  rw [indexedTypeTraceLaw,FiniteLaw.expect_average]
  simp_rw [game_trace_outcome E H hR]

theorem indexedTypeTraceLaw_count (E : ExactRestrictedLaw i M) (a : Fin M) (v : Value i) :
    (indexedTypeTraceLaw E a v).map NativeCounts.traceCount=indexedTypeLaw E a v := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map,indexedTypeTraceLaw,FiniteLaw.expect_average,indexedTypeLaw,
    FiniteLaw.expect_average]
  apply integral_congr_ae
  exact ae_of_all _ (fun q=> by
    change (NativeProfile.indexedTraceLaw i E.law a (baseBid i (v,q))).expect
      (fun r=>f (NativeCounts.traceCount r))=_
    rw [← FiniteLaw.expect_map,NativeProfile.indexedTraceLaw_count])

theorem indexedTypeTraceLaw_original_integral (E : ExactRestrictedLaw i M) (a : Fin M)
    (f : Bool×Bool→ℝ) :
    (∫v,(indexedTypeTraceLaw E a v).expect f∂lowerMeasure i)=
      ∫p,(NativeProfile.indexedTraceLaw i E.law a (baseBid i p)).expect f
        ∂(E.pi.1 : Measure (Value i×unitInterval)) := by
  have hi:=FiniteLaw.integrable_expect (lowerMeasure i⊗ₘE.sigma)
    (fun p=> NativeProfile.indexedTraceLaw i E.law a (baseBid i p))
    (fun r=>(NativeProfile.measurable_indexedTraceLaw_mass i E.law a r).comp
      (continuous_baseBid i).measurable) f
  simp_rw [indexedTypeTraceLaw,FiniteLaw.expect_average]
  have hdis : lowerMeasure i⊗ₘE.sigma=(E.pi.1 : Measure (Value i×unitInterval)) := E.disintegration
  rw [← Measure.integral_compProd hi,hdis]

end OriginalPopulation
end FCAppendix.Affine.UniformFinite
