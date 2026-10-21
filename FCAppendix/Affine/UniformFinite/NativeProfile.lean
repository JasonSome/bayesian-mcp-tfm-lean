import FCAppendix.Affine.UniformFinite.NativeFixedCounts
import FCAppendix.Affine.UniformFinite.OriginalPopulationRows
import FCAppendix.Affine.Hybrid.NativeRealizedContext
import FCAppendix.Finite.ConditionalCountLaw

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05 SourceContinuity
open scoped BigOperators

namespace NativeProfile
variable {M : ℕ}

def rowContext (i : Row) (row : Source.CountRow M) (b : Fin M→ Bid i) :
    Hybrid.ClassifiedContext M :=
  (fun a=> if a∈row.lower then some (b a:ℝ) else none,row.upper0,row.upper1)

@[simp] lemma present_rowContext (i : Row) (row : Source.CountRow M) (b : Fin M→ Bid i) :
    NativeContext.present (rowContext i row b).1=row.lower := by
  ext a
  simp [rowContext,NativeContext.present]

lemma valid_rowContext (i : Row) (row : Source.CountRow M) (b : Fin M→ Bid i) :
    NativeContext.Valid (rowContext i row b) := by
  change (NativeContext.present (rowContext i row b).1).card+row.upper0+row.upper1=M
  rw [present_rowContext]
  exact row.partition

@[simp] lemma decode_rowContext (i : Row) (row : Source.CountRow M) (b : Fin M→ Bid i) :
    NativeContext.decode (rowContext i row b)=row := by
  apply (NativeContext.countRow_eq_iff _ _).mpr
  have h0 : row.upper0≤ M-row.lower.card := by have h:=row.partition;omega
  have h1 : M-row.lower.card-row.upper0=row.upper1 := by have h:=row.partition;omega
  simp only [NativeContext.decode,present_rowContext]
  simp only [rowContext,min_eq_left h0,h1,and_self]

lemma state_rowContext (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ Bid i) (hz : ∀a,a∉row.lower→ b a=Noisy.zeroBid i) :
    NativeContext.state i G (rowContext i row b)=(G,b) := by
  change ((G,NativeContext.cappedList i (rowContext i row b).1) :
    RestrictedLaw i×(Fin M→Bid i))=(G,b)
  apply congrArg (fun bs : Fin M→Bid i=> (G,bs))
  funext a
  apply Subtype.ext
  by_cases ha : a∈row.lower
  · simp [NativeContext.cappedList,rowContext,ha,entryBid,
      max_eq_right (b a).property.1,min_eq_right (b a).property.2]
  · simp [NativeContext.cappedList,rowContext,ha,entryBid,hz a ha,
      Noisy.zeroBid,(cap_pos i).le]

lemma common_rowContext (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ Bid i) :
    NativeContext.common i (NativeSeed.measure i G) (rowContext i row b)=
      NativeSeed.common i G row b := by
  have hlist : TaggedLocal.lowList (t i/2) (cap i) (rowContext i row b).1=
      NativeSeed.seedList i row b := by
    funext a
    by_cases ha : a∈row.lower <;> by_cases hb : (b a:ℝ)≤ t i/2 <;>
      simp [rowContext,NativeSeed.seedList,TaggedLocal.lowList,TaggedLocal.tag,ha,hb]
    split_ifs <;> decide
  simp only [NativeContext.common,Hybrid.observedLowSeed,hlist,NativeSeed.common]

def numericCapped (i : Row) : NumericObservation i→ Bid i :=
  Sum.elim id (fun _=> Noisy.zeroBid i)

lemma measurable_numericCapped (i : Row) : Measurable (numericCapped i) :=
  measurable_id.sumElim measurable_const

lemma measurable_numericKind (i : Row) : Measurable (numericKind i) :=
  measurable_const.sumElim (measurable_of_countable _)

def numericRow (i : Row) (z : Fin M→ NumericObservation i) : Source.CountRow M :=
  Source.countRowOfKind (fun a=> numericKind i (z a))

def numericBids (i : Row) (z : Fin M→ NumericObservation i) : Fin M→ Bid i :=
  fun a=> numericCapped i (z a)

def numericContext (i : Row) (z : Fin M→ NumericObservation i) : Hybrid.ClassifiedContext M :=
  rowContext i (numericRow i z) (numericBids i z)

lemma measurable_numericRow (i : Row) : Measurable (numericRow (M:=M) i) :=
  (measurable_of_countable Source.countRowOfKind).comp
    (measurable_pi_lambda _ (fun a=>(measurable_numericKind i).comp (measurable_pi_apply a)))

lemma measurable_numericBids (i : Row) : Measurable (numericBids (M:=M) i) :=
  measurable_pi_lambda _ (fun a=>(measurable_numericCapped i).comp (measurable_pi_apply a))

lemma measurable_numericContext (i : Row) : Measurable (numericContext (M:=M) i) := by
  have hrow:=measurable_numericRow (M:=M) i
  have hl : Measurable (fun z : Fin M→ NumericObservation i=>(numericContext i z).1) := by
    apply measurable_pi_lambda
    intro a
    have he : (fun z : Fin M→ NumericObservation i=>(numericContext i z).1 a)=
        fun z=> Sum.elim (fun b : Bid i=> some (b:ℝ)) (fun _ : Fin 2=> none) (z a) := by
      funext z
      cases hz : z a with
      | inl b=> simp [numericContext,rowContext,numericRow,Source.countRowOfKind,numericKind,hz,numericBids,numericCapped]
      | inr j=> fin_cases j <;> simp [numericContext,rowContext,numericRow,Source.countRowOfKind,numericKind,hz]
    rw [he]
    exact ((measurable_some.comp measurable_subtype_coe).sumElim measurable_const).comp
      (measurable_pi_apply a)
  exact hl.prodMk (((measurable_of_countable Source.CountRow.upper0).comp hrow).prodMk
    ((measurable_of_countable Source.CountRow.upper1).comp hrow))

lemma numericBids_outside (i : Row) (z : Fin M→ NumericObservation i) :
    ∀a,a∉(numericRow i z).lower→ numericBids i z a=Noisy.zeroBid i := by
  intro a ha
  cases hz : z a with
  | inl b=> exact False.elim (ha (by simp [numericRow,Source.countRowOfKind,numericKind,hz]))
  | inr j=> simp [numericBids,numericCapped,hz]

lemma singleton_one_iff_not_zero (τ : Equiv.Perm (Fin 2)) :
    ((1:Fin 2)∈firstK τ 1)↔(0:Fin 2)∉firstK τ 1 := by
  obtain ⟨j,hj⟩:=Finset.card_eq_one.mp (card_firstK τ 1 (by omega))
  fin_cases j <;> simp [hj]

lemma numericalDraw_lower (i : Row) (u : UserDraw 2) (hu : u.1.2.bid≤ cap i) :
    OriginalPopulation.numericalDraw i u=Sum.inl (OriginalPopulation.clipBid i u.1.2.bid) := by
  simp [OriginalPopulation.numericalDraw,OriginalPopulation.numericalOfFour,Hybrid.collapseAction,hu]

lemma numericalDraw_upper (i : Row) (u : UserDraw 2) (hu : cap i< u.1.2.bid) :
    OriginalPopulation.numericalDraw i u=
      if (0:Fin 2)∈firstK u.2 1 then Sum.inr 0 else Sum.inr 1 := by
  by_cases hr : (0:Fin 2)∈firstK u.2 1 <;>
    simp [OriginalPopulation.numericalDraw,OriginalPopulation.numericalOfFour,Hybrid.collapseAction,
      Hybrid.upperRow,not_le.mpr hu,hr]

theorem actualContext_numeric (i : Row) (d : UserProfile M 2)
    (hd : d∈Hybrid.classifiedProfiles M (cap i)) :
    Hybrid.actualContext (cap i) d=
      numericContext i (fun a=> OriginalPopulation.numericalDraw i (d a)) := by
  apply Prod.ext
  · rw [show (Hybrid.actualContext (cap i) d).1=
        Hybrid.broadcastPart (cap i) (observe (drawsRealization d) 0) from rfl,
      Hybrid.broadcastPart_observe d hd 0]
    funext a
    rcases hd a with ⟨hb,hroute⟩|⟨hb,hroute⟩
    · rw [if_pos hb]
      simp [numericContext,rowContext,numericRow,Source.countRowOfKind,
        numericalDraw_lower i (d a) hb,numericKind,numericBids,numericCapped,
        OriginalPopulation.clipBid,max_eq_right (d a).1.2.bid_nonneg,min_eq_right hb]
    · rw [if_neg (not_le.mpr hb)]
      by_cases hr : (0:Fin 2)∈firstK (d a).2 1 <;>
        simp [numericContext,rowContext,numericRow,Source.countRowOfKind,
          numericalDraw_upper i (d a) hb,numericKind,hr]
  · apply Prod.ext
    · change (∑a : Fin M,if Hybrid.classifiedKind (cap i) d a=2 ∧
          (0:Fin 2)∈(drawsRealization d).recipients a then 1 else 0)=_
      simp only [numericContext,rowContext,numericRow,Source.countRowOfKind,
        Finset.card_eq_sum_ones,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      rcases hd a with ⟨hb,hroute⟩|⟨hb,hroute⟩
      · simp [Hybrid.classifiedKind,hb,numericalDraw_lower i (d a) hb,numericKind]
      · by_cases hr : (0:Fin 2)∈firstK (d a).2 1 <;>
          simp [Hybrid.classifiedKind,not_le.mpr hb,drawsRealization,hroute,
            numericalDraw_upper i (d a) hb,numericKind,hr]
    · change (∑a : Fin M,if Hybrid.classifiedKind (cap i) d a=2 ∧
          (1:Fin 2)∈(drawsRealization d).recipients a then 1 else 0)=_
      simp only [numericContext,rowContext,numericRow,Source.countRowOfKind,
        Finset.card_eq_sum_ones,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      rcases hd a with ⟨hb,hroute⟩|⟨hb,hroute⟩
      · simp [Hybrid.classifiedKind,hb,numericalDraw_lower i (d a) hb,numericKind]
      · by_cases hr : (0:Fin 2)∈firstK (d a).2 1 <;>
          simp [Hybrid.classifiedKind,not_le.mpr hb,drawsRealization,hroute,
            numericalDraw_upper i (d a) hb,numericKind,hr,singleton_one_iff_not_zero]

variable [NeZero M]

def draw (i : Row) (G : RestrictedLaw i) (z : Fin M→ NumericObservation i)
    (s : unitInterval×unitInterval) : Allocation M :=
  NativeRow.draw i (numericRow i z) (G,numericBids i z)
    (NativeSeed.common i G (numericRow i z) (numericBids i z),s)

lemma context_pair_eq_draw (i : Row) (G : RestrictedLaw i) (z : Fin M→ NumericObservation i)
    (s : Fin 2→ unitInterval) :
    (NativeContext.contextPolicy i G (NativeSeed.measure i G)).selectionPair (numericContext i z) s=
      draw i G z (s 0,s 1) := by
  have hv:=valid_rowContext i (numericRow i z) (numericBids i z)
  have hs:=state_rowContext i G (numericRow i z) (numericBids i z) (numericBids_outside i z)
  simp only [Hybrid.ContextPolicy.selectionPair,NativeContext.contextPolicy,NativeContext.select,
    numericContext,if_pos hv,NativeContext.sourceSelect,decode_rowContext,hs,common_rowContext,
    draw,NativeRow.draw]

lemma measurable_draw (i : Row) (G : RestrictedLaw i) :
    Measurable (Function.uncurry (draw (M:=M) i G)) := by
  have h0 : Measurable (fun x : (Fin M→NumericObservation i)×(unitInterval×unitInterval)=>
      NativeContext.select i G (NativeSeed.measure i G) 0 (numericContext i x.1) x.2.1) := by
    convert! (NativeContext.measurable_select (M:=M) i G (NativeSeed.measure i G) 0).comp
      (((measurable_numericContext (M:=M) i).comp measurable_fst).prodMk measurable_snd.fst) using 1
  have h1 : Measurable (fun x : (Fin M→NumericObservation i)×(unitInterval×unitInterval)=>
      NativeContext.select i G (NativeSeed.measure i G) 1 (numericContext i x.1) x.2.2) := by
    convert! (NativeContext.measurable_select (M:=M) i G (NativeSeed.measure i G) 1).comp
      (((measurable_numericContext (M:=M) i).comp measurable_fst).prodMk measurable_snd.snd) using 1
  have he : Function.uncurry (draw (M:=M) i G)=fun x=>
      (NativeContext.contextPolicy i G (NativeSeed.measure i G)).selectionPair
        (numericContext i x.1) (Fin.cons x.2.1 (Fin.cons x.2.2 Fin.elim0)) := by
    funext x
    rw [context_pair_eq_draw]
    rfl
  rw [he]
  exact h0.prodMk h1

def insert {i : Row} (a : Fin M) (own : Bid i) (z : Fin M→ NumericObservation i) :
    Fin M→ NumericObservation i := Function.update z a (Sum.inl own)

omit [NeZero M] in
lemma measurable_insert {i : Row} (a : Fin M) (own : Bid i) : Measurable (insert a own) := by
  apply measurable_pi_lambda
  intro l
  by_cases hl : l=a
  · simp only [insert,hl,Function.update_self];exact measurable_const
  · simp only [insert,Function.update_of_ne hl];exact measurable_pi_apply l

omit [NeZero M] in
lemma measurable_insert_joint (i : Row) (a : Fin M) :
    Measurable (fun x : Bid i×(Fin M→ NumericObservation i)=> insert a x.1 x.2) := by
  apply measurable_pi_lambda
  intro l
  by_cases hl : l=a
  · simp only [insert,hl,Function.update_self]
    exact measurable_inl.comp measurable_fst
  · simp only [insert,Function.update_of_ne hl]
    exact (measurable_pi_apply l).comp measurable_snd

omit [NeZero M] in
lemma numerical_insert (i : Row) (a : Fin M) (own : Bid i) (v : ℝ)
    (d : UserProfile M 2) (τ : Equiv.Perm (Fin 2)) :
    (fun l=> OriginalPopulation.numericalDraw i ((Function.update d a ((v,Hybrid.lowBroadcast own),τ)) l))=
      insert a own (fun l=> OriginalPopulation.numericalDraw i (d l)) := by
  funext l
  by_cases hl : l=a
  · subst l
    simp only [Function.update_self,insert]
    rw [numericalDraw_lower i _ own.property.2]
    simp only [Hybrid.lowBroadcast,OriginalPopulation.clipBid_coe]
  · simp only [insert,Function.update_of_ne hl]

omit [NeZero M] in
lemma inserted_classified (i : Row) (a : Fin M) (own : Bid i) (v : ℝ)
    (d : UserProfile M 2) (hd : d∈Hybrid.classifiedProfiles M (cap i))
    (τ : Equiv.Perm (Fin 2)) :
    Function.update d a ((v,Hybrid.lowBroadcast own),τ)∈Hybrid.classifiedProfiles M (cap i) := by
  intro l
  by_cases hl : l=a
  · subst l
    simp only [Function.update_self]
    exact Or.inl ⟨own.property.2,rfl⟩
  · simpa only [Function.update_of_ne hl] using hd l

omit [NeZero M] in
lemma pairCount_focalCopy (a : Fin M) (P : Allocation M) : pairCount a P=LowBody.focalCopy P a := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [pairCount,LowBody.focalCopy,h0,h1]

theorem broadcast_focalCount (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval)
    (a : Fin M) (own : Bid i) (d : UserProfile M 2)
    (hd : d∈Hybrid.classifiedProfiles M (cap i))
    (s : Fin 2→ unitInterval) (τ : Equiv.Perm (Fin 2)) :
    focalCount (NativeContext.nativeGame i G (NativeSeed.measure i G) Γ) a
      (Hybrid.lowBroadcast own) ((d,s),τ)=
      pairCount a (draw i G (insert a own (fun l=> OriginalPopulation.numericalDraw i (d l))) (s 0,s 1)) := by
  unfold NativeContext.nativeGame
  apply Fin.ext
  rw [Hybrid.focalCount_eq_inserted_count _ a 0]
  rw [Hybrid.ContextPolicy.native_inclusionCount_eq_focalCopy
    (NativeContext.contextPolicy i G (NativeSeed.measure i G)) Γ (cap i)
    (Function.update d a ((0,Hybrid.lowBroadcast own),τ)) (inserted_classified i a own 0 d hd τ)
    s a (by simpa only [Function.update_self,Hybrid.lowBroadcast] using own.property.2),actualContext_numeric i _ (inserted_classified i a own 0 d hd τ),
    numerical_insert,context_pair_eq_draw,pairCount_focalCopy]

def law (i : Row) (M : ℕ) (G : RestrictedLaw i) :
    Measure ((Fin M→ NumericObservation i)×(unitInterval×unitInterval)) :=
  (Measure.pi (fun _ : Fin M=> numericObservationLaw i G)).prod
    ((volume : Measure unitInterval).prod volume)

instance law_probability (i : Row) (M : ℕ) (G : RestrictedLaw i) :
    IsProbabilityMeasure (law i M G) := by unfold law;infer_instance

def count (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i)
    (x : (Fin M→ NumericObservation i)×(unitInterval×unitInterval)) : Fin 3 :=
  pairCount a (draw i G (insert a own x.1) x.2)

lemma measurable_count (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i) :
    Measurable (count i G a own) := by
  convert! (measurable_of_countable (pairCount a)).comp ((measurable_draw i G).comp
    (((measurable_insert a own).comp measurable_fst).prodMk measurable_snd)) using 1

def indexedLaw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i) : CountLaw 2 :=
  FiniteLaw.ofMeasure (law i M G) (count i G a own) (measurable_count i G a own)

theorem indexedLaw_expect (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i)
    (f : Fin 3→ℝ) :
    (indexedLaw i G a own).expect f=
      ∫z : Fin M→ NumericObservation i,∫s,f (count i G a own (z,s))
        ∂((volume : Measure unitInterval).prod volume)
        ∂Measure.pi (fun _ : Fin M=> numericObservationLaw i G) := by
  rw [indexedLaw,FiniteLaw.expect_ofMeasure]
  exact integral_prod _ (CountLaw.integrable_comp _ _ (measurable_count i G a own) f)

lemma measurable_count_joint (i : Row) (G : RestrictedLaw i) (a : Fin M) :
    Measurable (fun x : Bid i×((Fin M→ NumericObservation i)×(unitInterval×unitInterval))=>
      count i G a x.1 x.2) := by
  convert! (measurable_of_countable (pairCount a)).comp ((measurable_draw i G).comp
    (((measurable_insert_joint i a).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      measurable_snd.snd)) using 1

lemma measurable_indexedLaw_mass (i : Row) (G : RestrictedLaw i) (a : Fin M) (k : Fin 3) :
    Measurable (fun own : Bid i=>(indexedLaw i G a own).mass k) := by
  simp_rw [← FiniteLaw.expect_singleton,indexedLaw,FiniteLaw.expect_ofMeasure]
  convert! ((measurable_of_countable (fun r : Fin 3=> if r=k then (1:ℝ) else 0)).comp
    (measurable_count_joint i G a)).stronglyMeasurable.integral_prod_right'.measurable using 1
  infer_instance

theorem native_outcome_indexed (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval)
    (hseed : Γ.seedLaw=volume)
    (hfull : ∀ᵐd∂userProfileLaw Γ,d∈Hybrid.classifiedProfiles M (cap i))
    (hrow : (userProfileLaw Γ).map (fun d=> fun l=> OriginalPopulation.numericalDraw i (d l))=
      Measure.pi (fun _ : Fin M=> numericObservationLaw i G))
    (a : Fin M) (own : Bid i) :
    (problem (NativeContext.nativeGame i G (NativeSeed.measure i G) Γ) a).outcome
      (Hybrid.lowBroadcast own)=indexedLaw i G a own := by
  let C:=NativeContext.nativeGame i G (NativeSeed.measure i G) Γ
  let num : UserProfile M 2→(Fin M→ NumericObservation i):=
    fun d l=> OriginalPopulation.numericalDraw i (d l)
  have hm : Measurable num := measurable_pi_lambda _
    (fun l=>(OriginalPopulation.measurable_numericalDraw i).comp (measurable_pi_apply l))
  have hnum : MeasurePreserving num (userProfileLaw Γ)
      (Measure.pi (fun _ : Fin M=> numericObservationLaw i G)) := ⟨hm,hrow⟩
  have hp : MeasurePreserving (fun s : Fin 2→ unitInterval=>(s 0,s 1))
      (Measure.pi (fun _ : Fin 2=>Γ.seedLaw)) ((volume : Measure unitInterval).prod volume) := by
    rw [hseed]
    exact measurePreserving_piFinTwo (fun _ : Fin 2=>(volume : Measure unitInterval))
  have hproj : MeasurePreserving
      (fun ω : Bayes.Sample M 2 unitInterval=>(num ω.1.1,(ω.1.2 0,ω.1.2 1)))
      (sampleLaw C) (law i M G) :=
    (hnum.prod hp).comp
      (measurePreserving_fst (μ:=backgroundLaw C) (ν:=permLaw 2))
  have hprofile : ∀ᵐω∂sampleLaw C,ω.1.1∈Hybrid.classifiedProfiles M (cap i) :=
    ((measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=Measure.pi (fun _ : Fin 2=>Γ.seedLaw))).comp
        (measurePreserving_fst (μ:=backgroundLaw C) (ν:=permLaw 2))).quasiMeasurePreserving.ae hfull
  apply FiniteLaw.ext_expect
  intro f
  rw [problem_outcome,CountLaw.expect_ofMeasure,indexedLaw,FiniteLaw.expect_ofMeasure]
  calc
    _=∫ω,f (count i G a own (num ω.1.1,(ω.1.2 0,ω.1.2 1))) ∂sampleLaw C := by
      apply integral_congr_ae
      filter_upwards [hprofile] with ω hω
      rw [broadcast_focalCount i G Γ a own ω.1.1 hω ω.1.2 ω.2]
      rfl
    _=_ := by
      rw [← hproj.map_eq]
      exact (integral_map hproj.measurable.aemeasurable
        ((measurable_of_countable f).comp (measurable_count i G a own)).aestronglyMeasurable).symm

end NativeProfile

namespace OriginalPopulation
variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

omit [NeZero M] in
theorem seedLaw_eq_native (E : ExactRestrictedLaw i M) :
    seedLaw E=NativeSeed.measure i E.law := by
  rw [seedLaw,NativeSeed.measure_eq_real_cond]
  congr 1
  change (OriginalGain.realBidLaw i 0 E.pi : Measure ℝ)=_
  simp only [OriginalGain.realBidLaw,ProbabilityMeasure.toMeasure_map,
    ExactRestrictedLaw.law,restrictedLaw_bidLaw]

theorem game_numeric_profiles (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : cap i< R) :
    (userProfileLaw (game E H)).map
      (fun d=> fun a=> numericalDraw i (d a))=
      Measure.pi (fun _ : Fin M=> numericObservationLaw i E.law) := by
  rw [userProfileLaw,Measure.pi_map_pi (fun _=>(measurable_numericalDraw i).aemeasurable)]
  simp only [game_numeric_row_law E H hR]

theorem game_broadcast_outcome (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : cap i< R) (a : Fin M) (own : Bid i) :
    (problem (game E H) a).outcome (Hybrid.lowBroadcast own)=
      NativeProfile.indexedLaw i E.law a own := by
  have hfull:=game_profile_support E H hR
  have hrow:=game_numeric_profiles E H hR
  change (problem (NativeContext.nativeGame i E.law (seedLaw E) (primitiveGame E H)) a).outcome _=_
  rw [seedLaw_eq_native]
  exact NativeProfile.native_outcome_indexed i E.law (primitiveGame E H) rfl hfull hrow a own

def indexedTypeLaw (E : ExactRestrictedLaw i M) (a : Fin M) (v : Value i) : CountLaw 2 :=
  FiniteLaw.average (E.sigma v)
    (fun q=> NativeProfile.indexedLaw i E.law a (baseBid i (v,q)))
    (fun k=>(NativeProfile.measurable_indexedLaw_mass i E.law a k).comp
      ((continuous_baseBid i).comp (continuous_const.prodMk continuous_id)).measurable)

theorem game_typeOutcome (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : cap i< R) (a : Fin M) (v : Value i) :
    typeOutcome (game E H) a v=indexedTypeLaw E a v := by
  apply FiniteLaw.ext_expect
  intro f
  have hm : Measurable (fun q : unitInterval=>lowerAction i (v,q)) :=
    (measurable_lowerAction i).comp ((measurable_const (a:=v)).prodMk measurable_id)
  rw [typeOutcome_expect,game_lower_kernel,integral_map
    hm.aemeasurable
    (measurable_outcome_expect (game E H) a f).aestronglyMeasurable,
    indexedTypeLaw,FiniteLaw.expect_average]
  apply integral_congr_ae
  exact ae_of_all _ (fun q=> congrArg (fun C : CountLaw 2=>C.expect f)
    (game_broadcast_outcome E H hR a (baseBid i (v,q))))

theorem indexedTypeLaw_original_integral (E : ExactRestrictedLaw i M) (a : Fin M)
    (f : Fin 3→ℝ) :
    (∫v,(indexedTypeLaw E a v).expect f ∂lowerMeasure i)=
      ∫p,(NativeProfile.indexedLaw i E.law a (baseBid i p)).expect f
        ∂(E.pi.1 : Measure (Value i×unitInterval)) := by
  have hi:=FiniteLaw.integrable_expect (lowerMeasure i⊗ₘE.sigma)
    (fun p=> NativeProfile.indexedLaw i E.law a (baseBid i p))
    (fun k=>(NativeProfile.measurable_indexedLaw_mass i E.law a k).comp
      (continuous_baseBid i).measurable) f
  simp_rw [indexedTypeLaw,FiniteLaw.expect_average]
  rw [← Measure.integral_compProd hi,E.disintegration]
  rfl

end OriginalPopulation
end FCAppendix.Affine.UniformFinite
