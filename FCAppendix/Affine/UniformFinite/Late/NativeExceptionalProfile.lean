import FCAppendix.Affine.UniformFinite.Late.NativeExceptionalCounts
import FCAppendix.Affine.UniformFinite.Late.StrictAllocation
import FCAppendix.Affine.UniformFinite.NativeProfile

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.ExceptionalProfile
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05 SourceContinuity
open scoped BigOperators
variable {M : ℕ}

def rowContext (row : Source.CountRow M) (b : Fin M→ℝ) : Hybrid.ClassifiedContext M :=
  (fun a=> if a∈row.lower then some (b a) else none,row.upper0,row.upper1)

@[simp] theorem present_rowContext (row : Source.CountRow M) (b : Fin M→ℝ) :
    NativeContext.present (rowContext row b).1=row.lower := by
  ext a
  simp [rowContext,NativeContext.present]

theorem valid_rowContext (row : Source.CountRow M) (b : Fin M→ℝ) :
    NativeContext.Valid (rowContext row b) := by
  change (NativeContext.present (rowContext row b).1).card+row.upper0+row.upper1=M
  rw [present_rowContext]
  exact row.partition

@[simp] theorem decode_rowContext (row : Source.CountRow M) (b : Fin M→ℝ) :
    NativeContext.decode (rowContext row b)=row := by
  apply (NativeContext.countRow_eq_iff _ _).mpr
  have h0 : row.upper0≤ M-row.lower.card := by have h:=row.partition;omega
  have h1 : M-row.lower.card-row.upper0=row.upper1 := by have h:=row.partition;omega
  change NativeContext.present (rowContext row b).1=row.lower ∧
    min row.upper0 (M-(NativeContext.present (rowContext row b).1).card)=row.upper0 ∧
    M-(NativeContext.present (rowContext row b).1).card-
      min row.upper0 (M-(NativeContext.present (rowContext row b).1).card)=row.upper1
  simp only [present_rowContext,min_eq_left h0,h1,and_self]

theorem raw_rowContext (row : Source.CountRow M) (b : Fin M→ℝ)
    (hz : ∀a,a∉row.lower→ b a=0) : NativeExceptional.rawBids (rowContext row b)=b := by
  funext a
  by_cases ha : a∈row.lower
  · simp [NativeExceptional.rawBids,rowContext,ha,entryBid]
  · simp [NativeExceptional.rawBids,rowContext,ha,entryBid,hz a ha]

theorem nonnegative_rowContext (row : Source.CountRow M) (b : Fin M→ℝ)
    (hb : ∀a∈row.lower,0≤ b a) : NonnegativeList (rowContext row b).1 := by
  intro a
  by_cases ha : a∈row.lower
  · simpa only [rowContext,if_pos ha,entryBid] using hb a ha
  · simp only [rowContext,if_neg ha,entryBid,le_refl]

theorem common_rowContext [NeZero M] (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) : NativeContext.common i (NativeSeed.measure i G) (rowContext row b)=
      ExceptionalSeed.common i G row b := by
  have hlist : TaggedLocal.lowList (t i/2) (cap i) (rowContext row b).1=
      ExceptionalSeed.seedList i row b := by
    funext a
    by_cases ha : a∈row.lower <;> by_cases hb : b a≤ t i/2 <;> by_cases hU : b a≤ cap i <;>
      simp [rowContext,ExceptionalSeed.seedList,TaggedLocal.lowList,TaggedLocal.tag,ha,hb,hU]
  simp only [NativeContext.common,Hybrid.observedLowSeed,hlist,ExceptionalSeed.common]

def numericRow (i : Row) (a : Fin M) (z : Fin M→ NumericObservation i) : Source.CountRow M :=
  NativeProfile.numericRow i (NativeProfile.insert a (Noisy.zeroBid i) z)

def numericBids (i : Row) (a : Fin M) (own : ℝ) (z : Fin M→ NumericObservation i) : Fin M→ℝ :=
  Function.update (fun j=> numericBid i (z j)) a own

def numericContext (i : Row) (a : Fin M) (own : ℝ) (z : Fin M→ NumericObservation i) :
    Hybrid.ClassifiedContext M := rowContext (numericRow i a z) (numericBids i a own z)

theorem measurable_numericRow (i : Row) (a : Fin M) : Measurable (numericRow i a) :=
  (NativeProfile.measurable_numericRow i).comp (NativeProfile.measurable_insert a (Noisy.zeroBid i))

theorem measurable_numericBids (i : Row) (a : Fin M) (own : ℝ) :
    Measurable (numericBids i a own) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j=a
  · subst j
    simp only [numericBids,Function.update_self]
    exact measurable_const
  · simp only [numericBids,Function.update_of_ne hj]
    convert! (UniformFinite.measurable_numericBid i).comp
      (measurable_pi_apply j : Measurable (fun z : Fin M→NumericObservation i=>z j)) using 1

theorem measurable_numericContext (i : Row) (a : Fin M) (own : ℝ) :
    Measurable (numericContext i a own) := by
  have hr := measurable_numericRow i a
  have hb := measurable_numericBids i a own
  have hl : Measurable (fun z : Fin M→ NumericObservation i=>(numericContext i a own z).1) := by
    apply measurable_pi_lambda
    intro j
    have hmem : MeasurableSet {z : Fin M→ NumericObservation i | j∈(numericRow i a z).lower} := by
      have hh := measurableSet_eq_fun
        ((measurable_of_countable (fun r : Source.CountRow M=> decide (j∈r.lower))).comp hr)
        (measurable_const : Measurable (fun _ : Fin M→ NumericObservation i=>(true:Bool)))
      simp only [Function.comp_apply,decide_eq_true_eq] at hh
      convert! hh using 1
    exact Measurable.ite
      hmem
      (measurable_some.comp ((measurable_pi_apply j).comp hb)) measurable_const
  exact hl.prodMk (((measurable_of_countable Source.CountRow.upper0).comp hr).prodMk
    ((measurable_of_countable Source.CountRow.upper1).comp hr))

theorem focal_mem (i : Row) (a : Fin M) (z : Fin M→ NumericObservation i) :
    a∈(numericRow i a z).lower := by
  simp [numericRow,NativeProfile.numericRow,NativeProfile.insert,Source.countRowOfKind,numericKind]

theorem numericBids_focal (i : Row) (a : Fin M) (own : ℝ) (z : Fin M→ NumericObservation i) :
    numericBids i a own z a=own := Function.update_self _ _ _

theorem numericBids_outside (i : Row) (a : Fin M) (own : ℝ) (z : Fin M→ NumericObservation i) :
    ∀j,j∉(numericRow i a z).lower→ numericBids i a own z j=0 := by
  intro j hj
  have hja : j≠a := by
    intro he
    subst j
    exact hj (focal_mem i a z)
  rw [numericBids,Function.update_of_ne hja]
  cases hz : z j with
  | inl b => exact False.elim (hj (by simp [numericRow,NativeProfile.numericRow,NativeProfile.insert,
      Source.countRowOfKind,numericKind,hja,hz]))
  | inr k => rfl

theorem numericBids_good [NeZero M] (i : Row) (a : Fin M) (own : ℝ) (hown : 0≤ own)
    (z : Fin M→ NumericObservation i) :
    NativeExceptionalRow.Good i (numericRow i a z) a (numericBids i a own z) := by
  refine ⟨focal_mem i a z,?_,?_⟩
  · intro j hj
    by_cases hja : j=a
    · subst j
      simpa only [numericBids_focal] using hown
    · rw [numericBids,Function.update_of_ne hja]
      cases hz : z j with
      | inl b => exact b.property.1
      | inr k => exact le_rfl
  · intro j hj hja
    rw [numericBids,Function.update_of_ne hja]
    cases hz : z j with
    | inl b => exact b.property.2
    | inr k => exact (cap_pos i).le

theorem exceptions_numericContext [NeZero M] (i : Row) (a : Fin M) (own : ℝ)
    (hown : cap i< own) (z : Fin M→ NumericObservation i) :
    NativeExceptional.exceptions i (numericContext i a own z)={a} := by
  ext j
  rw [NativeExceptional.mem_exceptions]
  by_cases hja : j=a
  · subst j
    simp [numericContext,rowContext,focal_mem,numericBids_focal,NativeExceptional.rawBids,entryBid,hown]
  · have hg := numericBids_good i a own ((cap_pos i).trans hown).le z
    have hh : NativeExceptional.rawBids (numericContext i a own z) j≤ cap i := by
      rw [numericContext,raw_rowContext _ _ (numericBids_outside i a own z)]
      by_cases hj : j∈(numericRow i a z).lower
      · exact hg.2.2 j hj hja
      · rw [numericBids_outside i a own z j hj]
        exact (cap_pos i).le
    simp only [Finset.mem_singleton,hja,iff_false,not_and]
    intro _
    exact not_lt.mpr hh

variable [NeZero M]

def draw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (z : Fin M→ NumericObservation i) (s : unitInterval×unitInterval) : Allocation M :=
  NativeExceptionalRow.draw i G (numericRow i a z) a (numericBids i a own z)
    (ExceptionalSeed.common i G (numericRow i a z) (numericBids i a own z),s)

theorem context_pair_eq_draw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (hown : cap i< own) (z : Fin M→ NumericObservation i) (s : Fin 2→ unitInterval) :
    (NativeExceptional.contextPolicy i G (NativeSeed.measure i G)).selectionPair
      (numericContext i a own z) s=draw i G a own z (s 0,s 1) := by
  have hg := numericBids_good i a own ((cap_pos i).trans hown).le z
  have hv := valid_rowContext (numericRow i a z) (numericBids i a own z)
  have h0 := nonnegative_rowContext (numericRow i a z) (numericBids i a own z) hg.2.1
  have ha : a∈NativeExceptional.exceptions i (numericContext i a own z) := by
    rw [exceptions_numericContext i a own hown]
    simp
  have hc : (NativeExceptional.exceptions i (numericContext i a own z)).card=1 := by
    rw [exceptions_numericContext i a own hown,Finset.card_singleton]
  simp only [Hybrid.ContextPolicy.selectionPair,NativeExceptional.contextPolicy,
    NativeExceptional.unique_exception_select i G (NativeSeed.measure i G) _ a hv h0 ha hc,
    numericContext,decode_rowContext,raw_rowContext _ _ (numericBids_outside i a own z),
    common_rowContext,draw,NativeExceptionalRow.draw]

theorem measurable_draw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ) :
    Measurable (Function.uncurry (draw i G a own)) := by
  have hrow (row : Source.CountRow M) : Measurable
      (fun x : (Fin M→ NumericObservation i)×(unitInterval×unitInterval)=>
        NativeExceptionalRow.draw i G row a (numericBids i a own x.1)
          (ExceptionalSeed.common i G row (numericBids i a own x.1),x.2)) := by
    convert! (NativeExceptionalRow.draw_joint_measurable i G row a).comp
      (((measurable_numericBids i a own).comp measurable_fst).prodMk
        (((ExceptionalSeed.measurable_common i G row).comp
          ((measurable_numericBids i a own).comp measurable_fst)).prodMk measurable_snd)) using 1
  have hm : Measurable (fun p : Source.CountRow M×
      ((Fin M→NumericObservation i)×(unitInterval×unitInterval))=>
      NativeExceptionalRow.draw i G p.1 a (numericBids i a own p.2.1)
        (ExceptionalSeed.common i G p.1 (numericBids i a own p.2.1),p.2.2)) :=
    measurable_from_prod_countable_right hrow
  convert! hm.comp
    (((measurable_numericRow i a).comp measurable_fst).prodMk measurable_id) using 1

omit [NeZero M] in
theorem inserted_strict (i : Row) {R : ℝ} (hR : cap i< R) (a : Fin M)
    (u : JointAction 2) (hu : u.bid< R) (hr : u.routeCount=2) (v : ℝ)
    (d : UserProfile M 2) (hd : d∈Strict.strongProfiles M (cap i) R)
    (τ : Equiv.Perm (Fin 2)) : Function.update d a ((v,u),τ)∈Strict.profiles M R := by
  intro j
  by_cases hja : j=a
  · subst j
    simpa only [Function.update_self] using (Or.inl ⟨hu,hr⟩ :
      (u.bid<R ∧ u.routeCount=2) ∨ (R≤u.bid ∧ u.routeCount=1))
  · simpa only [Function.update_of_ne hja] using (Strict.strongProfiles_subset hR hd) j

omit [NeZero M] in

theorem actualContext_inserted (i : Row) {R : ℝ} (hR : cap i< R) (a : Fin M)
    (u : JointAction 2) (hu : u.bid< R) (hr : u.routeCount=2) (v : ℝ)
    (d : UserProfile M 2) (hd : d∈Strict.strongProfiles M (cap i) R)
    (τ : Equiv.Perm (Fin 2)) :
    Strict.actualContext R (Function.update d a ((v,u),τ))=
      numericContext i a u.bid (fun j=> OriginalPopulation.numericalDraw i (d j)) := by
  let d' := Function.update d a ((v,u),τ)
  have hd' := inserted_strict i hR a u hu hr v d hd τ
  apply Prod.ext
  · rw [show (Strict.actualContext R d').1=Strict.lowerPart R (observe (drawsRealization d') 0) from rfl,
      Strict.lowerPart_observe d' hd' 0]
    funext j
    by_cases hja : j=a
    · subst j
      simp [d',numericContext,rowContext,numericRow,NativeProfile.numericRow,NativeProfile.insert,
        Source.countRowOfKind,numericKind,numericBids,hu]
    · rcases hd j with ⟨hb,hroute⟩|⟨hb,hroute⟩
      · have hjR : (d j).1.2.bid< R := hb.trans_lt hR
        simp [d',Function.update_of_ne hja,numericContext,rowContext,numericRow,NativeProfile.numericRow,
          NativeProfile.insert,Source.countRowOfKind,numericBids,NativeProfile.numericalDraw_lower i (d j) hb,
          numericKind,numericBid,hjR,OriginalPopulation.clipBid,
          max_eq_right (d j).1.2.bid_nonneg,min_eq_right hb]
      · have hjU : cap i<(d j).1.2.bid := hR.trans_le hb
        by_cases hhere : (0:Fin 2)∈firstK (d j).2 1 <;>
          simp [d',Function.update_of_ne hja,numericContext,rowContext,numericRow,NativeProfile.numericRow,
            NativeProfile.insert,Source.countRowOfKind,numericBids,
            NativeProfile.numericalDraw_upper i (d j) hjU,numericKind,hhere,not_lt.mpr hb]
  · apply Prod.ext
    · change (∑j : Fin M,if Strict.kind R d' j=2 ∧
          (0:Fin 2)∈(drawsRealization d').recipients j then 1 else 0)=_
      simp only [numericContext,rowContext,numericRow,NativeProfile.numericRow,Source.countRowOfKind,
        Finset.card_eq_sum_ones,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hja : j=a
      · subst j
        simp [d',Strict.kind,hu,NativeProfile.insert,numericKind]
      · rcases hd j with ⟨hb,hroute⟩|⟨hb,hroute⟩
        · simp [d',Function.update_of_ne hja,Strict.kind,hb.trans_lt hR,NativeProfile.insert,
            NativeProfile.numericalDraw_lower i (d j) hb,numericKind]
        · by_cases hhere : (0:Fin 2)∈firstK (d j).2 1 <;>
            simp [d',Function.update_of_ne hja,Strict.kind,not_lt.mpr hb,drawsRealization,hroute,
              NativeProfile.insert,NativeProfile.numericalDraw_upper i (d j) (hR.trans_le hb),numericKind,hhere]
    · change (∑j : Fin M,if Strict.kind R d' j=2 ∧
          (1:Fin 2)∈(drawsRealization d').recipients j then 1 else 0)=_
      simp only [numericContext,rowContext,numericRow,NativeProfile.numericRow,Source.countRowOfKind,
        Finset.card_eq_sum_ones,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hja : j=a
      · subst j
        simp [d',Strict.kind,hu,NativeProfile.insert,numericKind]
      · rcases hd j with ⟨hb,hroute⟩|⟨hb,hroute⟩
        · simp [d',Function.update_of_ne hja,Strict.kind,hb.trans_lt hR,NativeProfile.insert,
            NativeProfile.numericalDraw_lower i (d j) hb,numericKind]
        · by_cases hhere : (0:Fin 2)∈firstK (d j).2 1 <;>
            simp [d',Function.update_of_ne hja,Strict.kind,not_lt.mpr hb,drawsRealization,hroute,
              NativeProfile.insert,NativeProfile.numericalDraw_upper i (d j) (hR.trans_le hb),numericKind,hhere,
              NativeProfile.singleton_one_iff_not_zero]

theorem broadcast_focalCount (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) {R : ℝ} (hR : cap i< R)
    (a : Fin M) (u : JointAction 2) (hU : cap i< u.bid) (hu : u.bid< R) (hr : u.routeCount=2)
    (d : UserProfile M 2) (hd : d∈Strict.strongProfiles M (cap i) R)
    (s : Fin 2→ unitInterval) (τ : Equiv.Perm (Fin 2)) :
    focalCount (Strict.constructedGame i G (NativeSeed.measure i G) Γ R) a u ((d,s),τ)=
      pairCount a (draw i G a u.bid (fun j=> OriginalPopulation.numericalDraw i (d j)) (s 0,s 1)) := by
  change focalCount (Strict.nativeGame
    (NativeExceptional.contextPolicy i G (NativeSeed.measure i G)) Γ R) a u ((d,s),τ)=_
  apply Fin.ext
  rw [Hybrid.focalCount_eq_inserted_count _ a 0]
  rw [Strict.native_inclusionCount_eq_focalCopy
    (NativeExceptional.contextPolicy i G (NativeSeed.measure i G)) Γ R
    (Function.update d a ((0,u),τ)) (inserted_strict i hR a u hu hr 0 d hd τ)
    s a (by simpa using hu),actualContext_inserted i hR a u hu hr 0 d hd τ,
    context_pair_eq_draw i G a u.bid hU,NativeProfile.pairCount_focalCopy]

def count (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (x : (Fin M→ NumericObservation i)×(unitInterval×unitInterval)) : Fin 3 :=
  pairCount a (draw i G a own x.1 x.2)

theorem measurable_count (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ) :
    Measurable (count i G a own) :=
  (measurable_of_countable (pairCount a)).comp (measurable_draw i G a own)

def indexedLaw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ) : CountLaw 2 :=
  FiniteLaw.ofMeasure (NativeProfile.law i M G) (count i G a own) (measurable_count i G a own)

theorem indexedLaw_expect (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (f : Fin 3→ℝ) : (indexedLaw i G a own).expect f=
      ∫z : Fin M→ NumericObservation i,∫s,f (count i G a own (z,s))
        ∂((volume : Measure unitInterval).prod volume)
        ∂Measure.pi (fun _ : Fin M=> numericObservationLaw i G) := by
  rw [indexedLaw,FiniteLaw.expect_ofMeasure]
  exact integral_prod _ (CountLaw.integrable_comp _ _ (measurable_count i G a own) f)

theorem native_outcome_indexed (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) (hseed : Γ.seedLaw=volume)
    {R : ℝ} (hR : cap i< R)
    (hfull : ∀ᵐd∂userProfileLaw Γ,d∈Strict.strongProfiles M (cap i) R)
    (hrow : (userProfileLaw Γ).map (fun d=> fun j=> OriginalPopulation.numericalDraw i (d j))=
      Measure.pi (fun _ : Fin M=> numericObservationLaw i G))
    (a : Fin M) (u : JointAction 2) (hU : cap i< u.bid) (hu : u.bid< R) (hr : u.routeCount=2) :
    (problem (Strict.constructedGame i G (NativeSeed.measure i G) Γ R) a).outcome u=
      indexedLaw i G a u.bid := by
  let C := Strict.constructedGame i G (NativeSeed.measure i G) Γ R
  let num : UserProfile M 2→(Fin M→ NumericObservation i) :=
    fun d j=> OriginalPopulation.numericalDraw i (d j)
  have hm : Measurable num := measurable_pi_lambda _
    (fun j=>(OriginalPopulation.measurable_numericalDraw i).comp (measurable_pi_apply j))
  have hnum : MeasurePreserving num (userProfileLaw Γ)
      (Measure.pi (fun _ : Fin M=> numericObservationLaw i G)) := ⟨hm,hrow⟩
  have hp : MeasurePreserving (fun s : Fin 2→ unitInterval=>(s 0,s 1))
      (Measure.pi (fun _ : Fin 2=>Γ.seedLaw)) ((volume : Measure unitInterval).prod volume) := by
    rw [hseed]
    exact measurePreserving_piFinTwo (fun _ : Fin 2=>(volume : Measure unitInterval))
  have hproj : MeasurePreserving
      (fun ω : Bayes.Sample M 2 unitInterval=>(num ω.1.1,(ω.1.2 0,ω.1.2 1)))
      (sampleLaw C) (NativeProfile.law i M G) :=
    (hnum.prod hp).comp (measurePreserving_fst (μ:=backgroundLaw C) (ν:=permLaw 2))
  have hprofile : ∀ᵐω∂sampleLaw C,ω.1.1∈Strict.strongProfiles M (cap i) R :=
    ((measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=Measure.pi (fun _ : Fin 2=>Γ.seedLaw))).comp
        (measurePreserving_fst (μ:=backgroundLaw C) (ν:=permLaw 2))).quasiMeasurePreserving.ae hfull
  apply FiniteLaw.ext_expect
  intro f
  rw [problem_outcome,CountLaw.expect_ofMeasure,indexedLaw,FiniteLaw.expect_ofMeasure]
  calc
    _=∫ω,f (count i G a u.bid (num ω.1.1,(ω.1.2 0,ω.1.2 1))) ∂sampleLaw C := by
      apply integral_congr_ae
      filter_upwards [hprofile] with ω hω
      rw [broadcast_focalCount i G Γ hR a u hU hu hr ω.1.1 hω ω.1.2 ω.2]
      rfl
    _=_ := by
      rw [← hproj.map_eq]
      exact (integral_map hproj.measurable.aemeasurable
        ((measurable_of_countable f).comp (measurable_count i G a u.bid)).aestronglyMeasurable).symm

end FCAppendix.Affine.UniformFinite.Late.ExceptionalProfile
