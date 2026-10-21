import FCAppendix.Affine.UniformFinite.Late.NativeDeviation

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05 SourceContinuity Existence.Distributional
open scoped BigOperators

namespace ExceptionalProfile
variable {M : ℕ} [NeZero M]

def pairAt (j : Fin 2) (P : Allocation M) : Finset (Fin M) := if j=0 then P.1 else P.2

def namedPairCount (a : Fin M) (j : Fin 2) (P : Allocation M) : Fin 3 :=
  if a∈pairAt j P then 1 else 0

omit [NeZero M] in
theorem namedPairCount_success (a : Fin M) (j : Fin 2) (P : Allocation M) :
    successIndicator (namedPairCount a j P).val=routeIndicator j a P := by
  by_cases hj : j=0 <;> by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [namedPairCount,successIndicator,routeIndicator,WeightedSampling.indicator,pairAt,hj,h0,h1]

def namedIndexedLaw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (j : Fin 2) : CountLaw 2 :=
  FiniteLaw.ofMeasure (NativeProfile.law i M G)
    (fun x=> namedPairCount a j (draw i G a own x.1 x.2))
    ((measurable_of_countable (namedPairCount a j)).comp (measurable_draw i G a own))

theorem namedIndexedLaw_expect (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (j : Fin 2) (f : Fin 3→ℝ) :
    (namedIndexedLaw i G a own j).expect f=
      ∫z : Fin M→ NumericObservation i,∫s,f (namedPairCount a j (draw i G a own z s))
        ∂((volume : Measure unitInterval).prod volume)
        ∂Measure.pi (fun _ : Fin M=> numericObservationLaw i G) := by
  rw [namedIndexedLaw,FiniteLaw.expect_ofMeasure]
  exact integral_prod _ (CountLaw.integrable_comp _ _
    ((measurable_of_countable (namedPairCount a j)).comp (measurable_draw i G a own)) f)

omit [NeZero M] in

theorem presentList_broadcast (a : Fin M) (u : JointAction 2) (hr : u.routeCount=2)
    (d : UserProfile M 2) (s : Fin 2→ unitInterval) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    observe (drawsRealization (Function.update d a ((0,u),τ))) j=
      presentList (d,s) a u.bid j := by
  funext k
  by_cases hka : k=a
  · subst k
    simp [observe,drawsRealization,presentList,hr,Hybrid.firstK_full_two]
  · simp [observe,drawsRealization,presentList,hka]

theorem accepts_exceptional (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) {R : ℝ} (hR : cap i< R)
    (a : Fin M) (own : ℝ) (hU : cap i< own) (hoR : own< R)
    (d : UserProfile M 2) (hd : d∈Strict.strongProfiles M (cap i) R)
    (s : Fin 2→ unitInterval) (j : Fin 2) :
    Accepts (Strict.constructedGame i G (NativeSeed.measure i G) Γ R) a own j (d,s) ↔
      a∈pairAt j (draw i G a own (fun k=> OriginalPopulation.numericalDraw i (d k)) (s 0,s 1)) := by
  let u : JointAction 2:=⟨own,((cap_pos i).trans hU).le,2,le_rfl⟩
  let τ : Equiv.Perm (Fin 2):=Equiv.refl _
  let d' := Function.update d a ((0,u),τ)
  let C := NativeExceptional.contextPolicy (M:=M) i G (NativeSeed.measure i G)
  have hd' : d'∈Strict.profiles M R := inserted_strict i hR a u hoR rfl 0 d hd τ
  have hp : C.selectionPair (Strict.actualContext R d') s=
      draw i G a own (fun k=> OriginalPopulation.numericalDraw i (d k)) (s 0,s 1) := by
    rw [actualContext_inserted i hR a u hoR rfl 0 d hd τ,context_pair_eq_draw i G a own hU]
  have hselect : C.select j (Strict.actualContext R d') (s j)=
      pairAt j (draw i G a own (fun k=> OriginalPopulation.numericalDraw i (d k)) (s 0,s 1)) := by
    fin_cases j
    · change C.select 0 _ (s 0)=
        (draw i G a own (fun k=> OriginalPopulation.numericalDraw i (d k)) (s 0,s 1)).1
      simpa only [Hybrid.ContextPolicy.selectionPair] using congrArg Prod.fst hp
    · change C.select 1 _ (s 1)=
        (draw i G a own (fun k=> OriginalPopulation.numericalDraw i (d k)) (s 0,s 1)).2
      simpa only [Hybrid.ContextPolicy.selectionPair] using congrArg Prod.snd hp
  change (a∈((Strict.nativeGame C Γ R).policy j (presentList (d,s) a own j) (s j)).val)↔_
  rw [← presentList_broadcast a u rfl d s τ j]
  change (a∈allocation (drawsRealization d') (Strict.nativeGame C Γ R).policy s j)↔_
  rw [Strict.native_allocation_mem_iff C Γ R d' hd' s j a (by simpa [d',u] using hoR),hselect]

theorem native_namedOutcome_indexed (i : Row) (G : RestrictedLaw i)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) (hseed : Γ.seedLaw=volume)
    {R : ℝ} (hR : cap i< R)
    (hfull : ∀ᵐd∂userProfileLaw Γ,d∈Strict.strongProfiles M (cap i) R)
    (hrow : (userProfileLaw Γ).map (fun d=> fun k=> OriginalPopulation.numericalDraw i (d k))=
      Measure.pi (fun _ : Fin M=> numericObservationLaw i G))
    (a : Fin M) (own : ℝ) (hU : cap i< own) (hoR : own< R) (j : Fin 2) :
    NativeRoutes.namedOutcome (Strict.constructedGame i G (NativeSeed.measure i G) Γ R) a own j=
      namedIndexedLaw i G a own j := by
  let C := Strict.constructedGame i G (NativeSeed.measure i G) Γ R
  let num : UserProfile M 2→(Fin M→ NumericObservation i) :=
    fun d k=> OriginalPopulation.numericalDraw i (d k)
  have hm : Measurable num := measurable_pi_lambda _
    (fun k=>(OriginalPopulation.measurable_numericalDraw i).comp (measurable_pi_apply k))
  have hnum : MeasurePreserving num (userProfileLaw Γ)
      (Measure.pi (fun _ : Fin M=> numericObservationLaw i G)) := ⟨hm,hrow⟩
  have hp : MeasurePreserving (fun s : Fin 2→ unitInterval=>(s 0,s 1))
      (Measure.pi (fun _ : Fin 2=>Γ.seedLaw)) ((volume : Measure unitInterval).prod volume) := by
    rw [hseed]
    exact measurePreserving_piFinTwo (fun _ : Fin 2=>(volume : Measure unitInterval))
  have hproj : MeasurePreserving
      (fun ω : Background M 2 unitInterval=>(num ω.1,(ω.2 0,ω.2 1)))
      (backgroundLaw C) (NativeProfile.law i M G) := hnum.prod hp
  have hsupport : ∀ᵐω∂backgroundLaw C,ω.1∈Strict.strongProfiles M (cap i) R :=
    (measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=Measure.pi (fun _ : Fin 2=>Γ.seedLaw))).quasiMeasurePreserving.ae hfull
  apply FiniteLaw.ext_expect
  intro f
  rw [NativeRoutes.namedOutcome_expect,namedIndexedLaw,FiniteLaw.expect_ofMeasure]
  calc
    _=∫ω,f (namedPairCount a j (draw i G a own (num ω.1) (ω.2 0,ω.2 1)))
        ∂backgroundLaw C := by
      apply integral_congr_ae
      filter_upwards [hsupport] with ω hω
      simp only [NativeRoutes.namedCount,namedPairCount,
        accepts_exceptional i G Γ hR a own hU hoR ω.1 hω ω.2 j,num]
    _=_ := by
      rw [← hproj.map_eq]
      exact (integral_map hproj.measurable.aemeasurable
        ((measurable_of_countable (fun P : Allocation M=> f (namedPairCount a j P))).comp
          (measurable_draw i G a own)).aestronglyMeasurable).symm

end ExceptionalProfile

namespace ExceptionalIndexed
variable {M : ℕ} [NeZero M]

theorem namedIndexedLaw_source (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : ℝ) (hown : cap i< own) (j : Fin 2) (f : Fin 3→ℝ) :
    (ExceptionalProfile.namedIndexedLaw i G a own j).expect f=
      (categoryRowLaw i M).expect (fun kind=>∫b : Fin M→ Bid i,
        (Exceptional.continuationLaw i G (fixedRow a kind) (fixedBids i a own kind b) a).expect
          (fun P=> f (ExceptionalProfile.namedPairCount a j P))
        ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := by
  let F : (Fin M→ NumericObservation i)→ℝ := fun z=>
    ∫s,f (ExceptionalProfile.namedPairCount a j (ExceptionalProfile.draw i G a own z s))
      ∂((volume : Measure unitInterval).prod volume)
  have hm : Measurable F := by
    convert! ((measurable_of_countable
      (fun P : Allocation M=> f (ExceptionalProfile.namedPairCount a j P))).comp
      (ExceptionalProfile.measurable_draw i G a own)).stronglyMeasurable.integral_prod_right'.measurable using 1
    infer_instance
  have hB : ∀z,|F z|≤∑r,|f r| := by
    intro z
    have hb (privateSeed : unitInterval×unitInterval) :
        |f (ExceptionalProfile.namedPairCount a j (ExceptionalProfile.draw i G a own z privateSeed))|≤∑r,|f r| :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun r : Fin 3=>|f r|)
        (fun r _=>abs_nonneg (f r)) (Finset.mem_univ _)
    simpa only [F,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f:=fun privateSeed : unitInterval×unitInterval=>
          f (ExceptionalProfile.namedPairCount a j (ExceptionalProfile.draw i G a own z privateSeed)))
        (ae_of_all ((volume : Measure unitInterval).prod volume)
          (fun privateSeed=>by simpa only [Real.norm_eq_abs] using hb privateSeed))
  have hi : Integrable (fun p=> F (encodeCategoryRow i M p))
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) :=
    Integrable.of_bound (hm.comp (measurable_encodeCategoryRow i M)).aestronglyMeasurable
      (∑r,|f r|) (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hB _))
  rw [ExceptionalProfile.namedIndexedLaw_expect]
  change (∫z,F z ∂Measure.pi (fun _ : Fin M=> numericObservationLaw i G))=_
  rw [← encodeCategoryRow_law i G M,integral_map
    (measurable_encodeCategoryRow i M).aemeasurable hm.aestronglyMeasurable,
    integral_prod _ hi,LowBody.integral_probabilityMeasure]
  exact FiniteLaw.expect_congr _ (fun kind=> fixed_allocation_integral i G a own hown kind
    (fun P=> f (ExceptionalProfile.namedPairCount a j P)))

end ExceptionalIndexed

namespace StrictOriginal
variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

theorem exceptional_namedOutcome (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (own : ℝ) (hU : cap i< own) (hoR : own< R) (j : Fin 2) :
    NativeRoutes.namedOutcome (game E H) a own j=
      ExceptionalProfile.namedIndexedLaw i E.law a own j := by
  have hs:=game_profile_support E H
  have hp:=OriginalPopulation.game_numeric_profiles E H hR
  change NativeRoutes.namedOutcome (Strict.constructedGame i E.law (OriginalPopulation.seedLaw E)
    (OriginalPopulation.primitiveGame E H) R) a own j=_
  rw [OriginalPopulation.seedLaw_eq_native]
  exact ExceptionalProfile.native_namedOutcome_indexed i E.law
    (OriginalPopulation.primitiveGame E H) rfl hR hs hp a own hU hoR j

theorem exceptional_namedOutcome_source (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (own : ℝ) (hU : cap i< own) (hoR : own< R) (j : Fin 2) (f : Fin 3→ℝ) :
    (NativeRoutes.namedOutcome (game E H) a own j).expect f=
      (categoryRowLaw i M).expect (fun kind=>∫b : Fin M→ Bid i,
        (Exceptional.continuationLaw i E.law (ExceptionalIndexed.fixedRow a kind)
          (ExceptionalIndexed.fixedBids i a own kind b) a).expect
          (fun P=> f (ExceptionalProfile.namedPairCount a j P))
        ∂(rowLaw M E.law.bidLaw : Measure (Fin M→ Bid i))) := by
  rw [exceptional_namedOutcome E H hR a own hU hoR j,
    ExceptionalIndexed.namedIndexedLaw_source i E.law a own hU j f]

end StrictOriginal
end FCAppendix.Affine.UniformFinite.Late
