import FCAppendix.Affine.Tail04.PartialNativeSeed

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialNativeSeedReplacement
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open NativeLocalPolicy PartialNativeSeed NativeDeletedCounts

variable {N c : ℕ}

def eraseLow (kind : Fin N→ Fin 4) (row : Fin N→ UserDraw 2) : Fin N→ UserDraw 2 :=
  fun i => if kind i=0 then dummyDraw else row i

def rebuildNonlow (kind : Fin N→ Fin 4)
    (row : {i : Fin N // kind i≠0}→ UserDraw 2) : Fin N→ UserDraw 2 :=
  fun i => if h : kind i=0 then dummyDraw else row ⟨i,h⟩

lemma measurable_eraseLow (kind : Fin N→ Fin 4) : Measurable (eraseLow kind) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : kind i=0
  · simpa only [eraseLow,if_pos hi] using
      (measurable_const : Measurable (fun _ : Fin N→ UserDraw 2 => dummyDraw))
  · simpa only [eraseLow,if_neg hi] using
      (measurable_pi_apply i : Measurable (fun row : Fin N→ UserDraw 2 => row i))

lemma measurable_rebuildNonlow (kind : Fin N→ Fin 4) : Measurable (rebuildNonlow kind) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : kind i=0
  · simpa only [rebuildNonlow,dif_pos hi] using
      (measurable_const : Measurable (fun _ : {i : Fin N // kind i≠0}→ UserDraw 2 => dummyDraw))
  · simpa only [rebuildNonlow,dif_neg hi] using
      (measurable_pi_apply (⟨i,hi⟩ : {i : Fin N // kind i≠0}) : Measurable
        (fun row : {i : Fin N // kind i≠0}→ UserDraw 2 => row ⟨i,hi⟩))

lemma rebuild_projection (kind : Fin N→ Fin 4) (row : Fin N→ UserDraw 2) :
    rebuildNonlow kind (fun i => row i.val)=eraseLow kind row := by
  funext i
  by_cases hi : kind i=0 <;> simp [rebuildNonlow,eraseLow,hi]

section Fiber
variable (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed) (D : Data (N+1) c)
    (hcat : ∀ k : Fin 4,(userLaw Γ) (D.E.coarseTag ⁻¹' {k})≠0)
    (hlow : ∀ b,NativeFlag.nativeLowBidLaw Γ D.E {b}=0)
    (kind : Fin N→ Fin 4) (n : ℕ) (e : Fin (n+1)≃{r : Fin N // kind r=0})

abbrev Rest (kind : Fin N→ Fin 4) :=
  ({i : Fin N // kind i≠0}→ UserDraw 2)×(Fin 2→ NativeLocalPolicy.Seed)

def restLaw : Measure (Rest kind) :=
  (Measure.pi (fun i : {i : Fin N // kind i≠0} =>
    cond (userLaw Γ) (D.E.coarseTag ⁻¹' {kind i.val}))).prod
      (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))

include hcat in
lemma rest_probability : IsProbabilityMeasure (restLaw Γ D kind) := by
  haveI (i : {i : Fin N // kind i≠0}) :
      IsProbabilityMeasure (cond (userLaw Γ) (D.E.coarseTag ⁻¹' {kind i.val})) :=
    cond_isProbabilityMeasure (hcat (kind i.val))
  unfold restLaw;infer_instance

def minimumAndRest (z : DeletedBackground N NativeLocalPolicy.Seed) : unitInterval×Rest kind :=
  (fiberMinimum Γ D kind n e z,((fun r => z.1 r.val),z.2))

lemma measurable_minimumAndRest : Measurable (minimumAndRest Γ D kind n e) :=
  (measurable_fiberMinimum Γ D kind n e).prodMk
    ((measurable_pi_lambda _ fun r => (measurable_pi_apply r.val).comp measurable_fst).prodMk measurable_snd)

include hcat hlow in
theorem minimumAndRest_law :
    (fiber Γ D kind).map (minimumAndRest Γ D kind n e)=
      (volume : Measure unitInterval).prod (restLaw Γ D kind) := by
  have h := conditional_low_seed_joint (userLaw Γ) D.E.coarseTag D.E.measurable_coarseTag
    kind 0 (fun r => hcat (kind r)) n e NativeFlag.nativeBid NativeFlag.measurable_nativeBid
    hlow (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))
  rw [←cond_prod_left] at h
  exact h

include hcat hlow in
theorem erased_minimum_law :
    (fiber Γ D kind).map (fun z => (eraseLow kind z.1,fiberMinimum Γ D kind n e z))=
      ((fiber Γ D kind).prod (volume : Measure unitInterval)).map
        (fun z => (eraseLow kind z.1.1,z.2)) := by
  letI := fiber_isProbabilityMeasure Γ D hcat kind
  letI := rest_probability Γ D hcat kind
  let f : Rest kind→(Fin N→ UserDraw 2) := fun z => rebuildNonlow kind z.1
  have hf : Measurable f := (measurable_rebuildNonlow kind).comp measurable_fst
  letI : IsProbabilityMeasure ((restLaw Γ D kind).map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have hj : MeasurePreserving (minimumAndRest Γ D kind n e) (fiber Γ D kind)
      ((volume : Measure unitInterval).prod (restLaw Γ D kind)) :=
    ⟨measurable_minimumAndRest Γ D kind n e,minimumAndRest_law Γ D hcat hlow kind n e⟩
  have hfMP : MeasurePreserving f (restLaw Γ D kind) ((restLaw Γ D kind).map f) := ⟨hf,rfl⟩
  have hrest := (hfMP.comp measurePreserving_snd).comp hj
  have he : (fiber Γ D kind).map (fun z => eraseLow kind z.1)=(restLaw Γ D kind).map f := by
    convert! hrest.map_eq using 1
  have hswap := (Measure.measurePreserving_swap
    (μ:=(volume : Measure unitInterval)) (ν:=(restLaw Γ D kind).map f)).comp
      ((MeasurePreserving.id (volume : Measure unitInterval)).prod hfMP)
  have ha := (hswap.comp hj).map_eq
  have hae : (fiber Γ D kind).map
      (fun z => (eraseLow kind z.1,fiberMinimum Γ D kind n e z))=
      ((restLaw Γ D kind).map f).prod (volume : Measure unitInterval) := by
    convert! ha using 1
  rw [hae,←he]
  simpa only [Measure.map_id,Function.comp_def,Prod.map_apply] using!
    (Measure.map_prod_map (fiber Γ D kind) (volume : Measure unitInterval)
      ((measurable_eraseLow kind).comp measurable_fst) measurable_id)

include hcat hlow in
theorem event_replacement (B : Set ((Fin N→ UserDraw 2)×unitInterval)) (hB : MeasurableSet B)
    (hirr : ∀ row u,(eraseLow kind row,u)∈B ↔ (row,u)∈B) :
    (fiber Γ D kind).real {z | (z.1,fiberMinimum Γ D kind n e z)∈B}=
      ((fiber Γ D kind).prod (volume : Measure unitInterval)).real
        {z | (z.1.1,z.2)∈B} := by
  have h := congrArg (fun μ : Measure ((Fin N→ UserDraw 2)×unitInterval) => μ B)
    (erased_minimum_law Γ D hcat hlow kind n e)
  have hm0 : Measurable (fun z : DeletedBackground N NativeLocalPolicy.Seed =>
      (eraseLow kind z.1,fiberMinimum Γ D kind n e z)) :=
    ((measurable_eraseLow kind).comp measurable_fst).prodMk (measurable_fiberMinimum Γ D kind n e)
  have hm1 : Measurable (fun z : DeletedBackground N NativeLocalPolicy.Seed×unitInterval =>
      (eraseLow kind z.1.1,z.2)) :=
    ((measurable_eraseLow kind).comp measurable_fst.fst).prodMk measurable_snd
  rw [Measure.map_apply hm0 hB,Measure.map_apply hm1 hB] at h
  have h0 : {z : DeletedBackground N NativeLocalPolicy.Seed |
      (eraseLow kind z.1,fiberMinimum Γ D kind n e z)∈B}=
      {z | (z.1,fiberMinimum Γ D kind n e z)∈B} := by ext z;exact hirr _ _
  have h1 : {z : DeletedBackground N NativeLocalPolicy.Seed×unitInterval |
      (eraseLow kind z.1.1,z.2)∈B}={z | (z.1.1,z.2)∈B} := by ext z;exact hirr _ _
  change (fiber Γ D kind) {z | (eraseLow kind z.1,fiberMinimum Γ D kind n e z)∈B}=
    ((fiber Γ D kind).prod (volume : Measure unitInterval))
      {z | (eraseLow kind z.1.1,z.2)∈B} at h
  rw [h0,h1] at h
  exact congrArg ENNReal.toReal h

end Fiber
end FCAppendix.Affine.Tail04.PartialNativeSeedReplacement
