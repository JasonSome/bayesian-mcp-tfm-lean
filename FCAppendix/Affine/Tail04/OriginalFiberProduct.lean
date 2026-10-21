import FCAppendix.Affine.Tail04.ThreeBlockProduct
import FCAppendix.Affine.Tail04.NoisyNativeCategories
import FCAppendix.Affine.Tail04.OriginalLowConditional

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalFiberProduct
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid ThreeBlockProduct Existence.Distributional OriginalValues OriginalPopulation

section Indices
variable {I : Type*} (k : I → Fin 4)

abbrev Nonlow := {i : I // k i≠0}
abbrev Common := {i : Nonlow k // k i.val=1}
abbrev Private := {i : Nonlow k // k i.val≠1}
abbrev Zero := {i : Private k // k i.val.val=2}
abbrev One := {i : Private k // k i.val.val≠2}

lemma one_tag (i : One k) : k i.val.val.val=3 := by
  have h0 := i.val.val.property
  have h1 := i.val.property
  have h2 := i.property
  generalize hk : k i.val.val.val=z at *
  fin_cases z <;> simp_all

end Indices

section Product
variable {I X A B Z : Type*} [Fintype I] [MeasurableSpace X]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (tag : X → Fin 4) (htag : Measurable tag) (k : I → Fin 4)
  (hmass : ∀ i,μ (tag ⁻¹' {k i})≠0)
  (a h0 h1 : ℕ) (ea : Fin a ≃ Common k)
  (e0 : Fin h0 ≃ Zero k) (e1 : Fin h1 ≃ One k)
  (fa : X → A) (fp : X → B) (hfa : Measurable fa) (hfp : Measurable fp)
  (ρa : Measure A) (ρp : Measure B) [IsProbabilityMeasure ρa] [IsProbabilityMeasure ρp]
  (ha : (cond μ (tag ⁻¹' {1})).map fa=ρa)
  (hp0 : (cond μ (tag ⁻¹' {2})).map fp=ρp)
  (hp1 : (cond μ (tag ⁻¹' {3})).map fp=ρp)
  (ω : Measure Z) [IsProbabilityMeasure ω]

def nonlowLaw : Measure (Nonlow k → X) :=
  Measure.pi (fun i : Nonlow k => cond μ (tag ⁻¹' {k i.val}))

include hmass in
lemma nonlowLaw_probability : IsProbabilityMeasure (nonlowLaw μ tag k) := by
  haveI (i : Nonlow k) : IsProbabilityMeasure (cond μ (tag ⁻¹' {k i.val})) :=
    cond_isProbabilityMeasure (hmass i.val)
  unfold nonlowLaw
  infer_instance

def numericalRows : (Nonlow k → X) → (Fin a → A) × (Fin h0 → B) × (Fin h1 → B) :=
  rows (fun i : Nonlow k => k i.val=1)
    (fun i : Private k => k i.val.val=2) a h0 h1 ea e0 e1 fa fp fp

include hfa hfp in
omit [Fintype I] in
lemma measurable_numericalRows :
    Measurable (numericalRows k a h0 h1 ea e0 e1 fa fp) :=
  measurable_rows _ _ _ _ _ _ _ _ _ _ _ hfa hfp hfp

def numericalLaw : Measure ((Fin a → A) × (Fin h0 → B) × (Fin h1 → B)) :=
  (Measure.pi (fun _ : Fin a => ρa)).prod
    ((Measure.pi (fun _ : Fin h0 => ρp)).prod (Measure.pi (fun _ : Fin h1 => ρp)))

instance numericalLaw_probability : IsProbabilityMeasure (numericalLaw a h0 h1 ρa ρp) := by
  unfold numericalLaw
  infer_instance

include hmass hfa hfp ha hp0 hp1 in
theorem nonlow_numerical_law :
    (nonlowLaw μ tag k).map (numericalRows k a h0 h1 ea e0 e1 fa fp)=
      numericalLaw a h0 h1 ρa ρp := by
  haveI (i : Nonlow k) : IsProbabilityMeasure (cond μ (tag ⁻¹' {k i.val})) :=
    cond_isProbabilityMeasure (hmass i.val)
  apply rows_law _ _ _ _ _ _ _ _ _ _ _ _ hfa hfp hfp ρa ρp ρp
  · intro j
    simpa only [(ea j).property] using ha
  · intro j
    simpa only [(e0 j).property] using hp0
  · intro j
    simpa only [one_tag k (e1 j)] using hp1

def fiberLaw : Measure ((I → X) × Z) :=
  (Measure.pi (fun i => cond μ (tag ⁻¹' {k i}))).prod ω

include hmass in
lemma fiberLaw_probability : IsProbabilityMeasure (fiberLaw μ tag k ω) := by
  haveI (i : I) : IsProbabilityMeasure (cond μ (tag ⁻¹' {k i})) :=
    cond_isProbabilityMeasure (hmass i)
  unfold fiberLaw
  infer_instance

def fiberRows (z : (I → X) × Z) :
    ((Fin a → A) × (Fin h0 → B) × (Fin h1 → B)) × Z :=
  (numericalRows k a h0 h1 ea e0 e1 fa fp (fun i => z.1 i.val),z.2)

include hfa hfp in
omit [Fintype I] in
lemma measurable_fiberRows : Measurable (fiberRows (Z:=Z) k a h0 h1 ea e0 e1 fa fp) :=
  ((measurable_numericalRows k a h0 h1 ea e0 e1 fa fp hfa hfp).comp
    (measurable_pi_lambda _ (fun i : Nonlow k =>
      (measurable_pi_apply i.val).comp measurable_fst))).prodMk measurable_snd

include hmass hfa hfp ha hp0 hp1 in
theorem fiberRows_law :
    (fiberLaw μ tag k ω).map (fiberRows k a h0 h1 ea e0 e1 fa fp)=
      (numericalLaw a h0 h1 ρa ρp).prod ω := by
  haveI := nonlowLaw_probability μ tag k hmass
  let ν : I → Measure X := fun i => cond μ (tag ⁻¹' {k i})
  haveI (i : I) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (hmass i)
  let r : (I → X) → Nonlow k → X := fun x i => x i.val
  have hr : Measurable r := measurable_pi_lambda _ (fun i : Nonlow k => measurable_pi_apply i.val)
  have hsplit := measurePreserving_piEquivPiSubtypeProd ν (fun i => k i=0)
  have hrLaw : (Measure.pi ν).map r=nonlowLaw μ tag k := by
    exact ((measurePreserving_snd (μ:=Measure.pi (fun i : {i : I // k i=0} => ν i))
      (ν:=nonlowLaw μ tag k)).comp hsplit).map_eq
  have hnr := nonlow_numerical_law μ tag k hmass a h0 h1 ea e0 e1 fa fp hfa hfp ρa ρp ha hp0 hp1
  let g := numericalRows k a h0 h1 ea e0 e1 fa fp
  have hg := measurable_numericalRows k a h0 h1 ea e0 e1 fa fp hfa hfp
  have hrg : (Measure.pi ν).map (g ∘ r)=numericalLaw a h0 h1 ρa ρp := by
    rw [←Measure.map_map hg hr,hrLaw,hnr]
  change ((Measure.pi ν).prod ω).map (Prod.map (g ∘ r) id)=_
  rw [←Measure.map_prod_map _ _ (hg.comp hr) measurable_id,hrg,Measure.map_id]

variable (lowBid : X → ℝ) (hlowBid : Measurable lowBid)
    (hlowAtoms : ∀ b,((cond μ (tag ⁻¹' {0})).map lowBid) {b}=0)
    (n : ℕ) (el : Fin (n+1) ≃ {i : I // k i=0})

def seedRows (z : (I → X) × Z) :
    unitInterval × (((Fin a → A) × (Fin h0 → B) × (Fin h1 → B)) × Z) :=
  (conditionalMinimumSeed ((cond μ (tag ⁻¹' {0})).map lowBid) n
    (fun j => lowBid (z.1 (el j))),fiberRows k a h0 h1 ea e0 e1 fa fp z)

include hfa hfp hlowBid in
omit [Fintype I] [IsProbabilityMeasure μ] in
lemma measurable_seedRows :
    Measurable (seedRows (Z:=Z) μ tag k a h0 h1 ea e0 e1 fa fp lowBid n el) :=
  ((measurable_conditionalMinimumSeed _ n).comp (measurable_pi_lambda _
    (fun j => hlowBid.comp ((measurable_pi_apply (el j).val).comp measurable_fst)))).prodMk
      (measurable_fiberRows k a h0 h1 ea e0 e1 fa fp hfa hfp)

include htag hmass hfa hfp ha hp0 hp1 hlowBid hlowAtoms in
theorem seedRows_law :
    (fiberLaw μ tag k ω).map
      (seedRows μ tag k a h0 h1 ea e0 e1 fa fp lowBid n el)=
      (volume : Measure unitInterval).prod ((numericalLaw a h0 h1 ρa ρp).prod ω) := by
  haveI := nonlowLaw_probability μ tag k hmass
  let r : ((I → X) × Z) → unitInterval × ((Nonlow k → X) × Z) := fun x =>
    (conditionalMinimumSeed ((cond μ (tag ⁻¹' {0})).map lowBid) n
      (fun j => lowBid (x.1 (el j))),((fun i => x.1 i.val),x.2))
  have hr : Measurable r :=
    ((measurable_conditionalMinimumSeed _ n).comp (measurable_pi_lambda _
      (fun j => hlowBid.comp ((measurable_pi_apply (el j).val).comp measurable_fst)))).prodMk
      ((measurable_pi_lambda _ (fun i : Nonlow k =>
        (measurable_pi_apply i.val).comp measurable_fst)).prodMk measurable_snd)
  have hseed := conditional_low_seed_joint μ tag htag k 0 hmass n el lowBid hlowBid hlowAtoms ω
  rw [conditional_categoryFiber μ tag htag k] at hseed
  have hseed' : (fiberLaw μ tag k ω).map r=
      (volume : Measure unitInterval).prod ((nonlowLaw μ tag k).prod ω) := by
    convert! hseed using 1
  let g := numericalRows k a h0 h1 ea e0 e1 fa fp
  have hg := measurable_numericalRows k a h0 h1 ea e0 e1 fa fp hfa hfp
  have hnr := nonlow_numerical_law μ tag k hmass a h0 h1 ea e0 e1 fa fp hfa hfp ρa ρp ha hp0 hp1
  calc
    _=((fiberLaw μ tag k ω).map r).map (Prod.map id (Prod.map g id)) := by
      rw [Measure.map_map (measurable_id.prodMap (hg.prodMap measurable_id)) hr]
      rfl
    _=_ := by
      rw [hseed',←Measure.map_prod_map _ _ measurable_id (hg.prodMap measurable_id),
        Measure.map_id,←Measure.map_prod_map _ _ hg measurable_id,Measure.map_id,hnr]

end Product
end FCAppendix.Affine.Tail04.OriginalFiberProduct
