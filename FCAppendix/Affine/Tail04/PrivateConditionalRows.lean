import FCAppendix.Affine.Tail04.PrivateRowSorting
import FCAppendix.Affine.Tail04.LocalSamplerMean
import FCAppendix.Affine.Hybrid.NativeSeed
import Mathlib.Probability.Kernel.Disintegration.Unique

noncomputable section
namespace FCAppendix.Affine.Tail04.PrivateConditionalRows
open MeasureTheory ProbabilityTheory Set Classical
open FCAppendix.Affine.Hybrid

section Block
variable {ι X Y : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y]

def blockSplit (p : ι → Prop) (H : ℕ) (e : Fin H ≃ Subtype p)
    (f : X → Y) (x : ι → X) : (Fin H → Y) × ({i : ι // ¬p i} → X) :=
  (fun k => f (x (e k)),fun i => x i)

omit [Fintype ι] in
lemma measurable_blockSplit (p : ι → Prop) (H : ℕ) (e : Fin H ≃ Subtype p)
    (f : X → Y) (hf : Measurable f) : Measurable (blockSplit p H e f) :=
  (measurable_pi_lambda _ (fun k => hf.comp (measurable_pi_apply (e k).val))).prodMk
    (measurable_pi_lambda _ (fun i : {i : ι // ¬p i} => measurable_pi_apply (i:ι)))

theorem blockSplit_law (ν : ι → Measure X) [∀ i, IsProbabilityMeasure (ν i)]
    (p : ι → Prop) (H : ℕ) (e : Fin H ≃ Subtype p)
    (f : X → Y) (hf : Measurable f) (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (hrow : ∀ k, (ν (e k)).map f=ρ) :
    (Measure.pi ν).map (blockSplit p H e f)=
      (Measure.pi (fun _ : Fin H => ρ)).prod
        (Measure.pi (fun i : {i : ι // ¬p i} => ν i)) := by
  let g : (Subtype p → X) → Fin H → Y := fun x k => f (x (e k))
  have hg : Measurable g := measurable_pi_lambda _
    (fun k => hf.comp (measurable_pi_apply (e k)))
  let r : (Subtype p → X) → Fin H → X := fun x k => x (e k)
  have hr : Measurable r := measurable_pi_lambda _ (fun k => measurable_pi_apply (e k))
  have hreindex : (Measure.pi (fun i : Subtype p => ν i)).map r=
      Measure.pi (fun k : Fin H => ν (e k)) := by
    have h := (measurePreserving_piCongrLeft
      (fun k : Fin H => ν (e k)) e.symm).map_eq
    simp only [Equiv.apply_symm_apply] at h
    convert! h using 1
    congr 1
    funext x k
    simp [r,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']
  have hc : Measurable (fun x : Fin H → X => fun k => f (x k)) :=
    measurable_pi_lambda _ (fun k => hf.comp (measurable_pi_apply k))
  have hgLaw : (Measure.pi (fun i : Subtype p => ν i)).map g=
      Measure.pi (fun _ : Fin H => ρ) := by
    calc
      _=((Measure.pi (fun i : Subtype p => ν i)).map r).map
          (fun x : Fin H → X => fun k => f (x k)) := (Measure.map_map hc hr).symm
      _=_ := by rw [hreindex,Measure.pi_map_pi (fun _ => hf.aemeasurable)];simp only [hrow]
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p
  have hsplit := (measurePreserving_piEquivPiSubtypeProd ν p).map_eq
  calc
    _=((Measure.pi ν).map E).map (Prod.map g id) := by
      rw [Measure.map_map (hg.prodMap measurable_id) E.measurable]
      rfl
    _=((Measure.pi (fun i : Subtype p => ν i)).prod
        (Measure.pi (fun i : {i : ι // ¬p i} => ν i))).map (Prod.map g id) := by rw [hsplit]
    _=_ := by rw [←Measure.map_prod_map _ _ hg measurable_id,hgLaw,Measure.map_id]

variable {K : Type*} [MeasurableSpace K] [MeasurableSingletonClass K]

theorem conditional_blockSplit (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X → K) (htag : Measurable tag) (k : ι → K) (privateClass : K)
    (hmass : ∀ i, μ (tag ⁻¹' {k i})≠0)
    (H : ℕ) (e : Fin H ≃ {i : ι // k i=privateClass})
    (f : X → Y) (hf : Measurable f) (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (hρ : (cond μ (tag ⁻¹' {privateClass})).map f=ρ) :
    (cond (Measure.pi (fun _ : ι => μ)) (categoryFiber tag k)).map
      (blockSplit (fun i => k i=privateClass) H e f)=
      (Measure.pi (fun _ : Fin H => ρ)).prod
        (Measure.pi (fun i : {i : ι // k i≠privateClass} => cond μ (tag ⁻¹' {k i}))) := by
  let ν : ι → Measure X := fun i => cond μ (tag ⁻¹' {k i})
  letI (i : ι) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (hmass i)
  rw [conditional_categoryFiber μ tag htag k]
  apply blockSplit_law ν (fun i => k i=privateClass) H e f hf ρ
  intro i
  simpa only [ν,(e i).property] using hρ

end Block

section SortedPrivate
variable {ι X K O : Type*} [Fintype ι] [MeasurableSpace X]
  [MeasurableSpace K] [MeasurableSingletonClass K] [MeasurableSpace O]
variable (E : Observable.Regions)

theorem sorted_conditional_private_joint
    (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X → K) (htag : Measurable tag) (k : ι → K) (privateClass : K)
    (hmass : ∀ i, μ (tag ⁻¹' {k i})≠0)
    (H : ℕ) (e : Fin H ≃ {i : ι // k i=privateClass})
    (f : X → Ici E.H ⊕ Icc E.R E.Rp) (hf : Measurable f)
    (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp))
    (hρ : (cond μ (tag ⁻¹' {privateClass})).map f=(ρ : Measure _))
    (obs : ({i : ι // k i≠privateClass} → X) → O) (hobs : Measurable obs) :
    (cond (Measure.pi (fun _ : ι => μ)) (categoryFiber tag k)).map
      (fun x => (obs (fun i => x i),
        PrivateRowSorting.sortRow E H (fun a => f (x (e a)))))=
      ((Measure.pi (fun i : {i : ι // k i≠privateClass} =>
        cond μ (tag ⁻¹' {k i}))).map obs).prod
          (PrivateRowSorting.sortedOriginalIid E H ρ : Measure _) := by
  let ν : ι → Measure X := fun i => cond μ (tag ⁻¹' {k i})
  letI (i : ι) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (hmass i)
  let rest := Measure.pi (fun i : {i : ι // k i≠privateClass} => ν i)
  have hm := conditional_blockSplit μ tag htag k privateClass hmass H e f hf (ρ : Measure _) hρ
  have hg : Measurable (fun z : (Fin H → Ici E.H ⊕ Icc E.R E.Rp) ×
      ({i : ι // k i≠privateClass} → X) =>
      (obs z.2,PrivateRowSorting.sortRow E H z.1)) :=
    (hobs.comp measurable_snd).prodMk ((PrivateRowSorting.measurable_sortRow E H).comp measurable_fst)
  calc
    _=((cond (Measure.pi (fun _ : ι => μ)) (categoryFiber tag k)).map
        (blockSplit (fun i => k i=privateClass) H e f)).map
        (fun z => (obs z.2,PrivateRowSorting.sortRow E H z.1)) :=
      (Measure.map_map hg (measurable_blockSplit _ _ _ _ hf)).symm
    _=((Measure.pi (fun _ : Fin H => (ρ : Measure _))).prod rest).map
        (fun z => (obs z.2,PrivateRowSorting.sortRow E H z.1)) := by rw [hm]
    _=(((Measure.pi (fun _ : Fin H => (ρ : Measure _))).prod rest).map Prod.swap).map
        (Prod.map obs (PrivateRowSorting.sortRow E H)) := by
      rw [Measure.map_map (hobs.prodMap (PrivateRowSorting.measurable_sortRow E H)) measurable_swap]
      rfl
    _=(rest.map obs).prod (PrivateRowSorting.sortedOriginalIid E H ρ : Measure _) := by
      rw [(Measure.measurePreserving_swap
        (μ := Measure.pi (fun _ : Fin H => (ρ : Measure (Ici E.H ⊕ Icc E.R E.Rp))))
        (ν := rest)).map_eq,
        ←Measure.map_prod_map _ _ hobs (PrivateRowSorting.measurable_sortRow E H)]
      rfl

end SortedPrivate

section PosteriorTransfer
variable {X O Y : Type*} [MeasurableSpace X] [MeasurableSpace O] [MeasurableSpace Y]
  [StandardBorelSpace Y] [Nonempty Y]

lemma restrict_compProd_fst (ν : Measure O) [IsFiniteMeasure ν]
    (κ : Kernel O X) [IsMarkovKernel κ] (S : Set O) (hS : MeasurableSet S) :
    (ν ⊗ₘ κ).restrict (S ×ˢ univ)=(ν.restrict S) ⊗ₘ κ := by
  ext T hT
  rw [Measure.restrict_apply hT,Measure.compProd_apply (hT.inter (hS.prod MeasurableSet.univ)),
    Measure.compProd_apply hT,←lintegral_indicator hS]
  apply lintegral_congr
  intro o
  by_cases ho : o∈S
  · simp [ho,Set.preimage_inter]
  · simp [ho,Set.preimage_inter]

lemma kernels_ae_eq_of_compProd_eq (ν : Measure O) [IsFiniteMeasure ν]
    (κ η : Kernel O Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : ν ⊗ₘ κ=ν ⊗ₘ η) : κ=ᵐ[ν]η := by
  have hκ := condKernel_compProd ν κ
  have hη := condKernel_compProd ν η
  simp only [h] at hκ
  exact hκ.symm.trans hη

theorem posterior_row_of_restricted_joint
    (μ : Measure X) [IsProbabilityMeasure μ]
    (obs : X → O) (hobs : Measurable obs)
    (B : Kernel O X) [IsMarkovKernel B]
    (hB : μ.map (fun x => (obs x,x))=(μ.map obs) ⊗ₘ B)
    (row : X → Y) (hrow : Measurable row)
    (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (S : Set O) (hS : MeasurableSet S)
    (hjoint : (μ.restrict (obs ⁻¹' S)).map (fun x => (obs x,row x))=
      ((μ.map obs).restrict S).prod ρ) :
    ∀ᵐ o ∂μ.map obs,o∈S → (B o).map row=ρ := by
  letI : IsMarkovKernel (B.map row) := Kernel.IsMarkovKernel.map B hrow
  have he : ((μ.map obs).restrict S) ⊗ₘ B.map row=
      ((μ.map obs).restrict S) ⊗ₘ Kernel.const O ρ := by
    rw [Measure.compProd_const]
    calc
      _=(((μ.map obs).restrict S) ⊗ₘ B).map (Prod.map id row) :=
        Measure.compProd_map hrow
      _=(((μ.map obs) ⊗ₘ B).restrict (S ×ˢ univ)).map (Prod.map id row) := by
        rw [restrict_compProd_fst _ B S hS]
      _=((μ.map (fun x => (obs x,x))).restrict (S ×ˢ univ)).map (Prod.map id row) := by rw [hB]
      _=((μ.restrict (obs ⁻¹' S)).map (fun x => (obs x,x))).map (Prod.map id row) := by
        have ht := Measure.restrict_map (μ := μ) (hobs.prodMk measurable_id)
          (hS.prod MeasurableSet.univ)
        have heq : (μ.map (fun x => (obs x,x))).restrict (S ×ˢ univ) =
            (μ.restrict (obs ⁻¹' S)).map (fun x => (obs x,x)) := by
          simpa only [id_eq, Set.preimage, Set.mem_prod, Set.mem_univ, and_true] using ht
        rw [heq]
      _=(μ.restrict (obs ⁻¹' S)).map (fun x => (obs x,row x)) := by
        have ht := Measure.map_map (μ := μ.restrict (obs ⁻¹' S))
          (measurable_id.prodMap hrow) (hobs.prodMk measurable_id)
        simpa only [Function.comp_def, Prod.map_apply, id_eq] using ht
      _=_ := hjoint
  have ha := kernels_ae_eq_of_compProd_eq ((μ.map obs).restrict S)
    (B.map row) (Kernel.const O ρ) he
  have hr : ∀ᵐ o ∂(μ.map obs).restrict S,(B o).map row=ρ := by
    filter_upwards [ha] with o ho
    simpa only [Kernel.map_apply _ hrow,Kernel.const_apply] using ho
  exact (ae_restrict_iff' hS).mp hr

omit [StandardBorelSpace Y] [Nonempty Y] in

theorem sampler_mean_of_row_law {α P : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace P] (f : (P×Y) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P) (μ : Measure X)
    [IsProbabilityMeasure μ] (r : X → Y) (hr : Measurable r)
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (hlaw : μ.map r=ρ) (i : α) :
    (∫ z : X×unitInterval,if i∈f (p,r z.1) z.2 then (1:ℝ) else 0 ∂μ.prod volume)=
      LocalSamplerMean.mean f p ρ i := by
  have hm := Measure.map_prod_map μ (volume : Measure unitInterval) hr measurable_id
  rw [hlaw,Measure.map_id] at hm
  unfold LocalSamplerMean.mean
  rw [hm,integral_map (hr.prodMap measurable_id).aemeasurable
    (LocalSamplerMean.measurable_indicator f hf p i).aestronglyMeasurable]
  rfl

end PosteriorTransfer
end FCAppendix.Affine.Tail04.PrivateConditionalRows
