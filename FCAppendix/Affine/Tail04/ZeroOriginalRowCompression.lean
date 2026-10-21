import FCAppendix.Affine.Tail04.ZeroCommonMenuCount

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroOriginalRowCompression
open MeasureTheory ProbabilityTheory Set Classical
open FiniteTailNoisyGame OriginalActiveCompression ZeroCommonMenuCount
open scoped BigOperators

def rowObservable (D : Data) {N : ℕ} {X : Type*} [MeasurableSpace X]
    (tag : X→ Fin 4) (decode : X→ Icc (1:ℝ) D.U)
    (g : (kind : Fin N→ Fin 4)→(Fin (D.count kind 1)→ Icc (1:ℝ) D.U)→ℝ)
    (r : Fin N→ X) : ℝ :=
  g (tags tag r) (baseCommonRow D decode (tags tag r) r)

theorem measurable_rowObservable (D : Data) {N : ℕ} {X : Type*} [MeasurableSpace X]
    (tag : X→ Fin 4) (htag : Measurable tag)
    (decode : X→ Icc (1:ℝ) D.U) (hdecode : Measurable decode)
    (g : (kind : Fin N→ Fin 4)→(Fin (D.count kind 1)→ Icc (1:ℝ) D.U)→ℝ)
    (hg : ∀kind,Measurable (g kind)) :
    Measurable (rowObservable D tag decode g) :=
  LocalCoordinates.measurable_finite_eval (tags tag)
    (fun r kind => g kind (baseCommonRow D decode kind r)) (measurable_tags tag htag)
    (fun kind=>(hg kind).comp (measurable_baseCommonRow D decode hdecode kind))

theorem integrable_rowObservable (D : Data) {N : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Fin N→ X)) [IsFiniteMeasure μ]
    (tag : X→ Fin 4) (htag : Measurable tag)
    (decode : X→ Icc (1:ℝ) D.U) (hdecode : Measurable decode)
    (g : (kind : Fin N→ Fin 4)→(Fin (D.count kind 1)→ Icc (1:ℝ) D.U)→ℝ)
    (hg : ∀kind,Measurable (g kind))
    (C : ℝ) (hbound : ∀kind row,‖g kind row‖≤ C) :
    Integrable (rowObservable D tag decode g) μ :=
  Integrable.of_bound (measurable_rowObservable D tag htag decode hdecode g hg).aestronglyMeasurable
    C (ae_of_all _ fun r=> hbound (tags tag r) _)

theorem conditional_integral (D : Data) {N : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X→ Fin 4) (htag : Measurable tag)
    (decode : X→ Icc (1:ℝ) D.U) (hdecode : Measurable decode)
    (hmass : ∀k,μ (tag ⁻¹' {k})≠0)
    (ρ : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (hρ : (cond μ (tag ⁻¹' {1})).map decode=(ρ : Measure _))
    (g : (kind : Fin N→ Fin 4)→(Fin (D.count kind 1)→ Icc (1:ℝ) D.U)→ℝ)
    (hg : ∀kind,Measurable (g kind)) (kind : Fin N→ Fin 4) :
    (∫r,rowObservable D tag decode g r
      ∂Measure.pi (fun i=> cond μ (tag ⁻¹' {kind i})))=
      ∫row : Fin (D.count kind 1)→ Icc (1:ℝ) D.U,g kind row
        ∂Measure.pi (fun _ : Fin (D.count kind 1)=>(ρ : Measure _)) := by
  rw [←baseCommonRow_law D μ tag decode hdecode hmass ρ hρ kind,
    integral_map (measurable_baseCommonRow D decode hdecode kind).aemeasurable
      (hg kind).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_tags_conditional μ tag htag hmass kind] with r hr
  exact congrArg (fun kind' : Fin N→Fin 4 =>
    g kind' (baseCommonRow D decode kind' r)) hr

theorem original_integral (D : Data) {N : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X→ Fin 4) (htag : Measurable tag)
    (decode : X→ Icc (1:ℝ) D.U) (hdecode : Measurable decode)
    (hmass : ∀k,μ (tag ⁻¹' {k})≠0)
    (ρ : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (hρ : (cond μ (tag ⁻¹' {1})).map decode=(ρ : Measure _))
    (hcat : ∀k,μ (tag ⁻¹' {k})=ENNReal.ofReal (D.categories.mass k))
    (g : (kind : Fin N→ Fin 4)→(Fin (D.count kind 1)→ Icc (1:ℝ) D.U)→ℝ)
    (hg : ∀kind,Measurable (g kind))
    (C : ℝ) (hbound : ∀kind row,‖g kind row‖≤ C) :
    (∫r,rowObservable D tag decode g r ∂Measure.pi (fun _ : Fin N=> μ))=
      ∑kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
        ∫row : Fin (D.count kind 1)→ Icc (1:ℝ) D.U,g kind row
          ∂Measure.pi (fun _ : Fin (D.count kind 1)=>(ρ : Measure _)) := by
  haveI (kind : Fin N→ Fin 4) (i : Fin N) :
      IsProbabilityMeasure (cond μ (tag ⁻¹' {kind i})) :=
    cond_isProbabilityMeasure (hmass (kind i))
  have hw (kind : Fin N→ Fin 4) : (∏i,μ (tag ⁻¹' {kind i}))=
      ENNReal.ofReal ((CommonList.iid D.categories N).mass kind) := by
    simp_rw [hcat]
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _=> D.categories.nonneg (kind i))).symm
  have hi (kind : Fin N→ Fin 4) : Integrable (rowObservable D tag decode g)
      (Measure.pi (fun i=> cond μ (tag ⁻¹' {kind i}))) :=
    integrable_rowObservable D _ tag htag decode hdecode g hg C hbound
  rw [OriginalFiniteFibers.iid_finite_disintegration μ tag htag]
  simp_rw [hw]
  rw [integral_finsetSum_measure (fun kind _=>(hi kind).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr (M:=ℝ) ?_ ?_
  · ext kind
    simp only [Finset.mem_univ]
  · intro kind _
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal ((CommonList.iid D.categories N).nonneg kind),
      conditional_integral D μ tag htag decode hdecode hmass ρ hρ g hg kind]
    rfl

end FCAppendix.Affine.Tail04.ZeroOriginalRowCompression
