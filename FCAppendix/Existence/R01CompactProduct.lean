import FCAppendix.Existence.R01Distributional

noncomputable section
namespace FCAppendix.Existence.Distributional
open MeasureTheory ProbabilityTheory Topology Set Classical
open scoped BoundedContinuousFunction

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y]
  [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y] [BorelSpace Y]

def productLaw (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    ProbabilityMeasure (X × Y) :=
  ⟨(μ : Measure X).prod (ν : Measure Y), inferInstance⟩

theorem continuous_productLaw : Continuous
    (fun p : ProbabilityMeasure X × ProbabilityMeasure Y => productLaw p.1 p.2) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  let g : ProbabilityMeasure Y × X → ℝ := fun p => ∫ y, f (p.2, y) ∂(p.1 : Measure Y)
  have hg : Continuous g :=
    (continuous_law_integral (fun p : X × Y => f p) f.continuous).comp
      (continuous_snd.prodMk continuous_fst)
  have hc := (continuous_law_integral g hg).comp
    (continuous_snd.prodMk continuous_fst)
  convert hc using 1
  funext p
  change (∫ z, f z ∂((p.1 : Measure X).prod (p.2 : Measure Y))) = _
  exact integral_prod _ ((ContinuousMap.equivBoundedOfCompact _ _ f).integrable _)

def rowLaw (N : ℕ) (μ : ProbabilityMeasure X) : ProbabilityMeasure (Fin N → X) :=
  match N with
  | 0 => ⟨Measure.dirac (fun i => Fin.elim0 i), Measure.dirac.isProbabilityMeasure⟩
  | N + 1 => (productLaw μ (rowLaw N μ)).map
      (show Measurable (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2) from by
        apply measurable_pi_lambda
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using (measurable_fst : Measurable (Prod.fst : X × (Fin N → X) → X))
        · simpa only [Function.comp_def, Fin.cons_succ] using (measurable_pi_apply j).comp measurable_snd).aemeasurable

theorem continuous_rowLaw (N : ℕ) : Continuous (rowLaw (X := X) N) := by
  induction N with
  | zero => exact continuous_const
  | succ N ih =>
    have hc : Continuous (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2) := by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using (continuous_fst : Continuous (Prod.fst : X × (Fin N → X) → X))
      · simpa only [Function.comp_def, Fin.cons_succ] using (continuous_apply j).comp continuous_snd
    exact (ProbabilityMeasure.continuous_map hc).comp
      (continuous_productLaw.comp (continuous_id.prodMk ih))

theorem integral_rowLaw_succ (N : ℕ) (μ : ProbabilityMeasure X)
    (f : (Fin (N + 1) → X) → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂(rowLaw (N + 1) μ : Measure (Fin (N + 1) → X))) =
      ∫ x, ∫ xs, f (Fin.cons x xs) ∂(rowLaw N μ : Measure (Fin N → X)) ∂(μ : Measure X) := by
  have hc : Continuous (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (continuous_fst : Continuous (Prod.fst : X × (Fin N → X) → X))
    · simpa only [Function.comp_def, Fin.cons_succ] using (continuous_apply j).comp continuous_snd
  change (∫ x, f x ∂(((μ : Measure X).prod (rowLaw N μ : Measure (Fin N → X))).map
    (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2))) = _
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ ((ContinuousMap.equivBoundedOfCompact _ _
    (⟨_, hf.comp hc⟩ : C(X × (Fin N → X), ℝ))).integrable _)

omit [BorelSpace X] in

theorem rowLaw_all (N : ℕ) (μ : ProbabilityMeasure X) (C : Set X) (hC : MeasurableSet C) :
    (rowLaw N μ : Measure (Fin N → X)) {x | ∀ i, x i ∈ C} = (μ : Measure X) C ^ N := by
  induction N with
  | zero => simp [rowLaw]
  | succ N ih =>
    have hs : MeasurableSet {x : Fin (N + 1) → X | ∀ i, x i ∈ C} :=
      by simpa only [Set.setOf_forall, Set.preimage] using
        (MeasurableSet.iInter fun i => hC.preimage (measurable_pi_apply i))
    have hm : Measurable (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2) := by
      apply measurable_pi_lambda
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using (measurable_fst : Measurable (Prod.fst : X × (Fin N → X) → X))
      · simpa only [Function.comp_def, Fin.cons_succ] using (measurable_pi_apply j).comp measurable_snd
    change (((μ : Measure X).prod (rowLaw N μ : Measure (Fin N → X))).map
      (fun p => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2)) _ = _
    rw [Measure.map_apply hm hs]
    have he : (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2) ⁻¹'
        {x | ∀ i, x i ∈ C} = C ×ˢ {x : Fin N → X | ∀ i, x i ∈ C} := by
      ext p
      simp [Fin.forall_fin_succ]
    rw [he, Measure.prod_prod, ih, pow_succ, mul_comm]

omit [BorelSpace X] in

theorem rowLaw_coordinate (N : ℕ) (μ : ProbabilityMeasure X) (i : Fin N) :
    (rowLaw N μ : Measure (Fin N → X)).map (fun x => x i) = (μ : Measure X) := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
    have hc : Measurable (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2) := by
      apply measurable_pi_lambda
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using (measurable_fst : Measurable (Prod.fst : X × (Fin N → X) → X))
      · simpa only [Function.comp_def, Fin.cons_succ] using (measurable_pi_apply k).comp measurable_snd
    apply Measure.ext
    intro C hC
    rw [Measure.map_apply (measurable_pi_apply i) hC]
    change (((μ : Measure X).prod (rowLaw N μ : Measure (Fin N → X))).map
      (fun p => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2)) _ = _
    rw [Measure.map_apply hc (hC.preimage (measurable_pi_apply i))]
    refine Fin.cases ?_ (fun j => ?_) i
    · have he : (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2) ⁻¹'
          ((fun x : Fin (N + 1) → X => x 0) ⁻¹' C) = C ×ˢ (univ : Set (Fin N → X)) := by
        ext p; simp
      rw [he, Measure.prod_prod, measure_univ, mul_one]
    · have he : (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N + 1) => X) p.1 p.2) ⁻¹'
          ((fun x : Fin (N + 1) → X => x j.succ) ⁻¹' C) =
            (univ : Set X) ×ˢ ((fun x : Fin N → X => x j) ⁻¹' C) := by
        ext p; simp
      rw [he, Measure.prod_prod, measure_univ, one_mul,
        ← Measure.map_apply (measurable_pi_apply j) hC, ih j]

omit [BorelSpace X] in

theorem integral_row_class_count (N : ℕ) (μ : ProbabilityMeasure X)
    (C : Set X) (hC : MeasurableSet C) :
    (∫ x, ∑ i : Fin N, if x i ∈ C then (1 : ℝ) else 0
      ∂(rowLaw N μ : Measure (Fin N → X))) = (N : ℝ) * (μ : Measure X).real C := by
  classical
  have hint : ∀ i : Fin N, Integrable
      (fun x : Fin N → X => if x i ∈ C then (1 : ℝ) else 0) (rowLaw N μ : Measure _) := by
    intro i
    exact (integrable_const (1 : ℝ)).indicator (hC.preimage (measurable_pi_apply i))
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have he : ∀ i : Fin N,
      (∫ x : Fin N → X, if x i ∈ C then (1 : ℝ) else 0 ∂(rowLaw N μ : Measure _)) =
        (μ : Measure X).real C := by
    intro i
    have hm := integral_map (φ := fun x : Fin N → X => x i)
      (f := C.indicator (fun _ : X => (1 : ℝ)))
      (μ := (rowLaw N μ : Measure _)) (measurable_pi_apply i).aemeasurable
      ((measurable_const.indicator hC).aestronglyMeasurable)
    rw [rowLaw_coordinate] at hm
    calc
      _ = ∫ x, C.indicator (fun _ : X => (1 : ℝ)) x ∂(μ : Measure X) := by
        simpa only [Set.indicator_apply] using hm.symm
      _ = _ := by simpa [Measure.real] using
        integral_indicator_const (μ := (μ : Measure X)) (1 : ℝ) hC
  simp_rw [he]
  simp
end FCAppendix.Existence.Distributional
