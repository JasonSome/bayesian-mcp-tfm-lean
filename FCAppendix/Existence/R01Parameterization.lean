import FCAppendix.Existence.R01Distributional

noncomputable section
namespace FCAppendix.Existence.Distributional
open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal BoundedContinuousFunction

variable {T Q A Z : Type*}
  [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace Q] [MeasurableSpace Q] [CompactSpace Q] [MetrizableSpace Q]
  [BorelSpace Q] [Nonempty Q] [StandardBorelSpace Q]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A] [MetrizableSpace A]
  [BorelSpace A] [Nonempty A] [StandardBorelSpace A]
  [TopologicalSpace Z] [MeasurableSpace Z] [CompactSpace Z] [MetrizableSpace Z]
  [BorelSpace Z]

def pushLaw (μ : Measure T) [IsProbabilityMeasure μ]
    (φ : T × Q → A) (hφ : Continuous φ) (π : Law (A := Q) μ) : Law (A := A) μ := by
  let f : T × Q → T × A := fun x => (x.1, φ x)
  have hf : Measurable f := measurable_fst.prodMk hφ.measurable
  refine ⟨π.1.map hf.aemeasurable, ?_⟩
  change ((π.1 : Measure (T × Q)).map f).map Prod.fst = μ
  rw [Measure.map_map measurable_fst hf]
  exact π.2

omit [CompactSpace T] [PolishSpace T] [Nonempty Q] [StandardBorelSpace Q]
  [Nonempty A] [StandardBorelSpace A] in
theorem continuous_pushLaw (μ : Measure T) [IsProbabilityMeasure μ]
    (φ : T × Q → A) (hφ : Continuous φ) : Continuous (pushLaw μ φ hφ) :=
  Continuous.subtype_mk
    ((ProbabilityMeasure.continuous_map (continuous_fst.prodMk hφ)).comp continuous_subtype_val) _

omit [CompactSpace T] [PolishSpace T] [Nonempty Q] [StandardBorelSpace Q]
  [Nonempty A] [StandardBorelSpace A] in

theorem integral_pushLaw (μ : Measure T) [IsProbabilityMeasure μ]
    (φ : T × Q → A) (hφ : Continuous φ) (π : Law (A := Q) μ)
    (f : T × A → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂((pushLaw μ φ hφ π).1 : Measure (T × A))) =
      ∫ x, f (x.1, φ x) ∂(π.1 : Measure (T × Q)) := by
  exact integral_map (measurable_fst.prodMk hφ.measurable).aemeasurable
    hf.aestronglyMeasurable

theorem exists_parameterized_law (μ : Measure T) [IsProbabilityMeasure μ]
    (φ : T × Q → A) (hφ : Continuous φ)
    (u : Law (A := A) μ × (T × A) → ℝ) (hu : Continuous u) :
    ∃ (πq : Law (A := Q) μ) (σ : Kernel T A), IsMarkovKernel σ ∧
      μ ⊗ₘ σ = ((pushLaw μ φ hφ πq).1 : Measure (T × A)) ∧
      (∀ᵐ t ∂μ, ∀ᵐ a ∂σ t, ∀ q : Q,
        u (pushLaw μ φ hφ πq, (t, φ (t, q))) ≤
          u (pushLaw μ φ hφ πq, (t, a))) := by
  let v : Law (A := Q) μ × (T × Q) → ℝ := fun p =>
    u (pushLaw μ φ hφ p.1, (p.2.1, φ p.2))
  have hv : Continuous v := hu.comp
    (((continuous_pushLaw μ φ hφ).comp continuous_fst).prodMk
      ((continuous_fst.comp continuous_snd).prodMk (hφ.comp continuous_snd)))
  obtain ⟨πq, σq, hmarkq, hdisq, ha, _⟩ := exists_symmetric_law μ v hv
  let π := pushLaw μ φ hφ πq
  let good : Set (T × A) := {x | ∀ q : Q,
    u (π, (x.1, φ (x.1, q))) ≤ u (π, x)}
  have hgood : MeasurableSet good := by
    have he : good = ⋂ q : Q, {x : T × A |
        u (π, (x.1, φ (x.1, q))) ≤ u (π, x)} := by ext x; simp [good]
    rw [he]
    apply IsClosed.measurableSet
    apply isClosed_iInter
    intro q
    apply isClosed_le
    · exact hu.comp (continuous_const.prodMk
        (continuous_fst.prodMk (hφ.comp (continuous_fst.prodMk continuous_const))))
    · exact hu.comp (continuous_const.prodMk continuous_id)
  have hπ : ∀ᵐ x ∂(π.1 : Measure (T × A)), x ∈ good := by
    change ∀ᵐ x ∂((πq.1 : Measure (T × Q)).map (fun x => (x.1, φ x))), x ∈ good
    exact (ae_map_iff (f := fun x : T × Q => (x.1, φ x))
      (p := fun x => x ∈ good)
      (measurable_fst.prodMk hφ.measurable).aemeasurable hgood).mpr ha
  let σ := (π.1 : Measure (T × A)).condKernel
  have hdis : μ ⊗ₘ σ = (π.1 : Measure (T × A)) := by
    calc
      μ ⊗ₘ σ = (π.1 : Measure (T × A)).fst ⊗ₘ σ :=
        congrArg (fun ν : Measure T => ν ⊗ₘ σ) π.2.symm
      _ = (π.1 : Measure (T × A)) := Measure.disintegrate _ _
  refine ⟨πq, σ, inferInstance, hdis, ?_⟩
  rw [← hdis] at hπ
  exact (Measure.ae_compProd_iff hgood).mp hπ

def isolatedLift (φ : T × Q → A) : T × (Unit ⊕ Q) → Unit ⊕ A :=
  fun x => match x.2 with
    | Sum.inl _ => Sum.inl ()
    | Sum.inr q => Sum.inr (φ (x.1, q))

omit [MeasurableSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [MeasurableSpace Q] [CompactSpace Q] [MetrizableSpace Q] [BorelSpace Q]
  [Nonempty Q] [StandardBorelSpace Q] [MeasurableSpace A] [CompactSpace A]
  [MetrizableSpace A] [BorelSpace A] [Nonempty A] [StandardBorelSpace A] in
theorem continuous_isolatedLift (φ : T × Q → A) (hφ : Continuous φ) :
    Continuous (isolatedLift φ) := by
  have hc : Continuous (Sum.elim (fun _ : T × Unit => (Sum.inl () : Unit ⊕ A))
      (fun x : T × Q => Sum.inr (φ x))) :=
    continuous_const.sumElim (continuous_inr.comp hφ)
  convert hc.comp (Homeomorph.prodSumDistrib (X := T) (Y := Unit) (Z := Q)).continuous using 1
  funext x
  rcases x with ⟨t, q⟩
  cases q <;> rfl

omit [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace Q] [MeasurableSpace Q] [CompactSpace Q] [MetrizableSpace Q]
  [BorelSpace Q] [Nonempty Q] [StandardBorelSpace Q]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A] [MetrizableSpace A]
  [BorelSpace A] [Nonempty A] [StandardBorelSpace A] in
@[simp] theorem isolatedLift_abstain (φ : T × Q → A) (t : T) :
    isolatedLift φ (t, Sum.inl ()) = Sum.inl () := rfl

omit [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace Q] [MeasurableSpace Q] [CompactSpace Q] [MetrizableSpace Q]
  [BorelSpace Q] [Nonempty Q] [StandardBorelSpace Q]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A] [MetrizableSpace A]
  [BorelSpace A] [Nonempty A] [StandardBorelSpace A] in
@[simp] theorem isolatedLift_active (φ : T × Q → A) (t : T) (q : Q) :
    isolatedLift φ (t, Sum.inr q) = Sum.inr (φ (t, q)) := rfl

def noisyLaw (μ : Measure T) [IsProbabilityMeasure μ]
    (θ : ProbabilityMeasure Z) (φ : (T × Q) × Z → A) (hφ : Continuous φ)
    (π : Law (A := Q) μ) : Law (A := A) μ := by
  let ψ : (T × Q) × Z → T × A := fun x => (x.1.1, φ x)
  have hψ : Measurable ψ := (measurable_fst.comp measurable_fst).prodMk hφ.measurable
  let ν : Measure (T × A) := ((π.1 : Measure (T × Q)).prod (θ : Measure Z)).map ψ
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hψ.aemeasurable
  refine ⟨⟨ν, inferInstance⟩, ?_⟩
  change ν.map Prod.fst = μ
  dsimp [ν]
  rw [Measure.map_map measurable_fst hψ]
  apply Measure.ext
  intro S hS
  change ((π.1 : Measure (T × Q)).prod (θ : Measure Z)).map
    (Prod.fst ∘ Prod.fst) S = μ S
  rw [Measure.map_apply (measurable_fst.comp measurable_fst) hS]
  have he : ((Prod.fst : T × Q → T) ∘
      (Prod.fst : (T × Q) × Z → T × Q)) ⁻¹' S =
      ((Prod.fst : T × Q → T) ⁻¹' S) ×ˢ (univ : Set Z) := by
    ext x; simp
  rw [he, Measure.prod_prod, measure_univ, mul_one,
    ← Measure.map_apply measurable_fst hS, π.2]

omit [Nonempty Q] [StandardBorelSpace Q] [Nonempty A] [StandardBorelSpace A] in

theorem integral_noisyLaw (μ : Measure T) [IsProbabilityMeasure μ]
    (θ : ProbabilityMeasure Z) (φ : (T × Q) × Z → A) (hφ : Continuous φ)
    (π : Law (A := Q) μ) (f : T × A → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂((noisyLaw μ θ φ hφ π).1 : Measure (T × A))) =
      ∫ x, ∫ z, f (x.1, φ (x, z)) ∂(θ : Measure Z) ∂(π.1 : Measure (T × Q)) := by
  change (∫ x, f x ∂(((π.1 : Measure (T × Q)).prod (θ : Measure Z)).map
    (fun x => (x.1.1, φ x)))) = _
  rw [integral_map (φ := fun x : (T × Q) × Z => (x.1.1, φ x))
    ((measurable_fst.comp measurable_fst).prodMk hφ.measurable).aemeasurable
    hf.aestronglyMeasurable]
  apply integral_prod
  have hc := hf.comp ((continuous_fst.comp continuous_fst).prodMk hφ)
  let f' : C((T × Q) × Z, ℝ) := ⟨_, hc⟩
  exact (ContinuousMap.equivBoundedOfCompact _ _ f').integrable _

omit [Nonempty Q] [StandardBorelSpace Q] [Nonempty A] [StandardBorelSpace A] in

theorem continuous_noisyLaw (μ : Measure T) [IsProbabilityMeasure μ]
    (θ : ProbabilityMeasure Z) (φ : (T × Q) × Z → A) (hφ : Continuous φ) :
    Continuous (noisyLaw μ θ φ hφ) := by
  apply Continuous.subtype_mk
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  let g : T × Q → ℝ := fun x => ∫ z, f (x.1, φ (x, z)) ∂(θ : Measure Z)
  have hg : Continuous g :=
    (continuous_law_integral (fun x : (T × Q) × Z => f (x.1.1, φ x))
      (f.continuous.comp ((continuous_fst.comp continuous_fst).prodMk hφ))).comp
        (continuous_id.prodMk continuous_const)
  have hc := (ProbabilityMeasure.continuous_integral_continuousMap
    (⟨g, hg⟩ : C(T × Q, ℝ))).comp
      (continuous_subtype_val : Continuous (fun π : Law (A := Q) μ => π.1))
  convert hc using 1
  funext π
  exact integral_noisyLaw μ θ φ hφ π f f.continuous

omit [Nonempty A] [StandardBorelSpace A] in

theorem exists_noisy_law (μ : Measure T) [IsProbabilityMeasure μ]
    (θ : ProbabilityMeasure Z) (φ : (T × Q) × Z → A) (hφ : Continuous φ)
    (u : Law (A := A) μ × (T × A) → ℝ) (hu : Continuous u) :
    ∃ (π : Law (A := Q) μ) (σ : Kernel T Q), IsMarkovKernel σ ∧
      μ ⊗ₘ σ = (π.1 : Measure (T × Q)) ∧
      (∀ᵐ t ∂μ, ∀ᵐ q ∂σ t, ∀ q' : Q,
        (∫ z, u (noisyLaw μ θ φ hφ π, (t, φ ((t, q'), z))) ∂(θ : Measure Z)) ≤
        ∫ z, u (noisyLaw μ θ φ hφ π, (t, φ ((t, q), z))) ∂(θ : Measure Z)) := by
  let f : (Law (A := Q) μ × (T × Q)) × Z → ℝ := fun x =>
    u (noisyLaw μ θ φ hφ x.1.1, (x.1.2.1, φ (x.1.2, x.2)))
  have hf : Continuous f := hu.comp
    (((continuous_noisyLaw μ θ φ hφ).comp (continuous_fst.comp continuous_fst)).prodMk
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
        (hφ.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))))
  let v : Law (A := Q) μ × (T × Q) → ℝ := fun p => ∫ z, f (p, z) ∂(θ : Measure Z)
  have hv : Continuous v := (continuous_law_integral f hf).comp
    (continuous_id.prodMk continuous_const)
  obtain ⟨π, σ, hm, hd, _, ho⟩ := exists_symmetric_law μ v hv
  exact ⟨π, σ, hm, hd, ho⟩

omit [Nonempty Q] [StandardBorelSpace Q] [Nonempty A] [StandardBorelSpace A] in

theorem parameterized_fiber_support (μ : Measure T) [IsProbabilityMeasure μ]
    (φ : T × Q → A) (hφ : Continuous φ) (π : Law (A := Q) μ)
    (σ : Kernel T A) [IsMarkovKernel σ]
    (hdis : μ ⊗ₘ σ = ((pushLaw μ φ hφ π).1 : Measure (T × A))) :
    ∀ᵐ t ∂μ, ∀ᵐ a ∂σ t, ∃ q : Q, φ (t, q) = a := by
  let ψ : T × Q → T × A := fun x => (x.1, φ x)
  have hψ : Continuous ψ := continuous_fst.prodMk hφ
  let G : Set (T × A) := Set.range ψ
  have hG : MeasurableSet G :=
    (isCompact_range hψ).isClosed.measurableSet
  have hgood : ∀ᵐ x ∂((pushLaw μ φ hφ π).1 : Measure (T × A)), x ∈ G := by
    change ∀ᵐ x ∂((π.1 : Measure (T × Q)).map ψ), x ∈ G
    exact (ae_map_iff (f := ψ) (p := fun x => x ∈ G)
      hψ.measurable.aemeasurable hG).mpr (ae_of_all _ fun x => Set.mem_range_self x)
  rw [← hdis] at hgood
  have hsplit := (Measure.ae_compProd_iff hG).mp hgood
  filter_upwards [hsplit] with t ht
  filter_upwards [ht] with a ha
  obtain ⟨⟨t', q⟩, he⟩ := ha
  have ht' : t' = t := congrArg Prod.fst he
  subst t'
  exact ⟨q, congrArg Prod.snd he⟩

omit [CompactSpace A] [MetrizableSpace A] in

theorem exists_noisy_law_of_continuous_expectation
    (μ : Measure T) [IsProbabilityMeasure μ]
    (θ : ProbabilityMeasure Z) (φ : (T × Q) × Z → A) (hφ : Continuous φ)
    (u : Law (A := A) μ × (T × A) → ℝ)
    (_hi : ∀ (π : Law (A := Q) μ) (t : T) (q : Q),
      Integrable (fun z => u (noisyLaw μ θ φ hφ π, (t, φ ((t, q), z))))
        (θ : Measure Z))
    (hc : Continuous (fun p : Law (A := Q) μ × (T × Q) =>
      ∫ z, u (noisyLaw μ θ φ hφ p.1, (p.2.1, φ (p.2, z))) ∂(θ : Measure Z))) :
    ∃ (π : Law (A := Q) μ) (σq : Kernel T Q) (σa : Kernel T A),
      IsMarkovKernel σq ∧ IsMarkovKernel σa ∧
      μ ⊗ₘ σq = (π.1 : Measure (T × Q)) ∧
      μ ⊗ₘ σa = ((noisyLaw μ θ φ hφ π).1 : Measure (T × A)) ∧
      (∀ᵐ t ∂μ, ∀ᵐ q ∂σq t, ∀ q' : Q,
        (∫ z, u (noisyLaw μ θ φ hφ π, (t, φ ((t, q'), z))) ∂(θ : Measure Z)) ≤
        ∫ z, u (noisyLaw μ θ φ hφ π, (t, φ ((t, q), z))) ∂(θ : Measure Z)) := by
  let v : Law (A := Q) μ × (T × Q) → ℝ := fun p =>
    ∫ z, u (noisyLaw μ θ φ hφ p.1, (p.2.1, φ (p.2, z))) ∂(θ : Measure Z)
  obtain ⟨π, σq, hq, hdq, _, ho⟩ := exists_symmetric_law μ v hc
  let implemented := noisyLaw μ θ φ hφ π
  let σa := (implemented.1 : Measure (T × A)).condKernel
  have hda : μ ⊗ₘ σa = (implemented.1 : Measure (T × A)) := by
    calc
      μ ⊗ₘ σa = (implemented.1 : Measure (T × A)).fst ⊗ₘ σa :=
        congrArg (fun ν : Measure T => ν ⊗ₘ σa) implemented.2.symm
      _ = (implemented.1 : Measure (T × A)) := Measure.disintegrate _ _
  exact ⟨π, σq, σa, hq, inferInstance, hdq, hda, ho⟩
end FCAppendix.Existence.Distributional
