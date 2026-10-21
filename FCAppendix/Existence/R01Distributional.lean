import FCAppendix.Existence.R01External.FixedMarginal
import FCAppendix.Existence.R01External.ProbabilityMeasureWeakDual
import FCAppendix.Existence.R01External.FanGlicksberg
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

noncomputable section
namespace FCAppendix.Existence.Distributional
open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal BoundedContinuousFunction BigOperators

section Integral
variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

private theorem integrable_continuous (f : C(X, ℝ)) (ν : ProbabilityMeasure X) :
    Integrable (fun x => f x) (ν : Measure X) := by
  refine ⟨f.continuous.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := ‖f‖) ?_⟩
  exact ae_of_all _ fun x => f.norm_coe_le_norm x

theorem continuous_integral_pair :
    Continuous (fun p : C(X, ℝ) × ProbabilityMeasure X =>
      ∫ x, p.1 x ∂(p.2 : Measure X)) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hleft : ∀ᶠ q : C(X, ℝ) × ProbabilityMeasure X in 𝓝 p,
      ‖q.1 - p.1‖ < ε / 2 := by
    have hc : Continuous (fun q : C(X, ℝ) × ProbabilityMeasure X => ‖q.1 - p.1‖) :=
      (continuous_fst.sub continuous_const).norm
    have hp : ‖p.1 - p.1‖ < ε / 2 := by simpa using hε2
    exact hc.continuousAt.eventually (Iio_mem_nhds hp)
  have hright : ∀ᶠ q : C(X, ℝ) × ProbabilityMeasure X in 𝓝 p,
      |(∫ x, p.1 x ∂(q.2 : Measure X)) - ∫ x, p.1 x ∂(p.2 : Measure X)| < ε / 2 := by
    have hc := (ProbabilityMeasure.continuous_integral_continuousMap p.1).comp
      (continuous_snd : Continuous (Prod.snd : C(X, ℝ) × ProbabilityMeasure X → _))
    simpa [Real.dist_eq] using hc.continuousAt.eventually
      (Metric.ball_mem_nhds _ hε2)
  filter_upwards [hleft, hright] with q hq₁ hq₂
  have hbound : |(∫ x, q.1 x ∂(q.2 : Measure X)) - ∫ x, p.1 x ∂(q.2 : Measure X)|
      ≤ ‖q.1 - p.1‖ := by
    rw [← integral_sub (integrable_continuous q.1 q.2) (integrable_continuous p.1 q.2)]
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
      (μ := (q.2 : Measure X)) (ae_of_all _ fun x => (q.1 - p.1).norm_coe_le_norm x)
  rw [Real.dist_eq]
  calc
    |(∫ x, q.1 x ∂(q.2 : Measure X)) - ∫ x, p.1 x ∂(p.2 : Measure X)|
        ≤ |(∫ x, q.1 x ∂(q.2 : Measure X)) - ∫ x, p.1 x ∂(q.2 : Measure X)| +
          |(∫ x, p.1 x ∂(q.2 : Measure X)) - ∫ x, p.1 x ∂(p.2 : Measure X)| :=
      abs_sub_le _ _ _
    _ < ε := by linarith

theorem continuous_law_integral (u : P × X → ℝ) (hu : Continuous u) :
    Continuous (fun p : P × ProbabilityMeasure X =>
      ∫ x, u (p.1, x) ∂(p.2 : Measure X)) := by
  let f : P → C(X, ℝ) := fun z => ⟨fun x => u (z, x),
    hu.comp (continuous_const.prodMk continuous_id)⟩
  have hf : Continuous f := ContinuousMap.continuous_of_continuous_uncurry _ hu
  exact continuous_integral_pair.comp ((hf.comp continuous_fst).prodMk continuous_snd)
end Integral

section Carrier
variable {T A : Type*} [TopologicalSpace T] [MeasurableSpace T]
  [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A]
  [MetrizableSpace A] [BorelSpace A] [Nonempty A]

abbrev Law (μ : Measure T) := ↥(fixedFstMarginal (A := A) μ)

instance lawCompact (μ : Measure T) [IsProbabilityMeasure μ] :
    CompactSpace (Law (A := A) μ) :=
  isCompact_iff_compactSpace.mp (isCompact_fixedFstMarginal μ)

instance lawNonempty (μ : Measure T) [IsProbabilityMeasure μ] :
    Nonempty (Law (A := A) μ) := (nonempty_fixedFstMarginal μ).to_subtype

omit [TopologicalSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace A] [CompactSpace A] [MetrizableSpace A] [BorelSpace A] [Nonempty A] in

theorem law_mix (μ : Measure T) [IsProbabilityMeasure μ]
    (π τ : Law (A := A) μ) (a b : ℝ≥0∞) (hab : a + b = 1) :
    ∃ ξ : Law (A := A) μ,
      (ξ.1 : Measure (T × A)) = a • (π.1 : Measure (T × A)) + b • (τ.1 : Measure (T × A)) := by
  let ν := a • (π.1 : Measure (T × A)) + b • (τ.1 : Measure (T × A))
  haveI : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact hab⟩
  refine ⟨⟨⟨ν, inferInstance⟩, ?_⟩, rfl⟩
  change ν.map Prod.fst = μ
  dsimp [ν]
  rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
    π.2, τ.2, ← add_smul, hab, one_smul]

abbrev Dual (T A : Type*) [TopologicalSpace T] [TopologicalSpace A] :=
  WeakDual ℝ ((T × A) →ᵇ ℝ)

def dualCarrier (μ : Measure T) : Set (Dual T A) :=
  ProbabilityMeasure.toWeakDualBCF '' fixedFstMarginal (A := A) μ

omit [CompactSpace T] [Nonempty A] in
theorem dualCarrier_compact (μ : Measure T) [IsProbabilityMeasure μ] :
    IsCompact (dualCarrier (A := A) μ) :=
  (isCompact_fixedFstMarginal μ).image ProbabilityMeasure.continuous_toWeakDualBCF

omit [CompactSpace T] [PolishSpace T] [Nonempty A] in
theorem dualCarrier_convex (μ : Measure T) [IsProbabilityMeasure μ] :
    Convex ℝ (dualCarrier (A := A) μ) := by
  apply ProbabilityMeasure.convex_image_toWeakDualBCF
  intro π τ hπ hτ a b hab
  obtain ⟨ξ, hξ⟩ := law_mix μ ⟨π, hπ⟩ ⟨τ, hτ⟩ a b hab
  exact ⟨ξ.1, ξ.2, hξ⟩

omit [CompactSpace T] [PolishSpace T] in
theorem dualCarrier_nonempty (μ : Measure T) [IsProbabilityMeasure μ] :
    (dualCarrier (A := A) μ).Nonempty :=
  (nonempty_fixedFstMarginal μ).image _

def lawHomeomorph (μ : Measure T) [IsProbabilityMeasure μ] :
    Law (A := A) μ ≃ₜ ↥(dualCarrier (A := A) μ) := by
  let e := Equiv.Set.imageOfInjOn
    (ProbabilityMeasure.toWeakDualBCF : ProbabilityMeasure (T × A) → Dual T A)
    (fixedFstMarginal μ) ProbabilityMeasure.toWeakDualBCF_injective.injOn
  have he : Continuous e :=
    Continuous.subtype_mk
      (ProbabilityMeasure.continuous_toWeakDualBCF.comp continuous_subtype_val) _
  exact he.homeoOfEquivCompactToT2

omit [CompactSpace T] [Nonempty A] in
@[simp] theorem lawHomeomorph_apply (μ : Measure T) [IsProbabilityMeasure μ]
    (π : Law (A := A) μ) :
    ((lawHomeomorph μ π : ↥(dualCarrier (A := A) μ)) : Dual T A) =
      ProbabilityMeasure.toWeakDualBCF π.1 := rfl

variable {μ : Measure T}

def IntegralOptimal (π : Law (A := A) μ) (f : T × A → ℝ) : Prop :=
  ∀ τ : Law (A := A) μ, (∫ x, f x ∂(τ.1 : Measure (T × A))) ≤
    ∫ x, f x ∂(π.1 : Measure (T × A))

def AllActionOptimal (π : Law (A := A) μ) (f : T × A → ℝ) : Prop :=
  ∀ᵐ x ∂(π.1 : Measure (T × A)), ∀ a : A, f (x.1, a) ≤ f x

omit [Nonempty A] [PolishSpace T] in

private theorem optimal_one_action (μ : Measure T) [IsProbabilityMeasure μ]
    (π : Law (A := A) μ) (f : C(T × A, ℝ)) (hmax : IntegralOptimal π f) (a : A) :
    ∀ᵐ x ∂(π.1 : Measure (T × A)), f (x.1, a) ≤ f x := by
  classical
  let g : C(T × A, ℝ) := ⟨fun x => max 0 (f (x.1, a) - f x),
    continuous_const.max ((f.continuous.comp (continuous_fst.prodMk continuous_const)).sub
      f.continuous)⟩
  let R : T × A → T × A := fun x => if f x < f (x.1, a) then (x.1, a) else x
  have hR : Measurable R :=
    Measurable.ite (isOpen_lt f.continuous
      (f.continuous.comp (continuous_fst.prodMk continuous_const))).measurableSet
      (measurable_fst.prodMk measurable_const) measurable_id
  let τ₀ := π.1.map hR.aemeasurable
  have hτ : τ₀ ∈ fixedFstMarginal μ := by
    change ((π.1 : Measure (T × A)).map R).map Prod.fst = μ
    rw [Measure.map_map measurable_fst hR]
    have he : Prod.fst ∘ R = Prod.fst := by
      funext x
      dsimp [R]
      split <;> rfl
    rw [he]
    exact π.2
  have he : ∀ x, f (R x) = f x + g x := by
    intro x
    dsimp [R, g]
    split_ifs with h
    · rw [max_eq_right (by linarith)]
      ring
    · rw [max_eq_left (by linarith)]
      ring
  have hi := hmax ⟨τ₀, hτ⟩
  change (∫ x, f x ∂((π.1 : Measure (T × A)).map R)) ≤ _ at hi
  rw [integral_map hR.aemeasurable f.continuous.aestronglyMeasurable] at hi
  simp_rw [he] at hi
  rw [integral_add (integrable_continuous f π.1) (integrable_continuous g π.1)] at hi
  have hgint : (∫ x, g x ∂(π.1 : Measure (T × A))) = 0 :=
    le_antisymm (by linarith) (integral_nonneg fun x => le_max_left _ _)
  have hgzero : ∀ᵐ x ∂(π.1 : Measure (T × A)), g x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => le_max_left _ _)
      (integrable_continuous g π.1)).mp hgint
  filter_upwards [hgzero] with x hx
  have h := le_max_right (0 : ℝ) (f (x.1, a) - f x)
  change max 0 (f (x.1, a) - f x) = 0 at hx
  linarith

omit [Nonempty A] [PolishSpace T] in

theorem allAction_of_integralOptimal (μ : Measure T) [IsProbabilityMeasure μ]
    (π : Law (A := A) μ) (f : T × A → ℝ) (hf : Continuous f)
    (hmax : IntegralOptimal π f) : AllActionOptimal π f := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense A
  have hone : ∀ a ∈ D, ∀ᵐ x ∂(π.1 : Measure (T × A)), f (x.1, a) ≤ f x :=
    fun a _ => optimal_one_action μ π ⟨f, hf⟩ hmax a
  have hall := (ae_ball_iff hDc).mpr hone
  filter_upwards [hall] with x hx
  have hclosed : IsClosed {a : A | f (x.1, a) ≤ f x} :=
    isClosed_le (hf.comp (continuous_const.prodMk continuous_id)) continuous_const
  have hsub : closure D ⊆ {a : A | f (x.1, a) ≤ f x} :=
    closure_minimal (fun a ha => hx a ha) hclosed
  intro a
  exact hsub (hDd.closure_eq ▸ mem_univ a)

theorem disintegrate_allAction (μ : Measure T) [IsProbabilityMeasure μ]
    [StandardBorelSpace A] (π : Law (A := A) μ) (f : T × A → ℝ)
    (hf : Continuous f) (hπ : AllActionOptimal π f) :
    ∃ σ : Kernel T A, IsMarkovKernel σ ∧ μ ⊗ₘ σ = (π.1 : Measure (T × A)) ∧
      (∀ᵐ t ∂μ, ∀ᵐ a ∂σ t, ∀ a' : A, f (t, a') ≤ f (t, a)) := by
  let σ := (π.1 : Measure (T × A)).condKernel
  have hmarg : (π.1 : Measure (T × A)).fst = μ := π.2
  have hdis : μ ⊗ₘ σ = (π.1 : Measure (T × A)) := by
    calc
      μ ⊗ₘ σ = (π.1 : Measure (T × A)).fst ⊗ₘ σ := congrArg (fun ν : Measure T => ν ⊗ₘ σ) hmarg.symm
      _ = (π.1 : Measure (T × A)) := Measure.disintegrate _ _
  refine ⟨σ, inferInstance, hdis, ?_⟩
  have hmeas : MeasurableSet {x : T × A | ∀ a' : A, f (x.1, a') ≤ f x} := by
    have he : {x : T × A | ∀ a' : A, f (x.1, a') ≤ f x} =
        ⋂ a' : A, {x | f (x.1, a') ≤ f x} := by ext x; simp
    rw [he]
    exact (isClosed_iInter fun a' =>
      isClosed_le (hf.comp (continuous_fst.prodMk continuous_const)) hf).measurableSet
  unfold AllActionOptimal at hπ
  rw [← hdis] at hπ
  exact (Measure.ae_compProd_iff hmeas).mp hπ
end Carrier

section Populations
variable {ι : Type*}
  (T A : ι → Type*)
  [∀ i, TopologicalSpace (T i)] [∀ i, MeasurableSpace (T i)]
  [∀ i, CompactSpace (T i)] [∀ i, PolishSpace (T i)] [∀ i, BorelSpace (T i)]
  [∀ i, TopologicalSpace (A i)] [∀ i, MeasurableSpace (A i)]
  [∀ i, CompactSpace (A i)] [∀ i, MetrizableSpace (A i)]
  [∀ i, BorelSpace (A i)] [∀ i, Nonempty (A i)]
  (μ : ∀ i, Measure (T i)) [∀ i, IsProbabilityMeasure (μ i)]

abbrev Profile := ∀ i, Law (A := A i) (μ i)

theorem exists_population_integral_law
    (u : ∀ i, Profile T A μ × (T i × A i) → ℝ)
    (hu : ∀ i, Continuous (u i)) :
    ∃ π : Profile T A μ, ∀ i, IntegralOptimal (π i) (fun x => u i (π, x)) := by
  classical
  let K : ∀ i, Set (Dual (T i) (A i)) := fun i => dualCarrier (μ i)
  let e : ∀ i, Law (A := A i) (μ i) ≃ₜ ↥(K i) := fun i => lawHomeomorph (μ i)
  let KK : Set (∀ i, Dual (T i) (A i)) := Set.pi univ K
  have hKcp : ∀ i, IsCompact (K i) := fun i => dualCarrier_compact (μ i)
  have hKcv : ∀ i, Convex ℝ (K i) := fun i => dualCarrier_convex (μ i)
  have hKne : ∀ i, (K i).Nonempty := fun i => dualCarrier_nonempty (μ i)
  have hKKcp : IsCompact KK := isCompact_univ_pi hKcp
  have hKKcv : Convex ℝ KK := convex_pi fun i _ => hKcv i
  have hKKne : KK.Nonempty :=
    ⟨fun i => (hKne i).choose, fun i _ => (hKne i).choose_spec⟩
  let prof : KK → Profile T A μ := fun x i => (e i).symm ⟨x.1 i, x.2 i (mem_univ i)⟩
  have hprof : Continuous prof := continuous_pi fun i =>
    (e i).symm.continuous.comp
      (Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _)
  let obj : ∀ i, KK → K i → ℝ := fun i x y =>
    ∫ z, u i (prof x, z) ∂(((e i).symm y).1 : Measure (T i × A i))
  have hobj : ∀ i, Continuous (fun p : KK × K i => obj i p.1 p.2) := by
    intro i
    exact (continuous_law_integral (u i) (hu i)).comp
      ((hprof.comp continuous_fst).prodMk
        (continuous_subtype_val.comp ((e i).symm.continuous.comp continuous_snd)))
  let B : ∀ i, KK → Set (K i) := fun i x => {y | ∀ z : K i, obj i x z ≤ obj i x y}
  have hBne : ∀ i x, (B i x).Nonempty := by
    intro i x
    letI : CompactSpace (K i) := isCompact_iff_compactSpace.mp (hKcp i)
    letI : Nonempty (K i) := (hKne i).to_subtype
    obtain ⟨y, _, hy⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
      ((hobj i).comp (continuous_const.prodMk continuous_id)).continuousOn
    exact ⟨y, fun z => hy (mem_univ z)⟩
  have hBcg : ∀ i, IsClosedGraph (B i) := by
    intro i
    change IsClosed {p : KK × K i | ∀ z : K i, obj i p.1 z ≤ obj i p.1 p.2}
    have he : {p : KK × K i | ∀ z : K i, obj i p.1 z ≤ obj i p.1 p.2} =
        ⋂ z : K i, {p | obj i p.1 z ≤ obj i p.1 p.2} := by ext p; simp
    rw [he]
    exact isClosed_iInter fun z => isClosed_le
      ((hobj i).comp (continuous_fst.prodMk continuous_const)) (hobj i)
  let BA : ∀ i, KK → Set (Dual (T i) (A i)) :=
    fun i x => Subtype.val '' B i x
  have hBAcg : ∀ i, IsClosedGraph (BA i) := fun i =>
    (hBcg i).image_subtypeVal (hKcp i).isClosed
  have hBAcv : ∀ i x, Convex ℝ (BA i x) := by
    intro i x y hy z hz a b ha hb hab
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := hz
    let π := (e i).symm y'
    let τ := (e i).symm z'
    obtain ⟨ξ, hξ⟩ := law_mix (μ i) π τ (ENNReal.ofReal a) (ENNReal.ofReal b)
      (by rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one])
    have hdual : ((e i ξ : K i) : Dual (T i) (A i)) = a • y'.1 + b • z'.1 := by
      apply ContinuousLinearMap.ext
      intro f
      change (∫ w, f w ∂(ξ.1 : Measure (T i × A i))) = _
      rw [hξ, integral_add_measure
        ((f.integrable (π.1 : Measure _)).smul_measure (by simp))
        ((f.integrable (τ.1 : Measure _)).smul_measure (by simp)),
        integral_smul_measure, integral_smul_measure,
        ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
      have hπ : ProbabilityMeasure.toWeakDualBCF π.1 = y'.1 :=
        congrArg Subtype.val ((e i).apply_symm_apply y')
      have hτ : ProbabilityMeasure.toWeakDualBCF τ.1 = z'.1 :=
        congrArg Subtype.val ((e i).apply_symm_apply z')
      change a • ProbabilityMeasure.toWeakDualBCF π.1 f +
        b • ProbabilityMeasure.toWeakDualBCF τ.1 f = _
      rw [hπ, hτ]
      rfl
    refine ⟨e i ξ, ?_, hdual⟩
    intro w
    have hf : Continuous (fun z : T i × A i => u i (prof x, z)) :=
      (hu i).comp (continuous_const.prodMk continuous_id)
    let f : C(T i × A i, ℝ) := ⟨_, hf⟩
    have heq : obj i x (e i ξ) = a * obj i x y' + b * obj i x z' := by
      dsimp [obj]
      rw [(e i).symm_apply_apply, hξ]
      change (∫ z, f z ∂(ENNReal.ofReal a • (π.1 : Measure _) +
        ENNReal.ofReal b • (τ.1 : Measure _))) = _
      rw [integral_add_measure
        ((integrable_continuous f π.1).smul_measure (c := ENNReal.ofReal a) (by simp))
        ((integrable_continuous f τ.1).smul_measure (c := ENNReal.ofReal b) (by simp)),
        integral_smul_measure, integral_smul_measure,
        ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
      rfl
    rw [heq]
    have h₁ := mul_le_mul_of_nonneg_left (hy' w) ha
    have h₂ := mul_le_mul_of_nonneg_left (hz' w) hb
    calc
      obj i x w = a * obj i x w + b * obj i x w := by rw [← add_mul, hab, one_mul]
      _ ≤ a * obj i x y' + b * obj i x z' := add_le_add h₁ h₂
  let Φ : KK → Set (∀ i, Dual (T i) (A i)) :=
    fun x => Set.pi univ (fun i => BA i x)
  have hΦcg : IsClosedGraph Φ := by
    change IsClosed {p : KK × (∀ i, Dual (T i) (A i)) | p.2 ∈ Φ p.1}
    have he : {p : KK × (∀ i, Dual (T i) (A i)) | p.2 ∈ Φ p.1} =
        ⋂ i, (fun p : KK × (∀ i, Dual (T i) (A i)) => (p.1, p.2 i)) ⁻¹'
          {q : KK × Dual (T i) (A i) | q.2 ∈ BA i q.1} := by
      ext p
      simp [Φ, Set.mem_pi]
    rw [he]
    refine isClosed_iInter fun i => ?_
    have hc : IsClosed {q : KK × Dual (T i) (A i) | q.2 ∈ BA i q.1} := hBAcg i
    exact hc.preimage (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hΦprop : ∀ x, Φ x ⊆ KK ∧ Convex ℝ (Φ x) ∧ (Φ x).Nonempty := by
    intro x
    refine ⟨?_, convex_pi (fun i _ => hBAcv i x), ?_⟩
    · intro y hy i _
      obtain ⟨z, _, hz⟩ := hy i (mem_univ i)
      exact hz ▸ z.2
    · exact ⟨fun i => ((hBne i x).choose : Dual (T i) (A i)),
        fun i _ => ⟨(hBne i x).choose, (hBne i x).choose_spec, rfl⟩⟩
  obtain ⟨x, hx⟩ := fanGlicksbergFixedPoint KK hKKcp hKKcv hKKne Φ hΦcg hΦprop
  refine ⟨prof x, ?_⟩
  intro i τ
  obtain ⟨y, hy, he⟩ := hx i (mem_univ i)
  have hyx : y = (⟨x.1 i, x.2 i (mem_univ i)⟩ : K i) := Subtype.ext he
  have hi := hy (e i τ)
  simpa only [obj, hyx, Homeomorph.symm_apply_apply, prof] using hi

theorem exists_population_laws [∀ i, StandardBorelSpace (A i)]
    (u : ∀ i, Profile T A μ × (T i × A i) → ℝ) (hu : ∀ i, Continuous (u i)) :
    ∃ (π : Profile T A μ) (σ : ∀ i, Kernel (T i) (A i)),
      (∀ i, IsMarkovKernel (σ i)) ∧
      (∀ i, μ i ⊗ₘ σ i = ((π i).1 : Measure (T i × A i))) ∧
      (∀ i, AllActionOptimal (π i) (fun z => u i (π, z))) ∧
      (∀ i, ∀ᵐ t ∂μ i, ∀ᵐ a ∂σ i t, ∀ a' : A i,
        u i (π, (t, a')) ≤ u i (π, (t, a))) := by
  obtain ⟨π, hπ⟩ := exists_population_integral_law T A μ u hu
  have hc : ∀ i, Continuous (fun z => u i (π, z)) :=
    fun i => (hu i).comp (continuous_const.prodMk continuous_id)
  have ha : ∀ i, AllActionOptimal (π i) (fun z => u i (π, z)) :=
    fun i => allAction_of_integralOptimal (μ i) (π i) _ (hc i) (hπ i)
  choose σ hmark hdis hopt using fun i =>
    disintegrate_allAction (μ i) (π i) _ (hc i) (ha i)
  exact ⟨π, σ, hmark, hdis, ha, hopt⟩
end Populations

section Symmetric
variable {T A : Type*} [TopologicalSpace T] [MeasurableSpace T]
  [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A]
  [MetrizableSpace A] [BorelSpace A] [Nonempty A] [StandardBorelSpace A]

theorem exists_symmetric_law (μ : Measure T) [IsProbabilityMeasure μ]
    (u : Law (A := A) μ × (T × A) → ℝ) (hu : Continuous u) :
    ∃ (π : Law (A := A) μ) (σ : Kernel T A), IsMarkovKernel σ ∧
      μ ⊗ₘ σ = (π.1 : Measure (T × A)) ∧
      AllActionOptimal π (fun z => u (π, z)) ∧
      (∀ᵐ t ∂μ, ∀ᵐ a ∂σ t, ∀ a' : A, u (π, (t, a')) ≤ u (π, (t, a))) := by
  let v : Unit → ((Unit → Law (A := A) μ) × (T × A)) → ℝ :=
    fun _ p => u (p.1 (), p.2)
  have hv : ∀ i, Continuous (v i) := fun _ =>
    hu.comp (((continuous_apply ()).comp continuous_fst).prodMk continuous_snd)
  obtain ⟨π, σ, hmark, hdis, hopt, hall⟩ :=
    exists_population_laws (fun _ : Unit => T) (fun _ => A) (fun _ => μ) v hv
  exact ⟨π (), σ (), hmark (), hdis (),
    hopt (), hall ()⟩
end Symmetric

end FCAppendix.Existence.Distributional
