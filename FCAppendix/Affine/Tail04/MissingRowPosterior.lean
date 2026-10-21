import FCAppendix.Affine.Tail04.PrivateConditionalRows
import FCAppendix.Game.PosteriorExistence

noncomputable section
namespace FCAppendix.Affine.Tail04.MissingRowPosterior
open MeasureTheory ProbabilityTheory Set Classical Filter
open Hybrid PrivateConditionalRows EqualPrivateSignal EqualPrivateUpper
open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

def missing (o : Option ℝ) : Bool := if o=none then true else false

lemma measurable_missing : Measurable missing :=
  Measurable.ite (measurableSet_singleton none) measurable_const measurable_const

@[simp] lemma missing_eq_true (o : Option ℝ) : missing o=true ↔ o=none := by
  by_cases h : o=none <;> simp [missing,h]

def observation (obs : X → Option ℝ) (x : ι → X) : ι → Option ℝ := fun i => obs (x i)

omit [Fintype ι] in
lemma measurable_observation (obs : X → Option ℝ) (hobs : Measurable obs) :
    Measurable (observation (ι:=ι) obs) :=
  measurable_pi_lambda _ (fun i => hobs.comp (measurable_pi_apply i))

def patternEvent (k : ι → Bool) : Set (ι → Option ℝ) := {L | ∀ i,missing (L i)=k i}

lemma measurableSet_patternEvent (k : ι → Bool) : MeasurableSet (patternEvent k) := by
  simp only [patternEvent,Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
    (measurable_missing.comp (measurable_pi_apply i)) measurable_const)

omit [Fintype ι] [MeasurableSpace X] in
lemma pattern_preimage (obs : X → Option ℝ) (k : ι → Bool) :
    observation obs ⁻¹' patternEvent k=categoryFiber (missing ∘ obs) k := by
  ext x
  simp only [patternEvent,observation,categoryFiber,Set.mem_preimage,Set.mem_setOf_eq,
    Set.mem_univ_pi,Set.mem_singleton_iff,Function.comp_apply]

def visibleObservation (obs : X → Option ℝ) (k : ι → Bool)
    (x : {i : ι // k i≠true} → X) : ι → Option ℝ :=
  fun i => if h : k i=true then none else obs (x ⟨i,h⟩)

omit [Fintype ι] in
lemma measurable_visibleObservation (obs : X → Option ℝ) (hobs : Measurable obs)
    (k : ι → Bool) : Measurable (visibleObservation obs k) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases h : k i=true
  · simp [visibleObservation,h]
  · simpa [visibleObservation,h,Function.comp_def] using hobs.comp
      (measurable_pi_apply (⟨i,h⟩ : {i : ι // k i≠true}))

omit [Fintype ι] [MeasurableSpace X] in
lemma observation_eq_visible (obs : X → Option ℝ) (k : ι → Bool) (x : ι → X)
    (hx : x∈categoryFiber (missing ∘ obs) k) :
    observation obs x=visibleObservation obs k (fun i => x i) := by
  funext i
  have hi : missing (obs (x i))=k i := hx i (Set.mem_univ i)
  by_cases hk : k i=true
  · have ho : obs (x i)=none := (missing_eq_true _).mp (hi.trans hk)
    simp [observation,visibleObservation,hk,ho]
  · simp [observation,visibleObservation,hk]

variable (E : Observable.Regions)

def sortedMissingRow (_obs : X → Option ℝ) (k : ι → Bool) (H : ℕ)
    (e : Fin H ≃ {i : ι // k i=true})
    (f : X → Ici E.H ⊕ Icc E.R E.Rp) (x : ι → X) : Row H E.R E.Rp E.H :=
  PrivateRowSorting.sortRow E H (fun a => f (x (e a)))

omit [Fintype ι] in
lemma measurable_sortedMissingRow (obs : X → Option ℝ) (k : ι → Bool) (H : ℕ)
    (e : Fin H ≃ {i : ι // k i=true})
    (f : X → Ici E.H ⊕ Icc E.R E.Rp) (hf : Measurable f) :
    Measurable (sortedMissingRow E obs k H e f) :=
  (PrivateRowSorting.measurable_sortRow E H).comp
    (measurable_pi_lambda _ (fun a => hf.comp (measurable_pi_apply (e a).val)))

theorem conditional_missing_joint (μ : Measure X) [IsProbabilityMeasure μ]
    (obs : X → Option ℝ) (hobs : Measurable obs) (k : ι → Bool)
    (hmass : ∀ i,μ ((missing ∘ obs) ⁻¹' {k i})≠0)
    (H : ℕ) (e : Fin H ≃ {i : ι // k i=true})
    (f : X → Ici E.H ⊕ Icc E.R E.Rp) (hf : Measurable f)
    (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp))
    (hρ : (cond μ (obs ⁻¹' {none})).map f=(ρ : Measure _)) :
    (cond (Measure.pi (fun _ : ι => μ)) (categoryFiber (missing ∘ obs) k)).map
      (fun x => (observation obs x,sortedMissingRow E obs k H e f x))=
      ((cond (Measure.pi (fun _ : ι => μ)) (categoryFiber (missing ∘ obs) k)).map
        (observation obs)).prod (PrivateRowSorting.sortedOriginalIid E H ρ : Measure _) := by
  letI : DecidableEq Bool := Classical.decEq Bool
  let ν := cond (Measure.pi (fun _ : ι => μ)) (categoryFiber (missing ∘ obs) k)
  have ht : Measurable (missing ∘ obs) := measurable_missing.comp hobs
  have hsource : (missing ∘ obs) ⁻¹' {true}=obs ⁻¹' {none} := by ext x;simp
  have hprod := sorted_conditional_private_joint E μ (missing ∘ obs) ht k true hmass H e
    f hf ρ (by simpa only [hsource] using hρ)
    (visibleObservation obs k) (measurable_visibleObservation obs hobs k)
  have hshape : ∀ᵐ x ∂ν,x∈categoryFiber (missing ∘ obs) k := by
    unfold ν ProbabilityTheory.cond
    exact Measure.ae_smul_measure
      (ae_restrict_mem (measurableSet_categoryFiber (missing ∘ obs) ht k)) _
  have he : (fun x => (observation obs x,sortedMissingRow E obs k H e f x))=ᵐ[ν]
      (fun x => (visibleObservation obs k (fun i => x i),
        PrivateRowSorting.sortRow E H (fun a => f (x (e a))))) := by
    filter_upwards [hshape] with x hx
    rw [observation_eq_visible obs k x hx]
    rfl
  have hpair : ν.map (fun x => (observation obs x,sortedMissingRow E obs k H e f x))=
      ((Measure.pi (fun i : {i : ι // k i≠true} =>
        cond μ ((missing ∘ obs) ⁻¹' {k i}))).map (visibleObservation obs k)).prod
          (PrivateRowSorting.sortedOriginalIid E H ρ : Measure _) :=
    (Measure.map_congr he).trans hprod
  let τ := (Measure.pi (fun i : {i : ι // k i≠true} =>
    cond μ ((missing ∘ obs) ⁻¹' {k i}))).map (visibleObservation obs k)
  letI (i : {i : ι // k i≠true}) : IsProbabilityMeasure
      (cond μ ((missing ∘ obs) ⁻¹' {k i})) := cond_isProbabilityMeasure (hmass i)
  letI : IsProbabilityMeasure τ :=
    Measure.isProbabilityMeasure_map (measurable_visibleObservation obs hobs k).aemeasurable
  have hfst : ν.map (observation obs)=τ := by
    have hh := congrArg (fun q : Measure ((ι→ Option ℝ)×Row H E.R E.Rp E.H) => q.map Prod.fst) hpair
    rw [Measure.map_map measurable_fst
      ((measurable_observation obs hobs).prodMk (measurable_sortedMissingRow E obs k H e f hf))] at hh
    change ν.map (observation obs) =
      (τ.prod (PrivateRowSorting.sortedOriginalIid E H ρ : Measure (Row H E.R E.Rp E.H))).map
        Prod.fst at hh
    rw [(measurePreserving_fst (μ:=τ)
      (ν:=(PrivateRowSorting.sortedOriginalIid E H ρ : Measure (Row H E.R E.Rp E.H)))).map_eq] at hh
    exact hh
  rw [hfst]
  exact hpair

lemma mass_smul_cond (μ : Measure X) [IsFiniteMeasure μ] (S : Set X) (hS : μ S≠0) :
    μ S • cond μ S=μ.restrict S := by
  unfold ProbabilityTheory.cond
  rw [smul_smul,ENNReal.mul_inv_cancel hS (measure_ne_top μ S),one_smul]

theorem original_missing_posterior (μ : Measure X) [IsProbabilityMeasure μ]
    (obs : X → Option ℝ) (hobs : Measurable obs)
    (B : Kernel (ι→ Option ℝ) (ι→ X)) [IsMarkovKernel B]
    (hB : (Measure.pi (fun _ : ι => μ)).map
      (fun x => (observation obs x,x))=
        ((Measure.pi (fun _ : ι => μ)).map (observation obs)) ⊗ₘ B)
    (k : ι → Bool) (H : ℕ) (e : Fin H ≃ {i : ι // k i=true})
    (f : X → Ici E.H ⊕ Icc E.R E.Rp) (hf : Measurable f)
    (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp))
    (hρ : (cond μ (obs ⁻¹' {none})).map f=(ρ : Measure _)) :
    ∀ᵐ L ∂(Measure.pi (fun _ : ι => μ)).map (observation obs),
      L∈patternEvent k →
        (B L).map (sortedMissingRow E obs k H e f)=
          (PrivateRowSorting.sortedOriginalIid E H ρ : Measure _) := by
  letI : PolishSpace (Ici E.H) := isClosed_Ici.polishSpace
  letI : PolishSpace (Icc E.R E.Rp) := isClosed_Icc.polishSpace
  let τ := Measure.pi (fun _ : ι => μ)
  let T := categoryFiber (missing ∘ obs) k
  let S := patternEvent k
  have ht : Measurable (missing ∘ obs) := measurable_missing.comp hobs
  have hS : MeasurableSet S := measurableSet_patternEvent k
  have hT : MeasurableSet T := measurableSet_categoryFiber _ ht k
  have hpre : observation obs ⁻¹' S=T := pattern_preimage obs k
  by_cases hz : τ T=0
  · have hzero : (τ.map (observation obs)) S=0 := by
      rw [Measure.map_apply (measurable_observation obs hobs) hS,hpre,hz]
    have ha : ∀ᵐ L ∂τ.map (observation obs),L∉S := by
      exact measure_eq_zero_iff_ae_notMem.mp hzero
    filter_upwards [ha] with L hL
    exact fun h => (hL h).elim
  · have hmass : ∀ i,μ ((missing ∘ obs) ⁻¹' {k i})≠0 := by
      have hp : (∏ i,μ ((missing ∘ obs) ⁻¹' {k i}))≠0 := by
        simpa only [τ,T,categoryFiber_mass] using hz
      intro i
      exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
    have hj := conditional_missing_joint E μ obs hobs k hmass H e f hf ρ hρ
    have hr : Measurable (sortedMissingRow E obs k H e f) :=
      measurable_sortedMissingRow E obs k H e f hf
    have hpair := (measurable_observation obs hobs).prodMk hr
    have hrestrict : (τ.restrict (observation obs ⁻¹' S)).map
        (fun x => (observation obs x,sortedMissingRow E obs k H e f x))=
        ((τ.map (observation obs)).restrict S).prod
          (PrivateRowSorting.sortedOriginalIid E H ρ : Measure _) := by
      rw [hpre,←mass_smul_cond τ T hz,Measure.map_smul,hj,
        ←Measure.prod_smul_left,←Measure.map_smul,mass_smul_cond τ T hz,
        ←hpre,←Measure.restrict_map (measurable_observation obs hobs) hS]
    exact posterior_row_of_restricted_joint τ (observation obs)
      (measurable_observation obs hobs) B hB (sortedMissingRow E obs k H e f) hr
      (PrivateRowSorting.sortedOriginalIid E H ρ : Measure _) S hS hrestrict

theorem original_missing_posterior_all_patterns (μ : Measure X) [IsProbabilityMeasure μ]
    (obs : X → Option ℝ) (hobs : Measurable obs)
    (B : Kernel (ι→ Option ℝ) (ι→ X)) [IsMarkovKernel B]
    (hB : (Measure.pi (fun _ : ι => μ)).map
      (fun x => (observation obs x,x))=
        ((Measure.pi (fun _ : ι => μ)).map (observation obs)) ⊗ₘ B)
    (f : X → Ici E.H ⊕ Icc E.R E.Rp) (hf : Measurable f)
    (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp))
    (hρ : (cond μ (obs ⁻¹' {none})).map f=(ρ : Measure _))
    (H : (ι→ Bool) → ℕ) (e : ∀ k,Fin (H k) ≃ {i : ι // k i=true}) :
    ∀ᵐ L ∂(Measure.pi (fun _ : ι => μ)).map (observation obs),
      ∀ k,L∈patternEvent k →
        (B L).map (sortedMissingRow E obs k (H k) (e k) f)=
          (PrivateRowSorting.sortedOriginalIid E (H k) ρ : Measure _) := by
  exact ae_all_iff.mpr (fun k =>
    original_missing_posterior E μ obs hobs B hB k (H k) (e k) f hf ρ hρ)

end FCAppendix.Affine.Tail04.MissingRowPosterior
