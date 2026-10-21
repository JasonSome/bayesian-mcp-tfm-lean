import FCAppendix.Affine.Tail04.EqualPrivateSignal

noncomputable section
namespace FCAppendix.Affine.Tail04.FrontierPushforward
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateFrontier EqualPrivateContinuity
open scoped BigOperators

variable {ι T S A : Type*} [Fintype ι]
  [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace S] [MeasurableSpace S] [CompactSpace S] [PolishSpace S] [BorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A] [MetrizableSpace A]
  [BorelSpace A] [Nonempty A] [Fintype A]
  (μ : Measure T) [IsProbabilityMeasure μ] (f : T→ S) (hf : Continuous f)

private abbrev map_probability : IsProbabilityMeasure (μ.map f) :=
  Measure.isProbabilityMeasure_map hf.measurable.aemeasurable

def planMap (π : Plan (A:=A) μ) : Plan (A:=A) (μ.map f) :=
  ⟨π.1.map (hf.measurable.prodMap measurable_id).aemeasurable,by
    change (((π.1 : Measure (T×A)).map (Prod.map f id)).map Prod.fst)=μ.map f
    rw [Measure.map_map measurable_fst (hf.measurable.prodMap measurable_id)]
    change (π.1 : Measure (T×A)).map (f ∘ Prod.fst)=_
    rw [←Measure.map_map hf.measurable measurable_fst,π.2]⟩

omit [Fintype ι] [CompactSpace T] [PolishSpace T] [CompactSpace S]
  [PolishSpace S] [CompactSpace A] [Nonempty A] [IsProbabilityMeasure μ] in
lemma marginal_planMap (x : ι→ C(T×A,ℝ)) (y : ι→ C(S×A,ℝ))
    (hxy : ∀ i t a,y i (f t,a)=x i (t,a)) (π : Plan (A:=A) μ) :
    marginal y (planMap μ f hf π)=marginal x π := by
  funext i
  change (∫ z,y i z ∂((π.1 : Measure (T×A)).map (Prod.map f id)))=
    ∫ z,x i z ∂(π.1 : Measure (T×A))
  rw [integral_map (hf.measurable.prodMap measurable_id).aemeasurable
    (y i).continuous.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun z => hxy i z.1 z.2)

omit [MeasurableSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [MeasurableSpace S] [CompactSpace S] [PolishSpace S] [BorelSpace S]
  [MeasurableSpace A] [CompactSpace A] [MetrizableSpace A] [BorelSpace A]
  [Nonempty A] [Fintype A] in
lemma score_map (x : ι→ C(T×A,ℝ)) (r : C(T×A,ℝ))
    (y : ι→ C(S×A,ℝ)) (s : C(S×A,ℝ))
    (hxy : ∀ i t a,y i (f t,a)=x i (t,a)) (hrs : ∀ t a,s (f t,a)=r (t,a))
    (b q : ι→ℝ) (ξ : ℝ) (t : T) (a : A) :
    score y s b q ξ (f t,a)=score x r b q ξ (t,a) := by
  simp only [score,ContinuousMap.add_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul,hxy,hrs]

omit [CompactSpace T] [PolishSpace T] [CompactSpace S] [PolishSpace S]
  [CompactSpace A] [Nonempty A] [IsProbabilityMeasure μ] in
theorem allAction_planMap (x : ι→ C(T×A,ℝ)) (r : C(T×A,ℝ))
    (y : ι→ C(S×A,ℝ)) (s : C(S×A,ℝ))
    (hxy : ∀ i t a,y i (f t,a)=x i (t,a)) (hrs : ∀ t a,s (f t,a)=r (t,a))
    (b : ι→ℝ) (ξ : ℝ) (π : Plan (A:=A) μ)
    (hπ : AllActionOptimal π (score x r b (marginal x π) ξ)) :
    AllActionOptimal (planMap μ f hf π)
      (score y s b (marginal y (planMap μ f hf π)) ξ) := by
  rw [marginal_planMap μ f hf x y hxy π]
  let u := score y s b (marginal x π) ξ
  have hset : MeasurableSet {z : S×A | ∀ a,u (z.1,a)≤ u z} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun a => measurableSet_le
      (u.continuous.measurable.comp (measurable_fst.prodMk measurable_const))
        u.continuous.measurable)
  change ∀ᵐ z ∂((π.1 : Measure (T×A)).map (Prod.map f id)),∀ a,u (z.1,a)≤ u z
  apply (ae_map_iff (hf.measurable.prodMap measurable_id).aemeasurable hset).mpr
  filter_upwards [hπ] with z hz
  intro a
  change score y s b (marginal x π) ξ (f z.1,a) ≤
    score y s b (marginal x π) ξ (f z.1,z.2)
  rw [score_map f x r y s hxy hrs,score_map f x r y s hxy hrs]
  exact hz a

omit [PolishSpace T] [PolishSpace S] in
theorem integralOptimal_planMap (x : ι→ C(T×A,ℝ)) (r : C(T×A,ℝ))
    (y : ι→ C(S×A,ℝ)) (s : C(S×A,ℝ))
    (hxy : ∀ i t a,y i (f t,a)=x i (t,a)) (hrs : ∀ t a,s (f t,a)=r (t,a))
    (b : ι→ℝ) (ξ : ℝ) (π : Plan (A:=A) μ)
    (hπ : IntegralOptimal π (score x r b (marginal x π) ξ)) :
    IntegralOptimal (planMap μ f hf π)
      (score y s b (marginal y (planMap μ f hf π)) ξ) := by
  letI : IsProbabilityMeasure (μ.map f) := map_probability μ f hf
  have hall := allAction_planMap μ f hf x r y s hxy hrs b ξ π
    (allAction_of_integralOptimal μ π _ (score x r b (marginal x π) ξ).continuous hπ)
  exact integralOptimal_of_gap_eq_zero y s b ξ (μ.map f) (planMap μ f hf π)
    (gap_eq_zero_of_allAction y s b ξ (μ.map f) (planMap μ f hf π) hall)

include hf in
omit [PolishSpace T] [PolishSpace S] in
theorem mean_eq (x : ι→ C(T×A,ℝ)) (r : C(T×A,ℝ))
    (y : ι→ C(S×A,ℝ)) (s : C(S×A,ℝ))
    (hxy : ∀ i t a,y i (f t,a)=x i (t,a)) (hrs : ∀ t a,s (f t,a)=r (t,a))
    (b : ι→ℝ) (ξ : ℝ) (hξ : 0< ξ) (hb : ∀ i,0< b i)
    (π : Plan (A:=A) μ) (τ : Plan (A:=A) (μ.map f))
    (hπ : IntegralOptimal π (score x r b (marginal x π) ξ))
    (hτ : IntegralOptimal τ (score y s b (marginal y τ) ξ)) :
    marginal x π=marginal y τ := by
  letI : IsProbabilityMeasure (μ.map f) := map_probability μ f hf
  rw [←marginal_planMap μ f hf x y hxy π]
  exact marginal_unique (μ.map f) y s b ξ hξ hb (planMap μ f hf π) τ
    (integralOptimal_planMap μ f hf x r y s hxy hrs b ξ π hπ) hτ

end FCAppendix.Affine.Tail04.FrontierPushforward
