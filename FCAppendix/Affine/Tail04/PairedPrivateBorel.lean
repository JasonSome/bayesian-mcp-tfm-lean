import FCAppendix.Affine.Tail04.PairedPrivatePotential
import FCAppendix.Affine.Tail04.EqualPrivateMeasurable
import FCAppendix.Affine.Tail04.BorelPlanRealizer

noncomputable section
namespace FCAppendix.Affine.Tail04.PairedPrivateBorel
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateFrontier EqualPrivateContinuity PairedPrivatePotential

variable {ι T0 T1 A0 A1 : Type*} [Fintype ι]
  [TopologicalSpace T0] [MeasurableSpace T0] [CompactSpace T0] [PolishSpace T0]
    [BorelSpace T0] [Nonempty T0]
  [TopologicalSpace T1] [MeasurableSpace T1] [CompactSpace T1] [PolishSpace T1]
    [BorelSpace T1] [Nonempty T1]
  [TopologicalSpace A0] [MeasurableSpace A0] [CompactSpace A0] [MetrizableSpace A0]
    [BorelSpace A0] [Nonempty A0] [StandardBorelSpace A0] [Fintype A0]
  [TopologicalSpace A1] [MeasurableSpace A1] [CompactSpace A1] [MetrizableSpace A1]
    [BorelSpace A1] [Nonempty A1] [StandardBorelSpace A1] [Fintype A1]

abbrev Parameters := (ι → ℝ) × (WeakProbability.Law T0 × WeakProbability.Law T1)
abbrev Output := WeakProbability.Law (T0×A0) × WeakProbability.Law (T1×A1)

variable (x0 : ι → C(T0×A0,ℝ)) (x1 : ι → C(T1×A1,ℝ))
  (r0 : C(T0×A0,ℝ)) (r1 : C(T1×A1,ℝ)) (ξ : ℝ)

def effective {T A : Type*} [MeasurableSpace T] [MeasurableSpace A]
    [TopologicalSpace T] [TopologicalSpace A]
    (x : ι → C(T×A,ℝ)) (ξ : ℝ) (b : ι → ℝ) (π : ProbabilityMeasure (T×A)) : ι → ℝ :=
  fun i => b i*(1-ξ*ambientMarginal x π i)

lemma score_effective {T A : Type*} [MeasurableSpace T] [MeasurableSpace A]
    [TopologicalSpace T] [TopologicalSpace A]
    (x : ι → C(T×A,ℝ)) (r : C(T×A,ℝ)) (b q q' : ι → ℝ) (ξ : ℝ) :
    score x r (fun i => b i*(1-ξ*q i)) q' 0=score x r b q ξ := by
  ext z
  simp only [score,ContinuousMap.add_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul,zero_mul,sub_zero,mul_one]

omit [Fintype ι] in
lemma continuous_effective {T A : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
    [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A] [MetrizableSpace A]
    [BorelSpace A] [Nonempty A] [StandardBorelSpace A] [Fintype A]
    (x : ι → C(T×A,ℝ)) (ξ : ℝ) :
    Continuous (fun p : (ι → ℝ) × ProbabilityMeasure (T×A) => effective x ξ p.1 p.2) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp continuous_fst).mul
    (continuous_const.sub (continuous_const.mul
      ((continuous_apply i).comp ((continuous_ambientMarginal x).comp continuous_snd))))

def graph : Set ((Parameters (ι:=ι) (T0:=T0) (T1:=T1)) ×
    Output (T0:=T0) (T1:=T1) (A0:=A0) (A1:=A1)) :=
  {z | firstMarginal z.2.1.val=z.1.2.1.val ∧ firstMarginal z.2.2.val=z.1.2.2.val ∧
    gap x0 r0 0 (effective x1 ξ z.1.1 z.2.2.val,z.2.1.val)=0 ∧
    gap x1 r1 0 (effective x0 ξ z.1.1 z.2.1.val,z.2.2.val)=0}

omit [Nonempty T0] [Nonempty T1] in
lemma isClosed_graph : IsClosed (graph x0 x1 r0 r1 ξ) := by
  let Z := Parameters (ι:=ι) (T0:=T0) (T1:=T1) ×
    Output (T0:=T0) (T1:=T1) (A0:=A0) (A1:=A1)
  have hb : Continuous (fun z : Z => z.1.1) := continuous_fst.comp continuous_fst
  have h0 : Continuous (fun z : Z => z.2.1.val) :=
    WeakProbability.continuous_val.comp (continuous_fst.comp continuous_snd)
  have h1 : Continuous (fun z : Z => z.2.2.val) :=
    WeakProbability.continuous_val.comp (continuous_snd.comp continuous_snd)
  have hg0 := (continuous_gap x0 r0 0).comp
    (((continuous_effective x1 ξ).comp (hb.prodMk h1)).prodMk h0)
  have hg1 := (continuous_gap x1 r1 0).comp
    (((continuous_effective x0 ξ).comp (hb.prodMk h0)).prodMk h1)
  exact (isClosed_eq (continuous_firstMarginal.comp h0)
    (WeakProbability.continuous_val.comp
      (continuous_fst.comp (continuous_snd.comp continuous_fst)))).inter
    ((isClosed_eq (continuous_firstMarginal.comp h1)
      (WeakProbability.continuous_val.comp
        (continuous_snd.comp (continuous_snd.comp continuous_fst)))).inter
      ((isClosed_eq hg0 continuous_const).inter (isClosed_eq hg1 continuous_const)))

include T0 T1 A0 A1 x0 x1 r0 r1 ξ in
omit [Nonempty T0] [Nonempty T1] [StandardBorelSpace A0] [StandardBorelSpace A1] in
lemma graph_nonempty (p : Parameters (ι:=ι) (T0:=T0) (T1:=T1)) :
    ∃ z : Output (T0:=T0) (T1:=T1) (A0:=A0) (A1:=A1),(p,z)∈graph x0 x1 r0 r1 ξ := by
  obtain ⟨π0,π1,h0,h1,ha0,ha1⟩ := exists_paired_plans x0 x1 r0 r1 p.1 ξ
    (WeakProbability.toMeasure p.2.1) (WeakProbability.toMeasure p.2.2)
  refine ⟨(⟨π0.1⟩,⟨π1.1⟩),?_,?_,?_,?_⟩
  · apply ProbabilityMeasure.toMeasure_injective
    exact π0.2
  · apply ProbabilityMeasure.toMeasure_injective
    exact π1.2
  · apply gap_eq_zero_of_allAction x0 r0 _ 0 _ π0
    have he : score x0 r0 (effective x1 ξ p.1 π1.1) (marginal x0 π0) 0 =
        score x0 r0 p.1 (marginal x1 π1) ξ :=
      score_effective x0 r0 p.1 (marginal x1 π1) (marginal x0 π0) ξ
    rw [he]
    exact ha0
  · apply gap_eq_zero_of_allAction x1 r1 _ 0 _ π1
    have he : score x1 r1 (effective x0 ξ p.1 π0.1) (marginal x1 π1) 0 =
        score x1 r1 p.1 (marginal x0 π0) ξ :=
      score_effective x1 r1 p.1 (marginal x0 π0) (marginal x1 π1) ξ
    rw [he]
    exact ha1

include T0 T1 A0 A1 x0 x1 r0 r1 ξ in
theorem exists_measurable_pair :
    ∃ f : Parameters (ι:=ι) (T0:=T0) (T1:=T1) →
      Output (T0:=T0) (T1:=T1) (A0:=A0) (A1:=A1),
      Measurable f ∧ ∀ p,(p,f p)∈graph x0 x1 r0 r1 ξ :=
  CompactSelector.exists_measurable_selector (graph x0 x1 r0 r1 ξ)
    (isClosed_graph x0 x1 r0 r1 ξ) (graph_nonempty x0 x1 r0 r1 ξ)

def pairLaw : Parameters (ι:=ι) (T0:=T0) (T1:=T1) →
    Output (T0:=T0) (T1:=T1) (A0:=A0) (A1:=A1) :=
  (exists_measurable_pair x0 x1 r0 r1 ξ).choose
lemma measurable_pairLaw : Measurable (pairLaw x0 x1 r0 r1 ξ) :=
  (exists_measurable_pair x0 x1 r0 r1 ξ).choose_spec.1
include T0 T1 x0 x1 r0 r1 ξ in
lemma pairLaw_spec (p : Parameters (ι:=ι) (T0:=T0) (T1:=T1)) :
    (p,pairLaw x0 x1 r0 r1 ξ p)∈graph x0 x1 r0 r1 ξ :=
  (exists_measurable_pair x0 x1 r0 r1 ξ).choose_spec.2 p

def zeroUtility (z : Parameters (ι:=ι) (T0:=T0) (T1:=T1) × T0) (a : A0) : ℝ :=
  score x0 r0 z.1.1 (ambientMarginal x1 (pairLaw x0 x1 r0 r1 ξ z.1).2.val) ξ (z.2,a)

def oneUtility (z : Parameters (ι:=ι) (T0:=T0) (T1:=T1) × T1) (a : A1) : ℝ :=
  score x1 r1 z.1.1 (ambientMarginal x0 (pairLaw x0 x1 r0 r1 ξ z.1).1.val) ξ (z.2,a)

lemma measurable_zeroUtility : Measurable (Function.uncurry (zeroUtility x0 x1 r0 r1 ξ)) := by
  unfold Function.uncurry zeroUtility score
  simp only [ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  have hp : Measurable (fun z : (Parameters (ι:=ι) (T0:=T0) (T1:=T1) × T0) × A0 =>
      z.1.1) := measurable_fst.comp measurable_fst
  have hz : Measurable (fun z : (Parameters (ι:=ι) (T0:=T0) (T1:=T1) × T0) × A0 =>
      (z.1.2, z.2)) := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hq := ((continuous_ambientMarginal x1).comp WeakProbability.continuous_val).measurable.comp
    ((measurable_pairLaw x0 x1 r0 r1 ξ).snd.comp hp)
  apply (r0.continuous.measurable.comp hz).add
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_pi_apply i).comp (measurable_fst.comp hp)).mul
    (measurable_const.sub (measurable_const.mul ((measurable_pi_apply i).comp hq)))).mul
    ((x0 i).continuous.measurable.comp hz)

lemma measurable_oneUtility : Measurable (Function.uncurry (oneUtility x0 x1 r0 r1 ξ)) := by
  unfold Function.uncurry oneUtility score
  simp only [ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  have hp : Measurable (fun z : (Parameters (ι:=ι) (T0:=T0) (T1:=T1) × T1) × A1 =>
      z.1.1) := measurable_fst.comp measurable_fst
  have hz : Measurable (fun z : (Parameters (ι:=ι) (T0:=T0) (T1:=T1) × T1) × A1 =>
      (z.1.2, z.2)) := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hq := ((continuous_ambientMarginal x0).comp WeakProbability.continuous_val).measurable.comp
    ((measurable_pairLaw x0 x1 r0 r1 ξ).fst.comp hp)
  apply (r1.continuous.measurable.comp hz).add
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_pi_apply i).comp (measurable_fst.comp hp)).mul
    (measurable_const.sub (measurable_const.mul ((measurable_pi_apply i).comp hq)))).mul
    ((x1 i).continuous.measurable.comp hz)

include T0 T1 A0 x0 x1 r0 r1 ξ in
lemma zero_allAction (p : Parameters (ι:=ι) (T0:=T0) (T1:=T1)) :
    ∀ᵐ z ∂WeakProbability.toMeasure (pairLaw x0 x1 r0 r1 ξ p).1,
      ∀ a',zeroUtility x0 x1 r0 r1 ξ (p,z.1) a'≤ zeroUtility x0 x1 r0 r1 ξ (p,z.1) z.2 := by
  let Q := pairLaw x0 x1 r0 r1 ξ p
  have h := pairLaw_spec x0 x1 r0 r1 ξ p
  let π : Plan (A:=A0) (WeakProbability.toMeasure p.2.1) :=
    ⟨Q.1.val,congrArg (fun ν : ProbabilityMeasure T0 => (ν : Measure T0)) h.1⟩
  have ho := integralOptimal_of_gap_eq_zero x0 r0 (effective x1 ξ p.1 Q.2.val) 0
    (WeakProbability.toMeasure p.2.1) π h.2.2.1
  have ha := Existence.Distributional.allAction_of_integralOptimal
    (WeakProbability.toMeasure p.2.1) π _
    (score x0 r0 (effective x1 ξ p.1 Q.2.val) (marginal x0 π) 0).continuous ho
  have he : score x0 r0 (effective x1 ξ p.1 Q.2.val) (marginal x0 π) 0 =
      score x0 r0 p.1 (ambientMarginal x1 Q.2.val) ξ :=
    score_effective x0 r0 p.1 (ambientMarginal x1 Q.2.val) (marginal x0 π) ξ
  rw [he] at ha
  simpa only [Existence.Distributional.AllActionOptimal, zeroUtility,
    Q, π, WeakProbability.toMeasure, Prod.mk.eta] using ha

include T0 T1 A1 x0 x1 r0 r1 ξ in
lemma one_allAction (p : Parameters (ι:=ι) (T0:=T0) (T1:=T1)) :
    ∀ᵐ z ∂WeakProbability.toMeasure (pairLaw x0 x1 r0 r1 ξ p).2,
      ∀ a',oneUtility x0 x1 r0 r1 ξ (p,z.1) a'≤ oneUtility x0 x1 r0 r1 ξ (p,z.1) z.2 := by
  let Q := pairLaw x0 x1 r0 r1 ξ p
  have h := pairLaw_spec x0 x1 r0 r1 ξ p
  let π : Plan (A:=A1) (WeakProbability.toMeasure p.2.2) :=
    ⟨Q.2.val,congrArg (fun ν : ProbabilityMeasure T1 => (ν : Measure T1)) h.2.1⟩
  have ho := integralOptimal_of_gap_eq_zero x1 r1 (effective x0 ξ p.1 Q.1.val) 0
    (WeakProbability.toMeasure p.2.2) π h.2.2.2
  have ha := Existence.Distributional.allAction_of_integralOptimal
    (WeakProbability.toMeasure p.2.2) π _
    (score x1 r1 (effective x0 ξ p.1 Q.1.val) (marginal x1 π) 0).continuous ho
  have he : score x1 r1 (effective x0 ξ p.1 Q.1.val) (marginal x1 π) 0 =
      score x1 r1 p.1 (ambientMarginal x0 Q.1.val) ξ :=
    score_effective x1 r1 p.1 (ambientMarginal x0 Q.1.val) (marginal x1 π) ξ
  rw [he] at ha
  simpa only [Existence.Distributional.AllActionOptimal, oneUtility,
    Q, π, WeakProbability.toMeasure, Prod.mk.eta] using ha

include T0 T1 A0 A1 x0 x1 r0 r1 ξ in
theorem exists_pair_samplers :
    ∃ (f0 : (Parameters (ι:=ι) (T0:=T0) (T1:=T1) × T0) → unitInterval → A0)
      (f1 : (Parameters (ι:=ι) (T0:=T0) (T1:=T1) × T1) → unitInterval → A1),
      Measurable (Function.uncurry f0) ∧ Measurable (Function.uncurry f1) ∧
      (∀ p t s a,zeroUtility x0 x1 r0 r1 ξ (p,t) a≤ zeroUtility x0 x1 r0 r1 ξ (p,t) (f0 (p,t) s)) ∧
      (∀ p t s a,oneUtility x0 x1 r0 r1 ξ (p,t) a≤ oneUtility x0 x1 r0 r1 ξ (p,t) (f1 (p,t) s)) ∧
      (∀ p,((WeakProbability.toMeasure p.2.1).prod (volume : Measure unitInterval)).map
        (fun z : T0×unitInterval => (z.1,f0 (p,z.1) z.2))=
          WeakProbability.toMeasure (pairLaw x0 x1 r0 r1 ξ p).1) ∧
      (∀ p,((WeakProbability.toMeasure p.2.2).prod (volume : Measure unitInterval)).map
        (fun z : T1×unitInterval => (z.1,f1 (p,z.1) z.2))=
          WeakProbability.toMeasure (pairLaw x0 x1 r0 r1 ξ p).2) := by
  have hf0 := (measurable_pairLaw x0 x1 r0 r1 ξ).fst
  have hf1 := (measurable_pairLaw x0 x1 r0 r1 ξ).snd
  have hm0 (p : Parameters (ι:=ι) (T0:=T0) (T1:=T1)) :
      ((pairLaw x0 x1 r0 r1 ξ p).1.val : Measure (T0×A0)).map Prod.fst=
        WeakProbability.toMeasure p.2.1 :=
    congrArg (fun ν : ProbabilityMeasure T0 => (ν : Measure T0)) (pairLaw_spec x0 x1 r0 r1 ξ p).1
  have hm1 (p : Parameters (ι:=ι) (T0:=T0) (T1:=T1)) :
      ((pairLaw x0 x1 r0 r1 ξ p).2.val : Measure (T1×A1)).map Prod.fst=
        WeakProbability.toMeasure p.2.2 :=
    congrArg (fun ν : ProbabilityMeasure T1 => (ν : Measure T1)) (pairLaw_spec x0 x1 r0 r1 ξ p).2.1
  obtain ⟨f0,h0,hlaw0,hbest0,hjoint0⟩ := BorelPlanRealizer.exists_sampler
    (fun p : Parameters (ι:=ι) (T0:=T0) (T1:=T1) => p.2.1)
    (fun p => (pairLaw x0 x1 r0 r1 ξ p).1) hf0
    (zeroUtility x0 x1 r0 r1 ξ) (measurable_zeroUtility x0 x1 r0 r1 ξ)
    hm0 (zero_allAction x0 x1 r0 r1 ξ)
  obtain ⟨f1,h1,hlaw1,hbest1,hjoint1⟩ := BorelPlanRealizer.exists_sampler
    (fun p : Parameters (ι:=ι) (T0:=T0) (T1:=T1) => p.2.2)
    (fun p => (pairLaw x0 x1 r0 r1 ξ p).2) hf1
    (oneUtility x0 x1 r0 r1 ξ) (measurable_oneUtility x0 x1 r0 r1 ξ)
    hm1 (one_allAction x0 x1 r0 r1 ξ)
  exact ⟨f0,f1,h0,h1,(fun p t s a => hbest0 (p,t) s a),
    (fun p t s a => hbest1 (p,t) s a),hjoint0,hjoint1⟩

end FCAppendix.Affine.Tail04.PairedPrivateBorel
