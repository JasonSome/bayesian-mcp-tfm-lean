import FCAppendix.Affine.LowBody.NullHyperplanes
import FCAppendix.Affine.Hybrid.FavoredNoisyPayoff
import FCAppendix.Affine.Tail04.TopSelection

noncomputable section
namespace FCAppendix.Affine.Tail04.AllNoiseFiniteSelector
open MeasureTheory Set Filter Topology Classical
open scoped BigOperators

section FiniteComparison
variable {A X : Type*} [Fintype A] [Nonempty A] [TopologicalSpace X]

theorem select_eq_of_comparisons (f g : A → ℝ)
    (h : ∀ a b, f a ≤ f b ↔ g a ≤ g b) :
    FiniteSelector.select f=FiniteSelector.select g := by
  have hm : FiniteSelector.maxIndices f=FiniteSelector.maxIndices g := by
    ext k
    simp only [FiniteSelector.maxIndices,Finset.mem_filter,Finset.mem_univ,true_and]
    exact forall_congr' (fun a => h a ((Fintype.equivFin A).symm k))
  simp only [FiniteSelector.select,hm]

theorem select_eventually_eq (f : X → A → ℝ)
    (hf : ∀ a, Continuous (fun x => f x a)) (x : X)
    (htie : ∀ a b, f x a=f x b → ∀ y, f y a=f y b) :
    ∀ᶠ y in 𝓝 x, FiniteSelector.select (f y)=FiniteSelector.select (f x) := by
  have he (a b : A) : ∀ᶠ y in 𝓝 x, (f y a ≤ f y b ↔ f x a ≤ f x b) := by
    rcases lt_trichotomy (f x a) (f x b) with hab | hab | hab
    · have hlt : ∀ᶠ y in 𝓝 x,f y a<f y b := (isOpen_lt (hf a) (hf b)).mem_nhds hab
      exact hlt.mono (fun y hy => iff_of_true hy.le hab.le)
    · exact Eventually.of_forall (fun y => by rw [htie a b hab y,hab]; exact iff_of_true le_rfl le_rfl)
    · have hlt : ∀ᶠ y in 𝓝 x,f y b<f y a := (isOpen_lt (hf b) (hf a)).mem_nhds hab
      exact hlt.mono (fun y hy => iff_of_false (not_le.mpr hy) (not_le.mpr hab))
  have hall : ∀ᶠ y in 𝓝 x, ∀ a b, (f y a ≤ f y b ↔ f x a ≤ f x b) :=
    Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (he a))
  exact hall.mono (fun y hy => select_eq_of_comparisons (f y) (f x) hy)

end FiniteComparison

def score {N A : Type*} [Fintype N] (constant : A → ℝ) (coefficient : A → N → ℝ)
    (b : N → ℝ) (a : A) : ℝ := constant a+∑ i, coefficient a i*b i

theorem continuous_score {N A : Type*} [Fintype N]
    (constant : A → ℝ) (coefficient : A → N → ℝ) (a : A) :
    Continuous (fun b : N → ℝ => score constant coefficient b a) := by
  unfold score
  apply continuous_const.add
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))

def noisyBids {N : Type*} (eps : ℝ) (b : N → ℝ) (z : N → unitInterval) : N → ℝ :=
  fun i => b i*(1+eps*(z i:ℝ))

theorem continuous_noisyBids {N : Type*} (eps : ℝ) :
    Continuous (fun p : (N → ℝ) × (N → unitInterval) => noisyBids eps p.1 p.2) := by
  apply continuous_pi
  intro i
  unfold noisyBids
  fun_prop

theorem noisy_score_difference {N A : Type*} [Fintype N]
    (constant : A → ℝ) (coefficient : A → N → ℝ) (eps : ℝ)
    (b : N → ℝ) (z : N → unitInterval) (a c : A) :
    score constant coefficient (noisyBids eps b z) a-
      score constant coefficient (noisyBids eps b z) c =
      (score constant coefficient b a-score constant coefficient b c)+
        ∑ i, (coefficient a i-coefficient c i)*b i*eps*(z i:ℝ) := by
  have hexpand (q : A) :
      score constant coefficient (noisyBids eps b z) q =
        score constant coefficient b q+∑ i, coefficient q i*b i*eps*(z i:ℝ) := by
    unfold score noisyBids
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hs : (∑ i, coefficient a i*b i*eps*(z i:ℝ))-
      (∑ i, coefficient c i*b i*eps*(z i:ℝ)) =
      ∑ i, (coefficient a i-coefficient c i)*b i*eps*(z i:ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hexpand a,hexpand c]
  linear_combination hs

theorem ae_score_ties_identical {N : ℕ} {A : Type*} [Fintype A]
    (constant : A → ℝ) (coefficient : A → Fin N → ℝ)
    {eps : ℝ} (heps : eps ≠ 0) (b : Fin N → ℝ) (hb : ∀ i, b i ≠ 0) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ a c, score constant coefficient (noisyBids eps b z) a=
        score constant coefficient (noisyBids eps b z) c →
        constant a=constant c ∧ coefficient a=coefficient c := by
  apply ae_all_iff.mpr
  intro a
  apply ae_all_iff.mpr
  intro c
  by_cases hc : coefficient a=coefficient c
  · exact ae_of_all _ fun z hz => by
      refine ⟨?_,hc⟩
      simp only [score,hc] at hz
      linarith
  · obtain ⟨i,hi⟩ : ∃ i, coefficient a i ≠ coefficient c i := by
      by_contra hn
      apply hc
      funext i
      simpa using not_exists.mp hn i
    have hn : (coefficient a i-coefficient c i)*b i*eps ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hi) (hb i)) heps
    filter_upwards [LowBody.ae_iid_linear_ne (volume : Measure (LowBody.LowValue 1))
      (fun j => (coefficient a j-coefficient c j)*b j*eps) i hn
      (-(score constant coefficient b a-score constant coefficient b c))] with z hz hscore
    exfalso
    apply hz
    have he := noisy_score_difference constant coefficient eps b z a c
    rw [hscore,sub_self] at he
    linarith

theorem ae_noisy_selector_locally_constant {N : ℕ} {A : Type*}
    [Fintype A] [Nonempty A] (constant : A → ℝ) (coefficient : A → Fin N → ℝ)
    {eps : ℝ} (heps : eps ≠ 0) (b : Fin N → ℝ) (hb : ∀ i, b i ≠ 0) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ᶠ a in 𝓝 b,
        FiniteSelector.select (score constant coefficient (noisyBids eps a z))=
          FiniteSelector.select (score constant coefficient (noisyBids eps b z)) := by
  filter_upwards [ae_score_ties_identical constant coefficient heps b hb] with z hz
  apply select_eventually_eq
  · intro a
    exact (continuous_score constant coefficient a).comp
      (continuous_noisyBids eps |>.comp (continuous_id.prodMk continuous_const))
  · intro a c hac y
    obtain ⟨h0,h1⟩ := hz a c hac
    simp only [score,h0,h1]

section TopSelection
open AtypicalUnequal

def topConstant {N : ℕ} (A : Finset (Fin N)) (c : ℕ) (S : Finset (Fin N)) : ℝ :=
  if TopFeasible A c S then 0 else -1

def topCoefficient {N : ℕ} (A : Finset (Fin N)) (c : ℕ)
    (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  if TopFeasible A c S ∧ i ∈ S then 1 else 0

theorem topObjective_eq_score {N : ℕ} (A : Finset (Fin N)) (c : ℕ)
    (b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i) :
    topObjective A c b=score (topConstant A c) (topCoefficient A c) b := by
  funext S
  by_cases hS : TopFeasible A c S
  · simp only [topObjective,topConstant,topCoefficient,hS,ite_true,true_and,score,
      zero_add,ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_ite_mem,Finset.univ_inter]
    exact Finset.sum_congr rfl (fun i _ => max_eq_left (hb i))
  · simp [topObjective,topConstant,topCoefficient,hS,score]

theorem ae_all_topSelections_locally_constant {N : ℕ} {eps : ℝ}
    (heps0 : 0 ≤ eps) (heps : eps ≠ 0) (b : Fin N → ℝ) (hb : ∀ i, 0 < b i) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ A : Finset (Fin N), ∀ c : Fin (N+1),
      ∀ᶠ a in 𝓝 b,
        topSelection A c.val (noisyBids eps a z)=topSelection A c.val (noisyBids eps b z) := by
  apply ae_all_iff.mpr
  intro A
  apply ae_all_iff.mpr
  intro c
  have hpositive : ∀ᶠ a : Fin N → ℝ in 𝓝 b, ∀ i, 0 < a i :=
    Filter.eventually_all.mpr (fun i =>
      (isOpen_lt continuous_const (continuous_apply i)).mem_nhds (hb i))
  filter_upwards [ae_noisy_selector_locally_constant (topConstant A c.val)
    (topCoefficient A c.val) heps b (fun i => (hb i).ne')] with z hz
  filter_upwards [hz,hpositive] with a ha hapos
  have hnoisy (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) (i : Fin N) :
      0 ≤ noisyBids eps a z i := by
    exact mul_nonneg (ha i).le (by nlinarith [mul_nonneg heps0 (z i).property.1])
  rw [topSelection,topSelection,topObjective_eq_score A c.val _ (hnoisy a hapos),
    topObjective_eq_score A c.val _ (hnoisy b hb)]
  exact ha

end TopSelection

section SmoothedLabel
variable {N : ℕ} {A : Type*} [Fintype A] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

def smoothedLabel (constant : A → ℝ) (coefficient : A → Fin N → ℝ)
    (eps : ℝ) (f : A → ℝ) (b : Fin N → ℝ) : ℝ :=
  ∫ z : Fin N → unitInterval,
    f (FiniteSelector.select (score constant coefficient (noisyBids eps b z)))
      ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

theorem continuousAt_smoothedLabel (constant : A → ℝ) (coefficient : A → Fin N → ℝ)
    {eps : ℝ} (heps : eps ≠ 0) (f : A → ℝ) (b : Fin N → ℝ) (hb : ∀ i, b i ≠ 0) :
    ContinuousAt (smoothedLabel constant coefficient eps f) b := by
  let C := ∑ a : A, |f a|
  have hC (a : A) : |f a| ≤ C :=
    Finset.single_le_sum (fun c _ => abs_nonneg (f c)) (Finset.mem_univ a)
  have hm (a : Fin N → ℝ) : Measurable (fun z : Fin N → unitInterval =>
      f (FiniteSelector.select (score constant coefficient (noisyBids eps a z)))) := by
    apply (measurable_of_countable f).comp
    apply FiniteSelector.measurable_select
    intro c
    exact ((continuous_score constant coefficient c).comp
      ((continuous_noisyBids eps).comp (continuous_const.prodMk continuous_id))).measurable
  apply MeasureTheory.continuousAt_of_dominated
    (F := fun a z => f (FiniteSelector.select (score constant coefficient (noisyBids eps a z))))
    (bound := fun _ => C)
    (Eventually.of_forall (fun a => (hm a).aestronglyMeasurable))
    (Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hC (FiniteSelector.select
        (score constant coefficient (noisyBids eps a z))))))
    (integrable_const C) ?_
  filter_upwards [ae_noisy_selector_locally_constant constant coefficient heps b hb] with z hz
  apply (continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ =>
    f (FiniteSelector.select (score constant coefficient (noisyBids eps b z)))) b).congr
  exact hz.mono (fun a ha => congrArg f ha.symm)

end SmoothedLabel
end FCAppendix.Affine.Tail04.AllNoiseFiniteSelector
