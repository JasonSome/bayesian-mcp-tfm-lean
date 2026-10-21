import FCAppendix.Affine.Tail04.LocalHighCommon
import FCAppendix.Existence.R01PayOnceRowIntegration

noncomputable section
namespace FCAppendix.Affine.Tail04.LocalSamplerMean
open MeasureTheory ProbabilityTheory Set Classical

variable {α P X A : Type*} [Fintype α] [DecidableEq α]
  [MeasurableSpace P] [MeasurableSpace X] [MeasurableSpace A]

local instance : MeasurableSpace (Finset α) := ⊤

def mean (f : (P × X) → unitInterval → Finset α) (p : P) (θ : Measure X) (i : α) : ℝ :=
  ∫ z : X × unitInterval, if i ∈ f (p,z.1) z.2 then (1:ℝ) else 0 ∂θ.prod volume

lemma measurable_indicator (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P) (i : α) :
    Measurable (fun z : X × unitInterval => if i ∈ f (p,z.1) z.2 then (1:ℝ) else 0) :=
  (measurable_of_countable (fun S : Finset α => if i ∈ S then (1:ℝ) else 0)).comp
    (hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))

lemma integrable_indicator (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P) (θ : Measure X)
    [IsProbabilityMeasure θ] (i : α) :
    Integrable (fun z : X × unitInterval => if i ∈ f (p,z.1) z.2 then (1:ℝ) else 0)
      (θ.prod volume) :=
  Integrable.of_bound (measurable_indicator f hf p i).aestronglyMeasurable 1
    (ae_of_all _ fun z => by split_ifs <;> norm_num)

theorem bounds (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P) (θ : Measure X)
    [IsProbabilityMeasure θ] (i : α) : mean f p θ i ∈ Icc (0:ℝ) 1 := by
  unfold mean
  constructor
  · exact integral_nonneg (fun z => by
      change 0 ≤ if i ∈ f (p,z.1) z.2 then (1:ℝ) else 0
      split_ifs <;> norm_num)
  · calc
      _ ≤ ∫ _z : X × unitInterval, (1:ℝ) ∂θ.prod volume :=
        integral_mono_ae (integrable_indicator f hf p θ i) (integrable_const 1)
          (ae_of_all _ fun z => by
            change (if i ∈ f (p,z.1) z.2 then (1:ℝ) else 0) ≤ 1
            split_ifs <;> norm_num)
      _ = 1 := by simp

omit [Fintype α] [MeasurableSpace P] in
theorem congr (f g : (P × X) → unitInterval → Finset α)
    (p : P) (θ : Measure X) (i : α)
    (h : ∀ x u, f (p,x) u=g (p,x) u) : mean f p θ i=mean g p θ i := by
  unfold mean
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change (if i ∈ f (p,z.1) z.2 then (1:ℝ) else 0) =
      if i ∈ g (p,z.1) z.2 then (1:ℝ) else 0
    rw [h z.1 z.2]

omit [DecidableEq α] in
theorem integral_finiteLaw (ν : FiniteLaw α) (g : α → ℝ)
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (∫ i, g i ∂FiniteLaw.probabilityMeasure ν)=ν.expect g := by
  have hν : FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure ν) id measurable_id=ν :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ id measurable_id ν Measure.map_id
  calc
    _=(FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure ν) id measurable_id).expect g :=
      (FiniteLaw.expect_ofMeasure _ id measurable_id g).symm
    _=ν.expect g := by rw [hν]

theorem of_law (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P) (θ : Measure X)
    [IsProbabilityMeasure θ] (K : X → Measure (Finset α))
    (hlaw : ∀ x, volume.map (f (p,x))=K x) (i : α) :
    mean f p θ i = ∫ x, ∫ S, (if i ∈ S then (1:ℝ) else 0) ∂K x ∂θ := by
  rw [mean,integral_prod _ (integrable_indicator f hf p θ i)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hfx : Measurable (f (p,x)) := hf.comp (measurable_const.prodMk measurable_id)
    change (∫ u : unitInterval, if i ∈ f (p,x) u then (1:ℝ) else 0 ∂volume) =
      ∫ S, if i ∈ S then (1:ℝ) else 0 ∂K x
    rw [← hlaw x,integral_map hfx.aemeasurable
      (measurable_of_countable (fun S : Finset α => if i ∈ S then (1:ℝ) else 0)).aestronglyMeasurable]

theorem of_finiteLaw (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P) (θ : Measure X)
    [IsProbabilityMeasure θ] (K : X → FiniteLaw (Finset α))
    (hlaw : ∀ x, volume.map (f (p,x))=FiniteLaw.probabilityMeasure (K x)) (i : α) :
    mean f p θ i = ∫ x, (K x).prob (fun S => i ∈ S) ∂θ := by
  rw [of_law f hf p θ _ hlaw i]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (∫ S, if i ∈ S then (1:ℝ) else 0 ∂FiniteLaw.probabilityMeasure (K x)) =
      (K x).prob (fun S => i ∈ S)
    rw [integral_finiteLaw]
    exact (FiniteLaw.prob_eq_expect _ _).symm

theorem of_deterministic (g : P × X → Finset α) (hg : Measurable g)
    (p : P) (θ : Measure X) [IsProbabilityMeasure θ] (i : α) :
    mean (fun z _ => g z) p θ i = ∫ x, if i ∈ g (p,x) then (1:ℝ) else 0 ∂θ := by
  have hf : Measurable (Function.uncurry (fun z : P × X => fun _ : unitInterval => g z)) := by
    change Measurable (fun z : (P × X) × unitInterval => g z.1)
    exact hg.comp measurable_fst
  rw [mean,integral_prod _ (integrable_indicator (fun z _ => g z) hf p θ i)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases h : i ∈ g (p,x) <;> simp [h]

theorem of_kernel_map (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P) (θ : Measure X)
    [IsProbabilityMeasure θ] (κ : Kernel X A) [IsMarkovKernel κ]
    (r : X × A → Finset α) (hr : Measurable r)
    (hlaw : ∀ x, volume.map (f (p,x))=(κ x).map (fun a => r (x,a))) (i : α) :
    mean f p θ i = ∫ z : X × A, if i ∈ r z then (1:ℝ) else 0 ∂(θ ⊗ₘ κ) := by
  rw [of_law f hf p θ _ hlaw i]
  have hri : Measurable (fun z : X × A => if i ∈ r z then (1:ℝ) else 0) :=
    (measurable_of_countable (fun S : Finset α => if i ∈ S then (1:ℝ) else 0)).comp hr
  have hint : Integrable (fun z : X × A => if i ∈ r z then (1:ℝ) else 0) (θ ⊗ₘ κ) :=
    Integrable.of_bound hri.aestronglyMeasurable 1 (ae_of_all _ fun z => by split_ifs <;> norm_num)
  rw [Measure.integral_compProd hint]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (∫ S, if i ∈ S then (1:ℝ) else 0 ∂(κ x).map (fun a => r (x,a))) =
      ∫ a, if i ∈ r (x,a) then (1:ℝ) else 0 ∂κ x
    exact integral_map (μ := κ x)
      (hr.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (measurable_of_countable (fun S : Finset α => if i ∈ S then (1:ℝ) else 0)).aestronglyMeasurable

end FCAppendix.Affine.Tail04.LocalSamplerMean
