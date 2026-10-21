import FCAppendix.Affine.Tail04.PairedPrivateBorel
import FCAppendix.Affine.Tail04.EqualPrivateUpper
import FCAppendix.Affine.Tail04.OriginalCountSampling

noncomputable section
namespace FCAppendix.Affine.Tail04.PairedRawPolicy
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper EqualPrivateContinuity
open scoped BigOperators

local instance (N H : ℕ) : TopologicalSpace (Finset (Target N H)) := ⊥
local instance (N H : ℕ) : DiscreteTopology (Finset (Target N H)) := ⟨rfl⟩
local instance (N H : ℕ) : MeasurableSpace (Finset (Target N H)) := ⊤
local instance (N H : ℕ) : BorelSpace (Finset (Target N H)) := ⟨borel_eq_top_of_discrete.symm⟩

local instance (N H c : ℕ) : OpensMeasurableSpace (Action N H c) := inferInstance
local instance (H : ℕ) (R Rp : ℝ) : OpensMeasurableSpace (Signal H R Rp) := inferInstance

abbrev Parameters (N H0 H1 : ℕ) (R Rp : ℝ) :=
  (Fin N → ℝ) × (WeakProbability.Law (Signal H0 R Rp) × WeakProbability.Law (Signal H1 R Rp))

def plans (N H0 H1 c : ℕ) (R Rp ξ : ℝ) : Parameters N H0 H1 R Rp →
    WeakProbability.Law (Signal H0 R Rp × Action N H0 c) ×
      WeakProbability.Law (Signal H1 R Rp × Action N H1 c) :=
  PairedPrivateBorel.pairLaw (activeIndicator N H0 c R Rp) (activeIndicator N H1 c R Rp)
    (privateReceipt N H0 c R Rp) (privateReceipt N H1 c R Rp) ξ

lemma measurable_plans (N H0 H1 c : ℕ) (R Rp ξ : ℝ) :
    Measurable (plans N H0 H1 c R Rp ξ) :=
  PairedPrivateBorel.measurable_pairLaw _ _ _ _ ξ

def mean0 (N H0 H1 c : ℕ) (R Rp ξ : ℝ) (p : Parameters N H0 H1 R Rp) : Fin N → ℝ :=
  ambientMarginal (activeIndicator N H0 c R Rp) (plans N H0 H1 c R Rp ξ p).1.val

def mean1 (N H0 H1 c : ℕ) (R Rp ξ : ℝ) (p : Parameters N H0 H1 R Rp) : Fin N → ℝ :=
  ambientMarginal (activeIndicator N H1 c R Rp) (plans N H0 H1 c R Rp ξ p).2.val

lemma measurable_mean0 (N H0 H1 c : ℕ) (R Rp ξ : ℝ) :
    Measurable (mean0 N H0 H1 c R Rp ξ) :=
  ((continuous_ambientMarginal (activeIndicator N H0 c R Rp)).comp
    WeakProbability.continuous_val).measurable.comp (measurable_plans N H0 H1 c R Rp ξ).fst

lemma measurable_mean1 (N H0 H1 c : ℕ) (R Rp ξ : ℝ) :
    Measurable (mean1 N H0 H1 c R Rp ξ) :=
  ((continuous_ambientMarginal (activeIndicator N H1 c R Rp)).comp
    WeakProbability.continuous_val).measurable.comp (measurable_plans N H0 H1 c R Rp ξ).snd

lemma indicator_integral_bounds {N H c : ℕ} {R Rp : ℝ}
    (π : ProbabilityMeasure (Signal H R Rp × Action N H c)) (i : Fin N) :
    ambientMarginal (activeIndicator N H c R Rp) π i ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun z => (activeIndicator_bounds i z).1)
  · calc
      _ ≤ ∫ _z, (1:ℝ) ∂(π : Measure _) :=
        integral_mono ((ContinuousMap.equivBoundedOfCompact _ _ (activeIndicator N H c R Rp i)).integrable _)
          (integrable_const 1) (fun z => (activeIndicator_bounds i z).2)
      _=1 := by simp

lemma mean0_bounds (N H0 H1 c : ℕ) (R Rp ξ : ℝ) (p : Parameters N H0 H1 R Rp) (i : Fin N) :
    mean0 N H0 H1 c R Rp ξ p i∈Icc (0:ℝ) 1 :=
  indicator_integral_bounds (plans N H0 H1 c R Rp ξ p).1.val i

lemma mean1_bounds (N H0 H1 c : ℕ) (R Rp ξ : ℝ) (p : Parameters N H0 H1 R Rp) (i : Fin N) :
    mean1 N H0 H1 c R Rp ξ p i∈Icc (0:ℝ) 1 :=
  indicator_integral_bounds (plans N H0 H1 c R Rp ξ p).2.val i

structure Realizers (N H0 H1 c : ℕ) (R Rp ξ : ℝ) where
  zero : (Parameters N H0 H1 R Rp × Signal H0 R Rp) → unitInterval → Action N H0 c
  one : (Parameters N H0 H1 R Rp × Signal H1 R Rp) → unitInterval → Action N H1 c
  measurable_zero : Measurable (Function.uncurry zero)
  measurable_one : Measurable (Function.uncurry one)
  zero_best : ∀ p s u a,
    EqualPrivateFrontier.score (activeIndicator N H0 c R Rp) (privateReceipt N H0 c R Rp)
      p.1 (mean1 N H0 H1 c R Rp ξ p) ξ (s,a) ≤
    EqualPrivateFrontier.score (activeIndicator N H0 c R Rp) (privateReceipt N H0 c R Rp)
      p.1 (mean1 N H0 H1 c R Rp ξ p) ξ (s,zero (p,s) u)
  one_best : ∀ p s u a,
    EqualPrivateFrontier.score (activeIndicator N H1 c R Rp) (privateReceipt N H1 c R Rp)
      p.1 (mean0 N H0 H1 c R Rp ξ p) ξ (s,a) ≤
    EqualPrivateFrontier.score (activeIndicator N H1 c R Rp) (privateReceipt N H1 c R Rp)
      p.1 (mean0 N H0 H1 c R Rp ξ p) ξ (s,one (p,s) u)
  zero_joint : ∀ p,((WeakProbability.toMeasure p.2.1).prod (volume : Measure unitInterval)).map
    (fun z : Signal H0 R Rp × unitInterval => (z.1,zero (p,z.1) z.2))=
      WeakProbability.toMeasure (plans N H0 H1 c R Rp ξ p).1
  one_joint : ∀ p,((WeakProbability.toMeasure p.2.2).prod (volume : Measure unitInterval)).map
    (fun z : Signal H1 R Rp × unitInterval => (z.1,one (p,z.1) z.2))=
      WeakProbability.toMeasure (plans N H0 H1 c R Rp ξ p).2

def realizers (N H0 H1 c : ℕ) (R Rp ξ : ℝ) : Realizers N H0 H1 c R Rp ξ :=
  Classical.choice (show Nonempty (Realizers N H0 H1 c R Rp ξ) from by
    obtain ⟨f0,f1,h0,h1,hb0,hb1,hj0,hj1⟩ := PairedPrivateBorel.exists_pair_samplers
      (activeIndicator N H0 c R Rp) (activeIndicator N H1 c R Rp)
      (privateReceipt N H0 c R Rp) (privateReceipt N H1 c R Rp) ξ
    exact ⟨⟨f0,f1,h0,h1,hb0,hb1,hj0,hj1⟩⟩)

def zero (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ) :
    (Parameters N H0 H1 R Rp × Row H0 R Rp Rm) → unitInterval → Finset (Target N H0) :=
  fun z u => restore z.1.1 (mean1 N H0 H1 c R Rp ξ z.1) ξ z.2
    ((realizers N H0 H1 c R Rp ξ).zero (z.1,signal z.2) u)

def one (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ) :
    (Parameters N H0 H1 R Rp × Row H1 R Rp Rm) → unitInterval → Finset (Target N H1) :=
  fun z u => restore z.1.1 (mean0 N H0 H1 c R Rp ξ z.1) ξ z.2
    ((realizers N H0 H1 c R Rp ξ).one (z.1,signal z.2) u)

lemma measurable_zero (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ) :
    Measurable (Function.uncurry (zero N H0 H1 c R Rp Rm ξ)) := by
  change Measurable (fun z : ((Parameters N H0 H1 R Rp × Row H0 R Rp Rm) × unitInterval) =>
    restore z.1.1.1 (mean1 N H0 H1 c R Rp ξ z.1.1) ξ z.1.2
      ((realizers N H0 H1 c R Rp ξ).zero (z.1.1,signal z.1.2) z.2))
  have hp : Measurable (fun z : ((Parameters N H0 H1 R Rp × Row H0 R Rp Rm) × unitInterval) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hr : Measurable (fun z : ((Parameters N H0 H1 R Rp × Row H0 R Rp Rm) × unitInterval) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hf := (realizers N H0 H1 c R Rp ξ).measurable_zero.comp
    ((hp.prodMk (continuous_signal.measurable.comp hr)).prodMk measurable_snd)
  simpa only [Function.comp_def, Function.uncurry] using (measurable_restore ξ).comp
    ((hp.fst.prodMk (((measurable_mean1 N H0 H1 c R Rp ξ).comp hp).prodMk hr)).prodMk hf)

lemma measurable_one (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ) :
    Measurable (Function.uncurry (one N H0 H1 c R Rp Rm ξ)) := by
  change Measurable (fun z : ((Parameters N H0 H1 R Rp × Row H1 R Rp Rm) × unitInterval) =>
    restore z.1.1.1 (mean0 N H0 H1 c R Rp ξ z.1.1) ξ z.1.2
      ((realizers N H0 H1 c R Rp ξ).one (z.1.1,signal z.1.2) z.2))
  have hp : Measurable (fun z : ((Parameters N H0 H1 R Rp × Row H1 R Rp Rm) × unitInterval) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hr : Measurable (fun z : ((Parameters N H0 H1 R Rp × Row H1 R Rp Rm) × unitInterval) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hf := (realizers N H0 H1 c R Rp ξ).measurable_one.comp
    ((hp.prodMk (continuous_signal.measurable.comp hr)).prodMk measurable_snd)
  simpa only [Function.comp_def, Function.uncurry] using (measurable_restore ξ).comp
    ((hp.fst.prodMk (((measurable_mean0 N H0 H1 c R Rp ξ).comp hp).prodMk hr)).prodMk hf)

lemma zero_capacity (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ)
    (p : Parameters N H0 H1 R Rp) (row : Row H0 R Rp Rm) (u : unitInterval) :
    (zero N H0 H1 c R Rp Rm ξ (p,row) u).card≤ c := restore_capacity _ _ _ _ _

lemma one_capacity (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ)
    (p : Parameters N H0 H1 R Rp) (row : Row H1 R Rp Rm) (u : unitInterval) :
    (one N H0 H1 c R Rp Rm ξ (p,row) u).card≤ c := restore_capacity _ _ _ _ _

theorem zero_optimal (N H0 H1 c : ℕ) {R Rp Rm U ξ : ℝ}
    (p : Parameters N H0 H1 R Rp) (row : Row H0 R Rp Rm) (u : unitInterval)
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i,p.1 i∈Icc (0:ℝ) U)
    (hR : 0≤ R) (hRp : Rp≤ U) (hU : U< Rm) (hRm : 0< Rm) :
    Finite.Optimal c (receipt p.1 (mean1 N H0 H1 c R Rp ξ p) ξ row)
      (zero N H0 H1 c R Rp Rm ξ (p,row) u) := by
  apply restore_optimal _ _ ξ row _ hξ hb (mean1_bounds N H0 H1 c R Rp ξ p) hR hRp hU hRm
  intro S hS
  have h := (realizers N H0 H1 c R Rp ξ).zero_best p (signal row) u
    (actionFor N H0 c (marks (signal row)) S hS)
  rw [score_eq_revenue,score_eq_revenue,selected_actionFor] at h
  exact h

theorem one_optimal (N H0 H1 c : ℕ) {R Rp Rm U ξ : ℝ}
    (p : Parameters N H0 H1 R Rp) (row : Row H1 R Rp Rm) (u : unitInterval)
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i,p.1 i∈Icc (0:ℝ) U)
    (hR : 0≤ R) (hRp : Rp≤ U) (hU : U< Rm) (hRm : 0< Rm) :
    Finite.Optimal c (receipt p.1 (mean0 N H0 H1 c R Rp ξ p) ξ row)
      (one N H0 H1 c R Rp Rm ξ (p,row) u) := by
  apply restore_optimal _ _ ξ row _ hξ hb (mean0_bounds N H0 H1 c R Rp ξ p) hR hRp hU hRm
  intro S hS
  have h := (realizers N H0 H1 c R Rp ξ).one_best p (signal row) u
    (actionFor N H1 c (marks (signal row)) S hS)
  rw [score_eq_revenue,score_eq_revenue,selected_actionFor] at h
  exact h

lemma original_signal_joint {H c N : ℕ} {R Rp Rm : ℝ}
    {P : Type*} [MeasurableSpace P]
    (f : (P × Signal H R Rp) → unitInterval → Action N H c)
    (hf : Measurable (Function.uncurry f)) (p : P)
    (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ]
    (μ : Measure (Signal H R Rp)) (π : Measure (Signal H R Rp × Action N H c))
    (hθ : θ.map signal=μ)
    (hj : (μ.prod (volume : Measure unitInterval)).map
      (fun z : Signal H R Rp × unitInterval => (z.1,f (p,z.1) z.2))=π) :
    ((θ.prod (volume : Measure unitInterval)).map
      (fun z : Row H R Rp Rm × unitInterval => (signal z.1,f (p,signal z.1) z.2)))=π := by
  have hm : Measurable (fun z : Signal H R Rp × unitInterval => (z.1,f (p,z.1) z.2)) :=
    measurable_fst.prodMk (hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
  have he : (θ.prod (volume : Measure unitInterval)).map (Prod.map signal id)=
      μ.prod volume := by
    rw [← Measure.map_prod_map θ (volume : Measure unitInterval) continuous_signal.measurable measurable_id,hθ,Measure.map_id]
  calc
    _=((θ.prod (volume : Measure unitInterval)).map (Prod.map signal id)).map
        (fun z : Signal H R Rp × unitInterval => (z.1,f (p,z.1) z.2)) := by
      rw [Measure.map_map hm (continuous_signal.measurable.prodMap measurable_id)]
      rfl
    _=π := by rw [he,hj]

theorem original_zero_joint (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ)
    (p : Parameters N H0 H1 R Rp) (θ : Measure (Row H0 R Rp Rm)) [IsProbabilityMeasure θ]
    (hθ : θ.map signal=WeakProbability.toMeasure p.2.1) :
    (θ.prod (volume : Measure unitInterval)).map
      (fun z : Row H0 R Rp Rm × unitInterval =>
        (signal z.1,(realizers N H0 H1 c R Rp ξ).zero (p,signal z.1) z.2))=
      WeakProbability.toMeasure (plans N H0 H1 c R Rp ξ p).1 :=
  original_signal_joint _ (realizers N H0 H1 c R Rp ξ).measurable_zero p θ _ _ hθ
    ((realizers N H0 H1 c R Rp ξ).zero_joint p)

theorem original_one_joint (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ)
    (p : Parameters N H0 H1 R Rp) (θ : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ]
    (hθ : θ.map signal=WeakProbability.toMeasure p.2.2) :
    (θ.prod (volume : Measure unitInterval)).map
      (fun z : Row H1 R Rp Rm × unitInterval =>
        (signal z.1,(realizers N H0 H1 c R Rp ξ).one (p,signal z.1) z.2))=
      WeakProbability.toMeasure (plans N H0 H1 c R Rp ξ p).2 :=
  original_signal_joint _ (realizers N H0 H1 c R Rp ξ).measurable_one p θ _ _ hθ
    ((realizers N H0 H1 c R Rp ξ).one_joint p)

theorem original_zero_mean (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ)
    (p : Parameters N H0 H1 R Rp) (θ : Measure (Row H0 R Rp Rm)) [IsProbabilityMeasure θ]
    (hθ : θ.map signal=WeakProbability.toMeasure p.2.1) (i : Fin N) :
    LocalSamplerMean.mean (zero N H0 H1 c R Rp Rm ξ) p θ (Sum.inl i)=
      mean0 N H0 H1 c R Rp ξ p i := by
  change _=∫ z,activeIndicator N H0 c R Rp i z
    ∂WeakProbability.toMeasure (plans N H0 H1 c R Rp ξ p).1
  rw [←original_zero_joint N H0 H1 c R Rp Rm ξ p θ hθ]
  have hm : Measurable (fun z : Row H0 R Rp Rm × unitInterval =>
      (signal z.1,(realizers N H0 H1 c R Rp ξ).zero (p,signal z.1) z.2)) :=
    (continuous_signal.measurable.comp measurable_fst).prodMk
      ((realizers N H0 H1 c R Rp ξ).measurable_zero.comp
        ((measurable_const.prodMk (continuous_signal.measurable.comp measurable_fst)).prodMk measurable_snd))
  rw [integral_map hm.aemeasurable (activeIndicator N H0 c R Rp i).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by simp [zero,activeIndicator,restore_active_iff]

theorem original_one_mean (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ)
    (p : Parameters N H0 H1 R Rp) (θ : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ]
    (hθ : θ.map signal=WeakProbability.toMeasure p.2.2) (i : Fin N) :
    LocalSamplerMean.mean (one N H0 H1 c R Rp Rm ξ) p θ (Sum.inl i)=
      mean1 N H0 H1 c R Rp ξ p i := by
  change _=∫ z,activeIndicator N H1 c R Rp i z
    ∂WeakProbability.toMeasure (plans N H0 H1 c R Rp ξ p).2
  rw [←original_one_joint N H0 H1 c R Rp Rm ξ p θ hθ]
  have hm : Measurable (fun z : Row H1 R Rp Rm × unitInterval =>
      (signal z.1,(realizers N H0 H1 c R Rp ξ).one (p,signal z.1) z.2)) :=
    (continuous_signal.measurable.comp measurable_fst).prodMk
      ((realizers N H0 H1 c R Rp ξ).measurable_one.comp
        ((measurable_const.prodMk (continuous_signal.measurable.comp measurable_fst)).prodMk measurable_snd))
  rw [integral_map hm.aemeasurable (activeIndicator N H1 c R Rp i).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by simp [one,activeIndicator,restore_active_iff]

theorem original_count (N H0 H1 c : ℕ) (R Rp Rm ξ : ℝ)
    (p : Parameters N H0 H1 R Rp)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hθ0 : θ0.map signal=WeakProbability.toMeasure p.2.1)
    (hθ1 : θ1.map signal=WeakProbability.toMeasure p.2.2) (i : Fin N) :
    originalIndependentCountLaw (zero N H0 H1 c R Rp Rm ξ) (one N H0 H1 c R Rp Rm ξ)
      (measurable_zero N H0 H1 c R Rp Rm ξ) (measurable_one N H0 H1 c R Rp Rm ξ)
      p θ0 θ1 (Sum.inl i) (Sum.inl i)=
      twoCoinCountLaw (mean0 N H0 H1 c R Rp ξ p i) (mean1 N H0 H1 c R Rp ξ p i)
        (mean0_bounds N H0 H1 c R Rp ξ p i).1 (mean0_bounds N H0 H1 c R Rp ξ p i).2
        (mean1_bounds N H0 H1 c R Rp ξ p i).1 (mean1_bounds N H0 H1 c R Rp ξ p i).2 := by
  simp only [originalIndependentCountLaw_eq,original_zero_mean N H0 H1 c R Rp Rm ξ p θ0 hθ0,
    original_one_mean N H0 H1 c R Rp Rm ξ p θ1 hθ1]

end FCAppendix.Affine.Tail04.PairedRawPolicy
