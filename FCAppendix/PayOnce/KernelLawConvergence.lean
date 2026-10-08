import FCAppendix.PayOnce.KernelTailEvent
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace FCAppendix.PayOnce.KernelLawConvergence
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.CommonList FCAppendix.PayOnce.KernelTailEvent

theorem kernel_price_difference {n : ℕ} (hn : 2 ≤ n) {L T ℓ : ℝ}
    (hℓ : 0 < ℓ) (hL : ℓ ≤ L) (hT : ℓ ≤ T) (b : ℝ) :
    |kernel n b L - kernel n b T| ≤ ((n : ℝ) / ℓ) * |L - T| := by
  by_cases hb : b ≤ ℓ
  · rw [kernel_of_le n (hb.trans hL), kernel_of_le n (hb.trans hT), sub_self, abs_zero]
    positivity
  · have hb' : ℓ < b := lt_of_not_ge hb
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hd := scalar_difference_bound n hn b (hℓ.trans hb') L T
      (kernel n b L) (kernel n b T)
      (scalarThreshold_kernel n hn (hℓ.trans hb') (hℓ.trans_le hL))
      (scalarThreshold_kernel n hn (hℓ.trans hb') (hℓ.trans_le hT))
    have hc : ℓ / (n : ℝ) ≤ b / n := div_le_div_of_nonneg_right hb'.le hnR.le
    have hd' := (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans hd
    have hden : 0 < ℓ / (n : ℝ) := div_pos hℓ hnR
    have hh : |kernel n b L - kernel n b T| ≤ |L - T| / (ℓ / (n : ℝ)) :=
      (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hd')
    convert hh using 1
    field_simp

theorem tendstoUniformly_kernel {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {L : α → ℝ} {T : ℝ} (hT : 0 < T) (hL : Tendsto L l (𝓝 T)) :
    TendstoUniformly (fun a b => kernel n b (L a)) (fun b => kernel n b T) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hlower : ∀ᶠ a in l, T / 2 ≤ L a := hL.eventually_const_le (by linarith)
  have hz : Tendsto (fun a => ((n : ℝ) / (T / 2)) * |L a - T|) l (𝓝 0) := by
    simpa only [sub_self, abs_zero, mul_zero] using (hL.sub_const T).abs.const_mul ((n : ℝ) / (T / 2))
  filter_upwards [hlower, hz.eventually_lt_const hε] with a ha he b
  have hh := kernel_price_difference hn (show 0 < T / 2 by linarith) ha
    (show T / 2 ≤ T by linarith) b
  simpa only [Real.dist_eq, abs_sub_comm] using hh.trans_lt he

theorem tendsto_integral_varying_test {Ω α : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] {l : Filter α}
    {ν : α → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hweak : Tendsto ν l (𝓝 μ))
    (F : α → BoundedContinuousFunction Ω ℝ) (f : BoundedContinuousFunction Ω ℝ)
    (hF : TendstoUniformly (fun a => F a) f l) :
    Tendsto (fun a => ∫ x, F a x ∂(ν a : Measure Ω)) l
      (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  have hzero : Tendsto (fun a => (∫ x, F a x ∂(ν a : Measure Ω)) -
      ∫ x, f x ∂(ν a : Measure Ω)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hF (ε / 2) (by linarith)] with a ha
    have hh := norm_integral_le_of_norm_le_const (μ := (ν a : Measure Ω))
      (f := fun x => F a x - f x) (C := ε / 2) (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using (ha x).le)
    rw [integral_sub ((F a).integrable (μ := (ν a : Measure Ω))) (f.integrable (μ := (ν a : Measure Ω))), probReal_univ, mul_one] at hh
    rw [dist_zero_right]
    exact hh.trans_lt (by linarith)
  have hfixed := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
  simpa only [sub_add_cancel, zero_add] using hzero.add hfixed

theorem tendsto_map_varying {Ω α : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω] {l : Filter α}
    {ν : α → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hweak : Tendsto ν l (𝓝 μ)) (F : α → C(Ω, ℝ)) (f : C(Ω, ℝ))
    (hF : TendstoUniformly (fun a => F a) f l)
    (hFb : ∀ᶠ a in l, ∀ x, F a x ∈ Icc (0 : ℝ) 1)
    (hfb : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun a => (ν a).map (F a).continuous.measurable.aemeasurable) l
      (𝓝 (μ.map f.continuous.measurable.aemeasurable)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  have hu : TendstoUniformly (fun a x => g (F a x)) (fun x => g (f x)) l :=
    UniformContinuousOn.comp_tendstoUniformly_eventually hFb hfb
      (isCompact_Icc.uniformContinuousOn_of_continuous g.continuous.continuousOn) hF
  have hi := tendsto_integral_varying_test hweak
    (fun a => g.compContinuous (F a)) (g.compContinuous f) hu
  have hmap (ν₀ : ProbabilityMeasure Ω) (F₀ : C(Ω, ℝ)) :
      (∫ x, g x ∂(ν₀.map F₀.continuous.measurable.aemeasurable : Measure ℝ)) =
        ∫ x, g (F₀ x) ∂(ν₀ : Measure Ω) := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map F₀.continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable
  simp_rw [hmap]
  exact hi

theorem tendsto_kernel_law {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {ν : α → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hweak : Tendsto ν l (𝓝 μ)) {L : α → ℝ} {T : ℝ}
    (hLpos : ∀ a, 0 < L a) (hT : 0 < T) (hL : Tendsto L l (𝓝 T)) :
    Tendsto (fun a => (ν a).map (continuous_kernel_bid hn (hLpos a)).measurable.aemeasurable) l
      (𝓝 (μ.map (continuous_kernel_bid hn hT).measurable.aemeasurable)) := by
  exact tendsto_map_varying hweak
    (fun a => ⟨fun b => kernel n b (L a), continuous_kernel_bid hn (hLpos a)⟩)
    ⟨fun b => kernel n b T, continuous_kernel_bid hn hT⟩
    (tendstoUniformly_kernel hn hT hL)
    (.of_forall fun a => kernel_bounds hn (hLpos a)) (kernel_bounds hn hT)

noncomputable def compactKernel (n : ℕ) (b : ENNReal) (L : ℝ) : ℝ :=
  if b = ⊤ then 1 else kernel n b.toReal L

@[simp] theorem compactKernel_top (n : ℕ) (L : ℝ) : compactKernel n ⊤ L = 1 := by
  simp [compactKernel]

@[simp] theorem compactKernel_ofReal (n : ℕ) {b : ℝ} (hb : 0 ≤ b) (L : ℝ) :
    compactKernel n (ENNReal.ofReal b) L = kernel n b L := by
  simp [compactKernel, ENNReal.toReal_ofReal hb]

theorem compactKernel_bounds {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L)
    (b : ENNReal) : compactKernel n b L ∈ Icc (0 : ℝ) 1 := by
  by_cases hb : b = ⊤
  · simp [hb]
  · simpa [compactKernel, hb] using kernel_bounds hn hL b.toReal

theorem continuous_compactKernel {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) :
    Continuous (fun b => compactKernel n b L) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  by_cases hb : b = ⊤
  · subst b
    have he : (fun b : ENNReal => compactKernel n b L) =ᶠ[𝓝 ⊤] fun _ => 1 := by
      filter_upwards [eventually_gt_nhds (ENNReal.ofReal_lt_top (r := (n : ℝ) * L))] with b hb
      by_cases hbt : b = ⊤
      · simp [hbt]
      · rw [compactKernel, if_neg hbt]
        apply kernel_of_ge n hn hL
        have hh := ENNReal.toReal_mono hbt hb.le
        rwa [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg n) hL.le)] at hh
    exact continuousAt_const.congr_of_eventuallyEq he
  · have hc := (continuous_kernel_bid hn hL).continuousAt.comp (ENNReal.continuousAt_toReal hb)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (lt_top_iff_ne_top.mpr hb)] with x hx
    simp [compactKernel, hx.ne]

theorem compactKernel_price_difference {n : ℕ} (hn : 2 ≤ n) {L T ℓ : ℝ}
    (hℓ : 0 < ℓ) (hL : ℓ ≤ L) (hT : ℓ ≤ T) (b : ENNReal) :
    |compactKernel n b L - compactKernel n b T| ≤ ((n : ℝ) / ℓ) * |L - T| := by
  by_cases hb : b = ⊤
  · simp only [hb, compactKernel_top, sub_self, abs_zero]
    positivity
  · simpa [compactKernel, hb] using kernel_price_difference hn hℓ hL hT b.toReal

theorem tendstoUniformly_compactKernel {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {L : α → ℝ} {T : ℝ} (hT : 0 < T) (hL : Tendsto L l (𝓝 T)) :
    TendstoUniformly (fun a b => compactKernel n b (L a)) (fun b => compactKernel n b T) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hlower : ∀ᶠ a in l, T / 2 ≤ L a := hL.eventually_const_le (by linarith)
  have hz : Tendsto (fun a => ((n : ℝ) / (T / 2)) * |L a - T|) l (𝓝 0) := by
    simpa only [sub_self, abs_zero, mul_zero] using (hL.sub_const T).abs.const_mul ((n : ℝ) / (T / 2))
  filter_upwards [hlower, hz.eventually_lt_const hε] with a ha he b
  have hh := compactKernel_price_difference hn (show 0 < T / 2 by linarith) ha
    (show T / 2 ≤ T by linarith) b
  simpa only [Real.dist_eq, abs_sub_comm] using hh.trans_lt he

theorem tendsto_compactKernel_law {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {ν : α → ProbabilityMeasure ENNReal} {μ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto ν l (𝓝 μ)) {L : α → ℝ} {T : ℝ}
    (hLpos : ∀ a, 0 < L a) (hT : 0 < T) (hL : Tendsto L l (𝓝 T)) :
    Tendsto (fun a => (ν a).map (continuous_compactKernel hn (hLpos a)).measurable.aemeasurable) l
      (𝓝 (μ.map (continuous_compactKernel hn hT).measurable.aemeasurable)) := by
  exact tendsto_map_varying hweak
    (fun a => ⟨fun b => compactKernel n b (L a), continuous_compactKernel hn (hLpos a)⟩)
    ⟨fun b => compactKernel n b T, continuous_compactKernel hn hT⟩
    (tendstoUniformly_compactKernel hn hT hL)
    (.of_forall fun a => compactKernel_bounds hn (hLpos a)) (compactKernel_bounds hn hT)

theorem tendsto_transformed_compactKernel_law {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {ν : α → ProbabilityMeasure ENNReal} {μ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto ν l (𝓝 μ)) {x : α → ℝ} {y s : ℝ}
    (hx : ∀ a, 0 < x a) (hy : 0 < y) (hxy : Tendsto x l (𝓝 y))
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Tendsto (fun a => (ν a).map (continuous_compactKernel hn
      (mul_pos (hx a) (H_pos n (by omega) s hs hs1))).measurable.aemeasurable) l
      (𝓝 (μ.map (continuous_compactKernel hn
        (mul_pos hy (H_pos n (by omega) s hs hs1))).measurable.aemeasurable)) := by
  exact tendsto_compactKernel_law hn hweak
    (fun a => mul_pos (hx a) (H_pos n (by omega) s hs hs1))
    (mul_pos hy (H_pos n (by omega) s hs hs1)) (hxy.mul_const (H n s))

end FCAppendix.PayOnce.KernelLawConvergence
