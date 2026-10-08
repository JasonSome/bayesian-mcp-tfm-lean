import FCAppendix.PayOnce.KernelDemand
import Mathlib.Probability.Moments.Variance

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open KernelLawConvergence KernelTailEvent

theorem tendsto_kernel_moment {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {G : α → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G l (𝓝 G₀)) {L : α → ℝ} {T : ℝ}
    (hL : ∀ a, 0 < L a) (hT : 0 < T) (hLT : Tendsto L l (𝓝 T)) (q : ℕ) :
    Tendsto (fun a => ∫ b, compactKernel n b (L a) ^ q ∂(G a : Measure ENNReal)) l
      (𝓝 (∫ b, compactKernel n b T ^ q ∂(G₀ : Measure ENNReal))) := by
  have hu : TendstoUniformly (fun a b => compactKernel n b (L a) ^ q)
      (fun b => compactKernel n b T ^ q) l :=
    UniformContinuousOn.comp_tendstoUniformly_eventually
      (.of_forall fun a => compactKernel_bounds hn (hL a)) (compactKernel_bounds hn hT)
      (isCompact_Icc.uniformContinuousOn_of_continuous
        (continuous_pow q : Continuous (fun x : ℝ => x^q)).continuousOn)
      (tendstoUniformly_compactKernel hn hT hLT)
  exact tendsto_integral_varying_test hweak
    (fun a => boundedKernel hn (hL a) ^ q) (boundedKernel hn hT ^ q) hu

theorem memLp_compactKernel {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsFiniteMeasure G] {L : ℝ} (hL : 0 < L) (q : ENNReal) :
    MemLp (fun b => compactKernel n b L) q G := by
  apply MemLp.of_bound (continuous_compactKernel hn hL).aestronglyMeasurable 1
  exact .of_forall fun b => by
    rw [Real.norm_eq_abs,abs_of_nonneg (compactKernel_bounds hn hL b).1]
    exact (compactKernel_bounds hn hL b).2

theorem tendsto_kernel_variance {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {G : α → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G l (𝓝 G₀)) {L : α → ℝ} {T : ℝ}
    (hL : ∀ a, 0 < L a) (hT : 0 < T) (hLT : Tendsto L l (𝓝 T)) :
    Tendsto (fun a => variance (fun b => compactKernel n b (L a)) (G a : Measure ENNReal)) l
      (𝓝 (variance (fun b => compactKernel n b T) (G₀ : Measure ENNReal))) := by
  simp_rw [variance_eq_sub (memLp_compactKernel hn _ (hL _) 2),
    variance_eq_sub (memLp_compactKernel hn _ hT 2)]
  exact (tendsto_kernel_moment hn hweak hL hT hLT 2).sub
    ((tendsto_demand hn hweak hL hT hLT).pow 2)

theorem tendsto_kernel_variance_of_eventually_pos {n : ℕ} (hn : 2 ≤ n)
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀)) {L : ℕ → ℝ} {T : ℝ}
    (hL : ∀ᶠ m in atTop, 0 < L m) (hT : 0 < T) (hLT : Tendsto L atTop (𝓝 T)) :
    Tendsto (fun m => variance (fun b => compactKernel n b (L m)) (G m : Measure ENNReal)) atTop
      (𝓝 (variance (fun b => compactKernel n b T) (G₀ : Measure ENNReal))) := by
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp hL
  apply (tendsto_add_atTop_iff_nat m₀).mp
  exact tendsto_kernel_variance hn (hweak.comp (tendsto_add_atTop_nat m₀))
    (fun m => hm₀ (m+m₀) (by omega)) hT (hLT.comp (tendsto_add_atTop_nat m₀))

end FCAppendix.PayOnce.KernelDemand
