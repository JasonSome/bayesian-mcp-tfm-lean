import FCAppendix.PayOnce.DummyFirstOrder
import FCAppendix.PayOnce.BidScaling
import FCAppendix.PayOnce.SupportedFOC

namespace FCAppendix.PayOnce.DummyRareSuccess
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open CommonList DummyKernel KernelLawConvergence CompactKernelRareSuccess
open CompactifiedBidLaws RareSuccessSlope
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem allocation_tail_probability_eq (G : ProbabilityMeasure ℝ)
    {n c : ℕ} (hn : 2 ≤ n)
    (hpos : ∀ᵐ b ∂(G : Measure ℝ), 0 ≤ b) {b s : ℝ}
    (hb : 0 < b) (hs : 0 < s) (hs1 : s ≤ 1) :
    (Measure.pi (fun _ : ι => (G : Measure ℝ))).real
      {rivals | s ≤ allocation n c hn rivals b} =
    (Measure.pi (fun _ : ι => (scaledLaw G 1 : Measure ENNReal))).real
      {rivals | ∑ j, compactKernel n (rivals j) (b * H n s) ≤ (c : ℝ) - s} := by
  let T : (ι → ℝ) → (ι → ENNReal) := fun d j => ENNReal.ofReal (d j)
  have hT : Measurable T := measurable_pi_lambda _ fun j =>
    ENNReal.measurable_ofReal.comp (measurable_pi_apply j)
  have hmap : (Measure.pi (fun _ : ι => (G : Measure ℝ))).map T =
      Measure.pi (fun _ : ι => (scaledLaw G 1 : Measure ENNReal)) := by
    have hh := Measure.pi_map_pi (fun _ : ι => ENNReal.measurable_ofReal.aemeasurable
      (μ := (G : Measure ℝ)))
    change (Measure.pi (fun _ : ι => (G : Measure ℝ))).map T =
      Measure.pi (fun _ : ι => Measure.map (fun b : ℝ => ENNReal.ofReal (b / 1)) (G : Measure ℝ))
    simpa only [div_one, T] using hh
  have hL : 0 < b * H n s := mul_pos hb (H_pos n (by omega) s hs.le hs1)
  have hE : MeasurableSet {rivals : ι → ENNReal |
      ∑ j, compactKernel n (rivals j) (b * H n s) ≤ (c : ℝ) - s} := by
    apply measurableSet_le _ measurable_const
    exact Finset.measurable_sum _ fun j _ =>
      (continuous_compactKernel hn hL).measurable.comp (measurable_pi_apply j)
  unfold Measure.real
  rw [← hmap, Measure.map_apply hT hE]
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hp : ∀ᵐ d ∂Measure.pi (fun _ : ι => (G : Measure ℝ)), ∀ j, 0 ≤ d j :=
    Filter.eventually_all.mpr fun _ => Measure.tendsto_eval_ae_ae.eventually hpos
  filter_upwards [hp] with d hd
  change (s ≤ allocation n c hn d b) =
    (∑ j, compactKernel n (ENNReal.ofReal (d j)) (b * H n s) ≤ (c : ℝ) - s)
  simp only [compactKernel_ofReal _ (hd _)]
  exact propext (le_allocation_iff hn d hb hs hs1)

theorem exponential_tail_over_coverage {n : ℕ} (hn : 2 ≤ n)
    (G : ℕ → ProbabilityMeasure ℝ) (hpos : ∀ m, ∀ᵐ b ∂(G m : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ}
    {x : ℕ → ℝ} {x₀ δ ε ρ : ℝ}
    (hx : ∀ m, 0 < x m) (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hδ : 0 < δ) (hδε : δ < ε) (hε : ε ≤ 1) (hδρ : δ < ρ)
    (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ρ < ∫ b, compactKernel n b (x₀ * H n δ) ∂(G₀ : Measure ENNReal))
    (hcapacity : Tendsto (fun m => (c m : ℝ) / m) atTop (𝓝 ρ)) :
    ∃ a : ℝ, 0 < a ∧
      (∀ᶠ m in atTop,
        0 < coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))) (x m) ∧
        (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))).real
          {rivals | ε ≤ allocation n (c m) hn rivals (x m)} /
        coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))) (x m)
          ≤ exp (-a * m) / success n δ) ∧
      Tendsto (fun m =>
        (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))).real
          {rivals | ε ≤ allocation n (c m) hn rivals (x m)} /
        coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))) (x m))
        atTop (𝓝 0) := by
  let P := fun m => Measure.pi (fun _ : Fin m => (G m : Measure ℝ))
  let p := fun m (rivals : Fin m → ℝ) => allocation n (c m) hn rivals (x m)
  have hd (m : ℕ) := allocation_tail_probability_eq (ι := Fin m) (c := c m) (G m) hn (hpos m)
    (hx m) hδ (hδε.le.trans hε)
  have he (m : ℕ) := allocation_tail_probability_eq (ι := Fin m) (c := c m) (G m) hn (hpos m)
    (hx m) (hδ.trans hδε) hε
  obtain ⟨a, ha, htailpos, htailratio⟩ := exponential_kernel_tail_ratio hn hweak hx hx₀ hxx
    hδ hδε hε hδρ hsupport hdemand
    (KernelCoverage.tendsto_capacity_sub_div hcapacity δ)
    (KernelCoverage.tendsto_capacity_sub_div hcapacity ε)
  have htpos : ∀ᶠ m in atTop, 0 < (P m).real {rivals | δ ≤ p m rivals} := by
    filter_upwards [htailpos] with m hm
    rw [show (P m).real {rivals | δ ≤ p m rivals} = _ from hd m]
    exact hm
  have hratio : ∀ᶠ m in atTop,
      (P m).real {rivals | ε ≤ p m rivals} / (P m).real {rivals | δ ≤ p m rivals} ≤ exp (-a*m) := by
    filter_upwards [htailratio] with m hm
    rw [show (P m).real {rivals | δ ≤ p m rivals} = _ from hd m,
      show (P m).real {rivals | ε ≤ p m rivals} = _ from he m]
    exact hm
  exact ⟨a, ha, RareSuccessCoverage.tail_ratio_to_coverage P (by omega) p
    (fun m => measurable_allocation_rivals hn (hx m))
    (fun m rivals => allocation_bounds hn rivals (x m))
    hδ (hδε.le.trans hε) ha htpos hratio⟩

theorem relative_tails_tendsto_zero {n : ℕ} (hn : 2 ≤ n)
    (G : ℕ → ProbabilityMeasure ℝ) (hpos : ∀ m, ∀ᵐ b ∂(G m : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ}
    {x : ℕ → ℝ} {x₀ ρ : ℝ}
    (hx : ∀ m, 0 < x m) (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hρ : 0 < ρ) (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ρ < ∫ b, compactKernel n b (x₀ * H n s) ∂(G₀ : Measure ENNReal))
    (hcapacity : Tendsto (fun m => (c m : ℝ) / m) atTop (𝓝 ρ)) :
    (∀ᶠ m in atTop,
      0 < coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))) (x m)) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Tendsto (fun m =>
        (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))).real
          {rivals | ε ≤ allocation n (c m) hn rivals (x m)} /
        coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))) (x m))
        atTop (𝓝 0) := by
  have hrare (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) := by
    let δ := min ε ρ / 2
    have hδ : 0 < δ := half_pos (lt_min hε hρ)
    have hδε : δ < ε := (half_lt_self (lt_min hε hρ)).trans_le (min_le_left ε ρ)
    have hδρ : δ < ρ := (half_lt_self (lt_min hε hρ)).trans_le (min_le_right ε ρ)
    exact exponential_tail_over_coverage hn G hpos hweak hx hx₀ hxx hδ hδε hε1
      hδρ hsupport (hdemand δ hδ (hδε.le.trans hε1)) hcapacity
  obtain ⟨a, _, he, _⟩ := hrare 1 zero_lt_one le_rfl
  refine ⟨he.mono fun _ hm => hm.1, ?_⟩
  intro ε hε hε1
  obtain ⟨_, _, _, hh⟩ := hrare ε hε hε1
  exact hh

def regularSupportedSet (n c : ℕ) (G : Measure ℝ) (T : Set ℝ) : Set ℝ :=
  {b | 0 < b ∧
    (∀ᵐ rivals ∂Measure.pi (fun _ : ι => G), RegularClearing n c rivals b) ∧
    (𝓝[T ∩ Iio b] b).NeBot ∧ (𝓝[T ∩ Ioi b] b).NeBot}

theorem ae_mem_regularSupportedSet (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {n c : ℕ} (hn : 2 ≤ n)
    {T : Set ℝ} (hT : ∀ᵐ b ∂G, 0 < b → b ∈ T) :
    ∀ᵐ b ∂G, 0 < b → b ∈ regularSupportedSet (ι := ι) n c G T := by
  filter_upwards [DummyKernel.ae_regularClearing (ι := ι) G hatom hn,
    SupportedFOC.ae_positive_two_sided_accumulation G hatom hT] with b hreg hacc hb
  exact ⟨hb,hreg hb,hacc hb⟩

theorem surplus_tendsto_zero_of_supported_IC {n : ℕ} (hn : 2 ≤ n)
    (G : ℕ → ProbabilityMeasure ℝ) (hpos : ∀ m, ∀ᵐ b ∂(G m : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ}
    {T : ℕ → Set ℝ} {x w : ℕ → ℝ} {x₀ ρ : ℝ}
    (hgood : ∀ m, x m ∈ regularSupportedSet (ι := Fin m) n (c m) (G m : Measure ℝ) (T m))
    (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hρ : 0 < ρ) (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ρ < ∫ b, compactKernel n b (x₀ * H n s) ∂(G₀ : Measure ENNReal))
    (hcapacity : Tendsto (fun m => (c m : ℝ) / m) atTop (𝓝 ρ))
    (hIC : ∀ m y, y ∈ T m →
      (w m-y) * coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))) y ≤
      (w m-x m) * coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))) (x m)) :
    Tendsto (fun m =>
      deriv (coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ)))) (x m) /
      coverage n (c m) hn (Measure.pi (fun _ : Fin m => (G m : Measure ℝ))) (x m)) atTop atTop ∧
    Tendsto (fun m => w m-x m) atTop (𝓝 0) := by
  let P := fun m => Measure.pi (fun _ : Fin m => (G m : Measure ℝ))
  let p := fun m (rivals : Fin m → ℝ) => allocation n (c m) hn rivals (x m)
  let Q := fun m => coverage n (c m) hn (P m)
  have hx : ∀ m, 0 < x m := fun m => (hgood m).1
  choose weight hw hwb hwgap _ hderiv using fun m =>
    exists_measurable_weight_coverage_derivative hn (P m) (hx m) (hgood m).2.1
  have hrare := relative_tails_tendsto_zero hn G hpos hweak hx hx₀ hxx hρ hsupport hdemand hcapacity
  have hD := tendsto_slope_over_coverage_atTop P hn p weight
    (fun m => measurable_allocation_rivals hn (hx m)) hw
    (fun m rivals => allocation_bounds hn rivals (x m))
    (fun m rivals _ => hwb m rivals)
    (show 0 < 1 / ((n : ℝ)^3+1) by positivity)
    (fun m rivals _ => hwgap m rivals) hrare.1 hrare.2
  have hlog : Tendsto (fun m => deriv (Q m) (x m) / Q m (x m)) atTop atTop :=
    tendsto_logarithmicSlope_atTop hx₀ hxx hD
      (Filter.Eventually.of_forall fun m => (hderiv m).deriv)
  refine ⟨hlog, tendsto_surplus_zero_of_firstOrder hrare.1 ?_ hlog⟩
  apply Filter.Eventually.of_forall
  intro m
  apply SupportedFOC.payOnce_first_order_condition (hderiv m).differentiableAt.hasDerivAt
    (hgood m).2.2.1 (hgood m).2.2.2
  exact hIC m

end FCAppendix.PayOnce.DummyRareSuccess
