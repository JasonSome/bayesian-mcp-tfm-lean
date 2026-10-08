import FCAppendix.PayOnce.AnalyticalRareSuccess
import FCAppendix.Probability.TriangularCramerRows

namespace FCAppendix.PayOnce.RareSuccessCoverage
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.CommonList FCAppendix.PayOnce.KernelTailEvent

theorem tail_ratio_to_coverage_rows
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    {n : ℕ} (hn : 0 < n) (p : ∀ m, Ω m → ℝ)
    (hp : ∀ m, Measurable (p m)) (hbound : ∀ m ω, p m ω ∈ Icc (0 : ℝ) 1)
    {δ ε c : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < c)
    (hpos : ∀ᶠ m in atTop, 0 < (P m).real {ω | δ ≤ p m ω})
    (hratio : ∀ᶠ m in atTop,
      (P m).real {ω | ε ≤ p m ω} / (P m).real {ω | δ ≤ p m ω} ≤ exp (-c * N m)) :
    (∀ᶠ m in atTop, 0 < (∫ ω, success n (p m ω) ∂P m) ∧
      (P m).real {ω | ε ≤ p m ω} / (∫ ω, success n (p m ω) ∂P m) ≤
        exp (-c * N m) / success n δ) ∧
    Tendsto (fun m => (P m).real {ω | ε ≤ p m ω} /
      (∫ ω, success n (p m ω) ∂P m)) atTop (𝓝 0) := by
  have hS := success_pos n hn δ hδ hδ1
  have hevent : ∀ᶠ m in atTop, 0 < (∫ ω, success n (p m ω) ∂P m) ∧
      (P m).real {ω | ε ≤ p m ω} / (∫ ω, success n (p m ω) ∂P m) ≤
        exp (-c * N m) / success n δ := by
    filter_upwards [hpos, hratio] with m ht hr
    have hh := ratio_coverage_le_ratio_tail (a := (P m).real {ω | ε ≤ p m ω}) (P m) hn (hp m) (hbound m) hδ hδ1 measureReal_nonneg ht
    exact ⟨hh.1, hh.2.trans (div_le_div_of_nonneg_right hr hS.le)⟩
  refine ⟨hevent, ?_⟩
  have hexp : Tendsto (fun m : ℕ => exp (-c * N m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop hc)
  have hlim : Tendsto (fun m : ℕ => exp (-c * N m) / success n δ) atTop (𝓝 0) := by
    simpa only [zero_div] using hexp.div_const (success n δ)
  apply squeeze_zero' ?_ (hevent.mono fun _ hh => hh.2) hlim
  exact hevent.mono fun _ hh => div_nonneg measureReal_nonneg hh.1.le

end FCAppendix.PayOnce.RareSuccessCoverage

namespace FCAppendix.PayOnce.CompactKernelRareSuccess
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.CommonList FCAppendix.PayOnce.KernelTailEvent
open FCAppendix.PayOnce.KernelLawConvergence

theorem exponential_kernel_tail_ratio_rows
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop) {n : ℕ} (hn : 2 ≤ n)
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀)) {x : ℕ → ℝ} {x₀ δ ε ρ : ℝ}
    (hx : ∀ m, 0 < x m) (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hδ : 0 < δ) (hδε : δ < ε) (hε : ε ≤ 1) (hδρ : δ < ρ)
    (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ρ < ∫ b, compactKernel n b (x₀ * H n δ) ∂(G₀ : Measure ENNReal))
    {r s : ℕ → ℝ}
    (hr : Tendsto (fun m => r m / N m) atTop (𝓝 ρ))
    (hs : Tendsto (fun m => s m / N m) atTop (𝓝 ρ)) :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ m in atTop,
        0 < (Measure.pi fun _ : Fin (N m) => (G m : Measure ENNReal)).real
          {b | ∑ i, compactKernel n (b i) (x m * H n δ) ≤ r m}) ∧
      (∀ᶠ m in atTop,
        (Measure.pi fun _ : Fin (N m) => (G m : Measure ENNReal)).real
          {b | ∑ i, compactKernel n (b i) (x m * H n ε) ≤ s m} /
        (Measure.pi fun _ : Fin (N m) => (G m : Measure ENNReal)).real
          {b | ∑ i, compactKernel n (b i) (x m * H n δ) ≤ r m} ≤ exp (-c * N m)) := by
  let P := fun m => Measure.pi fun _ : Fin (N m) => (G m : Measure ENNReal)
  let X := fun m (i : Fin (N m)) (b : Fin (N m) → ENNReal) => compactKernel n (b i) (x m * H n δ)
  let Y := fun m (i : Fin (N m)) (b : Fin (N m) → ENNReal) => compactKernel n (b i) (x m * H n ε)
  have hδ1 := hδε.le.trans hε
  have hε0 := hδ.le.trans hδε.le
  have hLX (m : ℕ) : 0 < x m * H n δ := mul_pos (hx m) (H_pos n (by omega) δ hδ.le hδ1)
  have hLY (m : ℕ) : 0 < x m * H n ε := mul_pos (hx m) (H_pos n (by omega) ε hε0 hε)
  have hL₀X : 0 < x₀ * H n δ := mul_pos hx₀ (H_pos n (by omega) δ hδ.le hδ1)
  have hL₀Y : 0 < x₀ * H n ε := mul_pos hx₀ (H_pos n (by omega) ε hε0 hε)
  let νX := fun m => (G m).map (continuous_compactKernel hn (hLX m)).measurable.aemeasurable
  let νY := fun m => (G m).map (continuous_compactKernel hn (hLY m)).measurable.aemeasurable
  let μX := G₀.map (continuous_compactKernel hn hL₀X).measurable.aemeasurable
  let μY := G₀.map (continuous_compactKernel hn hL₀Y).measurable.aemeasurable
  have hX : ∀ m i, Measurable (X m i) := fun m i =>
    (continuous_compactKernel hn (hLX m)).measurable.comp (measurable_pi_apply i)
  have hY : ∀ m i, Measurable (Y m i) := fun m i =>
    (continuous_compactKernel hn (hLY m)).measurable.comp (measurable_pi_apply i)
  have hiX : ∀ m, iIndepFun (X m) (P m) := fun m =>
    iIndepFun_pi fun _ => (continuous_compactKernel hn (hLX m)).measurable.aemeasurable
  have hiY : ∀ m, iIndepFun (Y m) (P m) := fun m =>
    iIndepFun_pi fun _ => (continuous_compactKernel hn (hLY m)).measurable.aemeasurable
  have hbX : ∀ m i, ∀ᵐ b ∂P m, X m i b ∈ Icc (0 : ℝ) 1 :=
    fun m i => .of_forall fun b => compactKernel_bounds hn (hLX m) (b i)
  have hbY : ∀ m i, ∀ᵐ b ∂P m, Y m i b ∈ Icc (0 : ℝ) 1 :=
    fun m i => .of_forall fun b => compactKernel_bounds hn (hLY m) (b i)
  have hlawX : ∀ m i, IdentDistrib (X m i) id (P m) (νX m : Measure ℝ) :=
    fun m i => identDistrib_pi_map (G m) (continuous_compactKernel hn (hLX m)).measurable i
  have hlawY : ∀ m i, IdentDistrib (Y m i) id (P m) (νY m : Measure ℝ) :=
    fun m i => identDistrib_pi_map (G m) (continuous_compactKernel hn (hLY m)).measurable i
  have hwX : Tendsto νX atTop (𝓝 μX) :=
    tendsto_transformed_compactKernel_law hn hweak hx hx₀ hxx hδ.le hδ1
  have hwY : Tendsto νY atTop (𝓝 μY) :=
    tendsto_transformed_compactKernel_law hn hweak hx hx₀ hxx hε0 hε
  have hlo : essInf id (μX : Measure ℝ) < ρ := by
    rw [show (μX : Measure ℝ) = (G₀ : Measure ENNReal).map
      (fun b => compactKernel n b (x₀ * H n δ)) from rfl,
      essInf_id_map _ (continuous_compactKernel hn hL₀X).measurable]
    exact (compactKernel_transformed_essInf_le hn _ hx₀ hδ.le hδ1 hsupport).trans_lt hδρ
  have hmean : ρ < ∫ y, y ∂(μX : Measure ℝ) := by
    have he := (identDistrib_map G₀ (continuous_compactKernel hn hL₀X).measurable).integral_eq
    change (∫ b, compactKernel n b (x₀ * H n δ) ∂(G₀ : Measure ENNReal)) =
      ∫ y, y ∂(μX : Measure ℝ) at he
    rwa [← he]
  have hgap : ∀ u : ℝ, u < 0 → cgf id (μY : Measure ℝ) u < cgf id (μX : Measure ℝ) u := by
    intro u hu
    rw [← BoundedLawConvergence.cgf_eq_of_identDistrib
      (identDistrib_map G₀ (continuous_compactKernel hn hL₀X).measurable),
      ← BoundedLawConvergence.cgf_eq_of_identDistrib
      (identDistrib_map G₀ (continuous_compactKernel hn hL₀Y).measurable)]
    exact compactKernel_transformed_cgf_lt hn _ hx₀ hδ.le hδε hε hsupport hu
  obtain ⟨c, hc, hratiob, _⟩ := StrictCramerComparison.exponential_tail_ratio_rows N hNpos hN P P X Y
    hX hY hiX hiY hbX hbY hlawX hlawY hwX hwY hr hs hlo hmean hgap
  have hpos := (TriangularCramer.tendsto_log_tail_rows N hNpos hN P X hX hiX hbX hlawX hwX hr hlo hmean).1
  exact ⟨c, hc, hpos, hratiob⟩

end FCAppendix.PayOnce.CompactKernelRareSuccess

namespace FCAppendix.PayOnce.KernelCoverage
open Filter Topology

theorem tendsto_capacity_sub_div_rows (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {c : ℕ → ℕ} {ρ : ℝ}
    (hc : Tendsto (fun m => (c m : ℝ) / N m) atTop (𝓝 ρ)) (s : ℝ) :
    Tendsto (fun m => ((c m : ℝ) - s) / N m) atTop (𝓝 ρ) := by
  have hi := (tendsto_const_div_atTop_nhds_zero_nat s).comp hN
  simpa only [sub_div, sub_zero, Function.comp_def] using hc.sub hi
end FCAppendix.PayOnce.KernelCoverage

namespace FCAppendix.PayOnce.AnalyticalRareSuccess
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open CommonList AnalyticalKernel KernelLawConvergence CompactKernelRareSuccess
open CompactifiedBidLaws RareSuccessSlope
open scoped BigOperators

theorem exponential_tail_over_coverage_rows
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop) {n : ℕ} (hn : 2 ≤ n)
    (G : ℕ → ProbabilityMeasure ℝ) (hpos : ∀ m, ∀ᵐ b ∂(G m : Measure ℝ), 0 < b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ} (hc : ∀ m, c m ≤ Fintype.card (Fin (N m)) + 1)
    {x : ℕ → ℝ} {x₀ δ ε ρ : ℝ}
    (hx : ∀ m, 0 < x m) (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hδ : 0 < δ) (hδε : δ < ε) (hε : ε ≤ 1) (hδρ : δ < ρ)
    (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ρ < ∫ b, compactKernel n b (x₀ * H n δ) ∂(G₀ : Measure ENNReal))
    (hcapacity : Tendsto (fun m => (c m : ℝ) / N m) atTop (𝓝 ρ)) :
    ∃ a : ℝ, 0 < a ∧
      (∀ᶠ m in atTop,
        0 < coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) (x m) ∧
        (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))).real
          {rivals | ε ≤ allocation n (c m) hn (hc m) rivals (x m)} /
        coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) (x m)
          ≤ exp (-a * N m) / success n δ) ∧
      Tendsto (fun m =>
        (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))).real
          {rivals | ε ≤ allocation n (c m) hn (hc m) rivals (x m)} /
        coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) (x m))
        atTop (𝓝 0) := by
  let P := fun m => Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))
  let p := fun m (rivals : Fin (N m) → ℝ) => allocation n (c m) hn (hc m) rivals (x m)
  have hd (m : ℕ) := allocation_tail_probability_eq (G m) hn (hc m) (hpos m)
    (hx m) hδ (hδε.le.trans hε)
  have he (m : ℕ) := allocation_tail_probability_eq (G m) hn (hc m) (hpos m)
    (hx m) (hδ.trans hδε) hε
  obtain ⟨a, ha, htailpos, htailratio⟩ := exponential_kernel_tail_ratio_rows N hNpos hN hn hweak hx hx₀ hxx
    hδ hδε hε hδρ hsupport hdemand
    (KernelCoverage.tendsto_capacity_sub_div_rows N hN hcapacity δ)
    (KernelCoverage.tendsto_capacity_sub_div_rows N hN hcapacity ε)
  have htpos : ∀ᶠ m in atTop, 0 < (P m).real {rivals | δ ≤ p m rivals} := by
    filter_upwards [htailpos] with m hm
    rw [show (P m).real {rivals | δ ≤ p m rivals} = _ from hd m]
    exact hm
  have hratio : ∀ᶠ m in atTop,
      (P m).real {rivals | ε ≤ p m rivals} / (P m).real {rivals | δ ≤ p m rivals} ≤ exp (-a*N m) := by
    filter_upwards [htailratio] with m hm
    rw [show (P m).real {rivals | δ ≤ p m rivals} = _ from hd m,
      show (P m).real {rivals | ε ≤ p m rivals} = _ from he m]
    exact hm
  exact ⟨a, ha, RareSuccessCoverage.tail_ratio_to_coverage_rows N hN P (by omega) p
    (fun m => measurable_allocation_rivals hn (hc m) (hx m))
    (fun m rivals => allocation_bounds hn (hc m) rivals (x m))
    hδ (hδε.le.trans hε) ha htpos hratio⟩

theorem relative_tails_tendsto_zero_rows
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop) {n : ℕ} (hn : 2 ≤ n)
    (G : ℕ → ProbabilityMeasure ℝ) (hpos : ∀ m, ∀ᵐ b ∂(G m : Measure ℝ), 0 < b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ} (hc : ∀ m, c m ≤ Fintype.card (Fin (N m)) + 1)
    {x : ℕ → ℝ} {x₀ ρ : ℝ}
    (hx : ∀ m, 0 < x m) (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hρ : 0 < ρ) (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ρ < ∫ b, compactKernel n b (x₀ * H n s) ∂(G₀ : Measure ENNReal))
    (hcapacity : Tendsto (fun m => (c m : ℝ) / N m) atTop (𝓝 ρ)) :
    (∀ᶠ m in atTop,
      0 < coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) (x m)) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Tendsto (fun m =>
        (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))).real
          {rivals | ε ≤ allocation n (c m) hn (hc m) rivals (x m)} /
        coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) (x m))
        atTop (𝓝 0) := by
  have hrare (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) := by
    let δ := min ε ρ / 2
    have hδ : 0 < δ := half_pos (lt_min hε hρ)
    have hδε : δ < ε := (half_lt_self (lt_min hε hρ)).trans_le (min_le_left ε ρ)
    have hδρ : δ < ρ := (half_lt_self (lt_min hε hρ)).trans_le (min_le_right ε ρ)
    exact exponential_tail_over_coverage_rows N hNpos hN hn G hpos hweak hc hx hx₀ hxx hδ hδε hε1
      hδρ hsupport (hdemand δ hδ (hδε.le.trans hε1)) hcapacity
  obtain ⟨a, _, he, _⟩ := hrare 1 zero_lt_one le_rfl
  refine ⟨he.mono fun _ hm => hm.1, ?_⟩
  intro ε hε hε1
  obtain ⟨_, _, _, hh⟩ := hrare ε hε hε1
  exact hh

theorem surplus_tendsto_zero_of_supported_IC_rows
    (N : ℕ → ℕ) (hNpos : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop) {n : ℕ} (hn : 2 ≤ n)
    (G : ℕ → ProbabilityMeasure ℝ) (hpos : ∀ m, ∀ᵐ b ∂(G m : Measure ℝ), 0 < b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ} (hc : ∀ m, c m ≤ Fintype.card (Fin (N m)) + 1)
    {T : ℕ → Set ℝ} {x w : ℕ → ℝ} {x₀ ρ : ℝ}
    (hgood : ∀ m, x m ∈ regularSupportedSet (ι := Fin (N m)) n (c m) (G m : Measure ℝ) (T m))
    (hx₀ : 0 < x₀) (hxx : Tendsto x atTop (𝓝 x₀))
    (hρ : 0 < ρ) (hsupport : ENNReal.ofReal x₀ ∈ (G₀ : Measure ENNReal).support)
    (hdemand : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ρ < ∫ b, compactKernel n b (x₀ * H n s) ∂(G₀ : Measure ENNReal))
    (hcapacity : Tendsto (fun m => (c m : ℝ) / N m) atTop (𝓝 ρ))
    (hIC : ∀ m y, y ∈ T m →
      (w m-y) * coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) y ≤
      (w m-x m) * coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) (x m)) :
    Tendsto (fun m =>
      deriv (coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ)))) (x m) /
      coverage n (c m) hn (hc m) (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) (x m)) atTop atTop ∧
    Tendsto (fun m => w m-x m) atTop (𝓝 0) := by
  let P := fun m => Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))
  let p := fun m (rivals : Fin (N m) → ℝ) => allocation n (c m) hn (hc m) rivals (x m)
  let Q := fun m => coverage n (c m) hn (hc m) (P m)
  have hx : ∀ m, 0 < x m := fun m => (hgood m).1
  choose weight hw hwb hwgap _ hderiv using fun m =>
    exists_measurable_weight_coverage_derivative hn (hc m) (P m) (hx m) (hgood m).2.1
  have hrare := relative_tails_tendsto_zero_rows N hNpos hN hn G hpos hweak hc hx hx₀ hxx hρ hsupport hdemand hcapacity
  have hD := tendsto_slope_over_coverage_atTop P hn p weight
    (fun m => measurable_allocation_rivals hn (hc m) (hx m)) hw
    (fun m rivals => allocation_bounds hn (hc m) rivals (x m))
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

end FCAppendix.PayOnce.AnalyticalRareSuccess
