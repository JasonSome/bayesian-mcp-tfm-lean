import FCAppendix.PayOnce.FocalPrice
import FCAppendix.Probability.TriangularBoundedCLT

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList Bayes KernelTailEvent
open scoped BigOperators

theorem focalPrice_probability_sandwich {N n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] (b : ℝ) (hb : 0 < b)
    {T : ℝ} (hT : 0 < T) :
    μ.real {r | (∑ i, kernel n (r i) T) ≤ (c:ℝ)-2} -
        μ.real {r | Fintype.card (Active r)+1 < c} ≤
      μ.real {r | focalPrice n c hn b r ≤ T} ∧
    μ.real {r | focalPrice n c hn b r ≤ T} ≤
      μ.real {r | (∑ i, kernel n (r i) T) ≤ (c:ℝ)} := by
  have hs := focalPrice_event_sandwich (N := N) (c := c) hn b hb hT
  have hsub : {r : Fin N → ℝ | (∑ i, kernel n (r i) T) ≤ (c:ℝ)-2} ⊆
      {r | focalPrice n c hn b r ≤ T} ∪ {r | Fintype.card (Active r)+1 < c} := by
    intro r hr
    by_cases hfill : Fintype.card (Active r)+1 < c
    · exact Or.inr hfill
    · exact Or.inl (hs.1 ⟨hr,hfill⟩)
  have hlo := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  exact ⟨by linarith,measureReal_mono hs.2⟩

theorem focalPrice_probability_uniform_of_sum_limits
    {N C : ℕ → ℕ} {n : ℕ} (hn : 2 ≤ n)
    (μ : (m : ℕ) → Measure (Fin (N m) → ℝ)) [∀ m, IsFiniteMeasure (μ m)]
    (T : ℕ → ℝ) (hT : ∀ᶠ m in atTop, 0 < T m) {q : ℝ}
    (hlo : Tendsto (fun m => (μ m).real
      {r | (∑ i, kernel n (r i) (T m)) ≤ (C m:ℝ)-2}) atTop (𝓝 q))
    (hhi : Tendsto (fun m => (μ m).real
      {r | (∑ i, kernel n (r i) (T m)) ≤ (C m:ℝ)}) atTop (𝓝 q))
    (hunder : Tendsto (fun m => (μ m).real
      {r | Fintype.card (Active r)+1 < C m}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ b : ℝ, 0 < b →
      |(μ m).real {r | focalPrice n (C m) hn b r ≤ T m}-q| < ε := by
  intro ε hε
  have hlower : Tendsto (fun m => (μ m).real
      {r | (∑ i, kernel n (r i) (T m)) ≤ (C m:ℝ)-2} -
        (μ m).real {r | Fintype.card (Active r)+1 < C m}) atTop (𝓝 q) := by
    simpa only [sub_zero] using hlo.sub hunder
  have hevlo := hlower.eventually_const_lt (show q-ε < q by linarith)
  have hevhi := hhi.eventually_lt_const (show q < q+ε by linarith)
  filter_upwards [hT,hevlo,hevhi] with m hm hml hmu b hb
  obtain ⟨hl,hu⟩ := focalPrice_probability_sandwich hn (μ m) b hb hm
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem iid_kernel_sum_probability_le_tendsto_gaussian
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ) (T : ℕ → ℝ)
    (hT : ∀ᶠ m in atTop, 0 < T m) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (fun b => kernel n b (T m))
      (G m : Measure ℝ)) atTop (𝓝 v)) (a : ℕ → ℝ) {z : ℝ}
    (ha : Tendsto (fun m => (a m-(N m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((N m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z)) :
    Tendsto (fun m => (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))).real
      {r | (∑ i, kernel n (r i) (T m)) ≤ a m}) atTop (𝓝 (cdf (gaussianReal 0 1) z)) := by
  let f := fun m b => kernel n b (T m)
  let x := fun m => (a m-(N m:ℝ)*(∫ b, f m b ∂(G m : Measure ℝ))) /
    Real.sqrt ((N m:ℝ)*variance (f m) (G m : Measure ℝ))
  have hσ := Probability.iid_totalStandardDeviation_tendsto_atTop
    (fun m => (G m : Measure ℝ)) f N hN hv hvar
  have hclt : Tendsto (fun m => (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))).real
      {r | Probability.iidStandardizedSum (G m : Measure ℝ) (f m) (N m) r ≤ x m})
      atTop (𝓝 (cdf (gaussianReal 0 1) z)) := by
    obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp hT
    apply (tendsto_add_atTop_iff_nat m₀).mp
    exact Probability.iid_unitInterval_probability_le_tendsto_gaussian
      (fun m => (G (m+m₀) : Measure ℝ)) (fun m => f (m+m₀)) (fun m => N (m+m₀))
      (fun m => (continuous_kernel_bid hn (hm₀ (m+m₀) (by omega))).measurable)
      (fun m => Eventually.of_forall (kernel_bounds hn (hm₀ (m+m₀) (by omega))))
      (hN.comp (tendsto_add_atTop_nat m₀)) hv (hvar.comp (tendsto_add_atTop_nat m₀))
      (ha.comp (tendsto_add_atTop_nat m₀))
  apply hclt.congr'
  filter_upwards [hσ.eventually_gt_atTop 0] with m hm
  congr 1
  ext r
  change Probability.iidStandardizedSum (G m : Measure ℝ) (f m) (N m) r ≤ x m ↔
    (∑ i, f m (r i)) ≤ a m
  rw [Probability.iidStandardizedSum_eq]
  dsimp only [x]
  rw [div_le_div_iff_of_pos_right hm]
  exact sub_le_sub_iff_right _

theorem focalPrice_probability_uniform_of_kernel_CLT
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ) (T : ℕ → ℝ)
    (hT : ∀ᶠ m in atTop, 0 < T m) (N C : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (fun b => kernel n b (T m))
      (G m : Measure ℝ)) atTop (𝓝 v)) {z : ℝ}
    (hthreshold : Tendsto (fun m => ((C m:ℝ)-(N m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((N m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z))
    (hunder : Tendsto (fun m => (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))).real
      {r | Fintype.card (Active r)+1 < C m}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ b : ℝ, 0 < b →
      |(Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))).real
        {r | focalPrice n (C m) hn b r ≤ T m}-cdf (gaussianReal 0 1) z| < ε := by
  have hσ := Probability.iid_totalStandardDeviation_tendsto_atTop
    (fun m => (G m : Measure ℝ)) (fun m b => kernel n b (T m)) N hN hv hvar
  have hmargin : Tendsto (fun m => (2:ℝ) /
      Real.sqrt ((N m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hσ
  have hthreshold2 : Tendsto (fun m => ((C m:ℝ)-2-
      (N m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((N m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z) := by
    have hh := hthreshold.sub hmargin
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun m => by ring
  have hlo := iid_kernel_sum_probability_le_tendsto_gaussian hn G T hT N hN hv hvar
    (fun m => (C m:ℝ)-2) hthreshold2
  have hhi := iid_kernel_sum_probability_le_tendsto_gaussian hn G T hT N hN hv hvar
    (fun m => (C m:ℝ)) hthreshold
  exact focalPrice_probability_uniform_of_sum_limits hn
    (fun m => Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))) T hT hlo hhi hunder

theorem cdf_focalPrice_eq {N n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ] (b T : ℝ) :
    cdf (μ.map (focalPrice n c hn b)) T = μ.real {r | focalPrice n c hn b r ≤ T} := by
  have hm := measurable_focalPrice (N := N) (c := c) hn b
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hm.aemeasurable
  rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
  rfl

theorem focalPrice_cdf_tendstoUniformlyOn
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ) (T : ℕ → ℝ)
    (hT : ∀ᶠ m in atTop, 0 < T m) (N C : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (fun b => kernel n b (T m))
      (G m : Measure ℝ)) atTop (𝓝 v)) {z : ℝ}
    (hthreshold : Tendsto (fun m => ((C m:ℝ)-(N m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((N m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z))
    (hunder : Tendsto (fun m => (Measure.pi (fun _ : Fin (N m) => (G m : Measure ℝ))).real
      {r | Fintype.card (Active r)+1 < C m}) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun m b => cdf ((Measure.pi (fun _ : Fin (N m) =>
      (G m : Measure ℝ))).map (focalPrice n (C m) hn b)) (T m))
      (fun _ => cdf (gaussianReal 0 1) z) atTop (Ioi (0:ℝ)) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [focalPrice_probability_uniform_of_kernel_CLT hn G T hT N C hN
    hv hvar hthreshold hunder ε hε] with m hm b hb
  rw [Real.dist_eq,cdf_focalPrice_eq,abs_sub_comm]
  exact hm b hb

end FCAppendix.PayOnce.DummyKernel
