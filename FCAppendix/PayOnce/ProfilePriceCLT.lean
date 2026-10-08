import FCAppendix.PayOnce.FocalPriceCLT

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList Bayes KernelTailEvent
open scoped BigOperators

noncomputable def sampleProfilePrice {m : ℕ} (n c : ℕ) (hn : 2 ≤ n) (r : Fin m → ℝ) : ℝ :=
  if hm : 0 < m then profilePrice n c hn hm r else 0

@[simp] theorem sampleProfilePrice_eq {m n c : ℕ} (hn : 2 ≤ n) (hm : 0 < m) :
    sampleProfilePrice (m := m) n c hn = profilePrice n c hn hm := by
  funext r
  simp only [sampleProfilePrice,dif_pos hm]

theorem measurable_sampleProfilePrice {m n c : ℕ} (hn : 2 ≤ n) :
    Measurable (sampleProfilePrice (m := m) n c hn) := by
  by_cases hm : 0 < m
  · rw [sampleProfilePrice_eq hn hm]
    exact measurable_profilePrice hn hm
  · have he : sampleProfilePrice (m := m) n c hn = fun _ => 0 := by
      funext r
      simp only [sampleProfilePrice,dif_neg hm]
    rw [he]
    exact measurable_const

theorem profilePrice_event_sandwich {m n c : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    {T : ℝ} (hT : 0 < T) :
    {r : Fin m → ℝ | (∑ i, kernel n (r i) T) ≤ (c:ℝ)-1} \
      {r | Fintype.card (Active r) < c} ⊆ {r | profilePrice n c hn hm r ≤ T} ∧
    {r : Fin m → ℝ | profilePrice n c hn hm r ≤ T} ⊆
      {r | (∑ i, kernel n (r i) T) ≤ (c:ℝ)} := by
  constructor
  · intro r hr
    obtain ⟨hL,_,hcap⟩ := profilePrice_spec (c := c) hn hm r
    rw [min_eq_left (Nat.le_of_not_gt hr.2)] at hcap
    have hlt : profilePrice n c hn hm r < T := by
      by_contra h
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        kernel_antitone_price hn hT hL (le_of_not_gt h) (b := r i))
      have hsmall : (∑ i, kernel n (r i) T) ≤ (c:ℝ)-1 := hr.1
      linarith
    exact hlt.le
  · intro r hr
    obtain ⟨hL,_,hcap⟩ := profilePrice_spec (c := c) hn hm r
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      kernel_antitone_price hn hL hT hr (b := r i))
    have hc : ((min c (Fintype.card (Active r)):ℕ):ℝ) ≤ c := Nat.cast_le.mpr (min_le_left _ _)
    change (∑ i, kernel n (r i) T) ≤ (c:ℝ)
    linarith

theorem profilePrice_probability_sandwich {m n c : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    μ.real {r | (∑ i, kernel n (r i) T) ≤ (c:ℝ)-1} -
      μ.real {r | Fintype.card (Active r) < c} ≤
        μ.real {r | profilePrice n c hn hm r ≤ T} ∧
    μ.real {r | profilePrice n c hn hm r ≤ T} ≤
      μ.real {r | (∑ i, kernel n (r i) T) ≤ (c:ℝ)} := by
  have hs := profilePrice_event_sandwich (c := c) hn hm hT
  have hsub : {r : Fin m → ℝ | (∑ i, kernel n (r i) T) ≤ (c:ℝ)-1} ⊆
      {r | profilePrice n c hn hm r ≤ T} ∪ {r | Fintype.card (Active r) < c} := by
    intro r hr
    by_cases hbad : Fintype.card (Active r) < c
    · exact Or.inr hbad
    · exact Or.inl (hs.1 ⟨hr,hbad⟩)
  have hlo := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  exact ⟨by linarith,measureReal_mono hs.2⟩

theorem sampleProfilePrice_probability_tendsto_of_sum_limits
    {M C : ℕ → ℕ} {n : ℕ} (hn : 2 ≤ n)
    (μ : (m : ℕ) → Measure (Fin (M m) → ℝ)) [∀ m, IsFiniteMeasure (μ m)]
    (hM : Tendsto M atTop atTop) (T : ℕ → ℝ) (hT : ∀ᶠ m in atTop, 0 < T m) {q : ℝ}
    (hlo : Tendsto (fun m => (μ m).real
      {r | (∑ i, kernel n (r i) (T m)) ≤ (C m:ℝ)-1}) atTop (𝓝 q))
    (hhi : Tendsto (fun m => (μ m).real
      {r | (∑ i, kernel n (r i) (T m)) ≤ (C m:ℝ)}) atTop (𝓝 q))
    (hunder : Tendsto (fun m => (μ m).real
      {r | Fintype.card (Active r) < C m}) atTop (𝓝 0)) :
    Tendsto (fun m => (μ m).real {r | sampleProfilePrice n (C m) hn r ≤ T m}) atTop (𝓝 q) := by
  have hlower : Tendsto (fun m => (μ m).real
      {r | (∑ i, kernel n (r i) (T m)) ≤ (C m:ℝ)-1} -
        (μ m).real {r | Fintype.card (Active r) < C m}) atTop (𝓝 q) := by
    simpa only [sub_zero] using hlo.sub hunder
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hhi
  · filter_upwards [hM.eventually_gt_atTop 0,hT] with m hm ht
    simpa only [sampleProfilePrice_eq hn hm] using (profilePrice_probability_sandwich hn hm (μ m) ht).1
  · filter_upwards [hM.eventually_gt_atTop 0,hT] with m hm ht
    simpa only [sampleProfilePrice_eq hn hm] using (profilePrice_probability_sandwich hn hm (μ m) ht).2

theorem sampleProfilePrice_probability_tendsto_of_kernel_CLT
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ) (T : ℕ → ℝ)
    (hT : ∀ᶠ m in atTop, 0 < T m) (M C : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (fun b => kernel n b (T m))
      (G m : Measure ℝ)) atTop (𝓝 v)) {z : ℝ}
    (hthreshold : Tendsto (fun m => ((C m:ℝ)-(M m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((M m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z))
    (hunder : Tendsto (fun m => (Measure.pi (fun _ : Fin (M m) => (G m : Measure ℝ))).real
      {r | Fintype.card (Active r) < C m}) atTop (𝓝 0)) :
    Tendsto (fun m => (Measure.pi (fun _ : Fin (M m) => (G m : Measure ℝ))).real
      {r | sampleProfilePrice n (C m) hn r ≤ T m}) atTop (𝓝 (cdf (gaussianReal 0 1) z)) := by
  have hσ := Probability.iid_totalStandardDeviation_tendsto_atTop
    (fun m => (G m : Measure ℝ)) (fun m b => kernel n b (T m)) M hM hv hvar
  have hmargin : Tendsto (fun m => (1:ℝ) /
      Real.sqrt ((M m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hσ
  have hthreshold1 : Tendsto (fun m => ((C m:ℝ)-1-
      (M m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((M m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z) := by
    have hh := hthreshold.sub hmargin
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun m => by ring
  exact sampleProfilePrice_probability_tendsto_of_sum_limits hn
    (fun m => Measure.pi (fun _ : Fin (M m) => (G m : Measure ℝ))) hM T hT
    (iid_kernel_sum_probability_le_tendsto_gaussian hn G T hT M hM hv hvar
      (fun m => (C m:ℝ)-1) hthreshold1)
    (iid_kernel_sum_probability_le_tendsto_gaussian hn G T hT M hM hv hvar
      (fun m => (C m:ℝ)) hthreshold) hunder

theorem profilePrice_probability_tendsto_of_kernel_CLT
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ) (T : ℕ → ℝ)
    (hT : ∀ᶠ m in atTop, 0 < T m) (M C : ℕ → ℕ) (hm : ∀ m, 0 < M m)
    (hM : Tendsto M atTop atTop) {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (fun b => kernel n b (T m))
      (G m : Measure ℝ)) atTop (𝓝 v)) {z : ℝ}
    (hthreshold : Tendsto (fun m => ((C m:ℝ)-(M m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((M m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z))
    (hunder : Tendsto (fun m => (Measure.pi (fun _ : Fin (M m) => (G m : Measure ℝ))).real
      {r | Fintype.card (Active r) < C m}) atTop (𝓝 0)) :
    Tendsto (fun m => (Measure.pi (fun _ : Fin (M m) => (G m : Measure ℝ))).real
      {r | profilePrice n (C m) hn (hm m) r ≤ T m}) atTop (𝓝 (cdf (gaussianReal 0 1) z)) := by
  simpa only [sampleProfilePrice_eq hn (hm _)] using
    sampleProfilePrice_probability_tendsto_of_kernel_CLT hn G T hT M C hM hv hvar hthreshold hunder

theorem cdf_sampleProfilePrice_eq {m n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] (T : ℝ) :
    cdf (μ.map (sampleProfilePrice n c hn)) T = μ.real {r | sampleProfilePrice n c hn r ≤ T} := by
  have hm := measurable_sampleProfilePrice (m := m) (c := c) hn
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hm.aemeasurable
  rw [cdf_eq_real,map_measureReal_apply hm measurableSet_Iic]
  rfl

theorem sampleProfilePrice_cdf_tendsto_of_kernel_CLT
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ) (T : ℕ → ℝ)
    (hT : ∀ᶠ m in atTop, 0 < T m) (M C : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (fun b => kernel n b (T m))
      (G m : Measure ℝ)) atTop (𝓝 v)) {z : ℝ}
    (hthreshold : Tendsto (fun m => ((C m:ℝ)-(M m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((M m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z))
    (hunder : Tendsto (fun m => (Measure.pi (fun _ : Fin (M m) => (G m : Measure ℝ))).real
      {r | Fintype.card (Active r) < C m}) atTop (𝓝 0)) :
    Tendsto (fun m => cdf ((Measure.pi (fun _ : Fin (M m) =>
      (G m : Measure ℝ))).map (sampleProfilePrice n (C m) hn)) (T m))
      atTop (𝓝 (cdf (gaussianReal 0 1) z)) := by
  simpa only [cdf_sampleProfilePrice_eq] using
    sampleProfilePrice_probability_tendsto_of_kernel_CLT hn G T hT M C hM hv hvar hthreshold hunder

theorem sampleProfilePrice_cdf_error_tendsto_zero_of_kernel_CLT
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ) (T : ℕ → ℝ)
    (hT : ∀ᶠ m in atTop, 0 < T m) (M C : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (fun b => kernel n b (T m))
      (G m : Measure ℝ)) atTop (𝓝 v)) {z : ℝ}
    (hthreshold : Tendsto (fun m => ((C m:ℝ)-(M m:ℝ)*(∫ b, kernel n b (T m) ∂(G m : Measure ℝ))) /
      Real.sqrt ((M m:ℝ)*variance (fun b => kernel n b (T m)) (G m : Measure ℝ)))
      atTop (𝓝 z))
    (hunder : Tendsto (fun m => (Measure.pi (fun _ : Fin (M m) => (G m : Measure ℝ))).real
      {r | Fintype.card (Active r) < C m}) atTop (𝓝 0)) :
    Tendsto (fun m => |cdf ((Measure.pi (fun _ : Fin (M m) =>
      (G m : Measure ℝ))).map (sampleProfilePrice n (C m) hn)) (T m) -
        cdf (gaussianReal 0 1) z|) atTop (𝓝 0) := by
  have hh := sampleProfilePrice_cdf_tendsto_of_kernel_CLT hn G T hT M C hM hv hvar hthreshold hunder
  simpa only [sub_self,abs_zero] using (hh.sub_const (cdf (gaussianReal 0 1) z)).abs

theorem sampleProfilePrice_standardized_event {m n c : ℕ} (hn : 2 ≤ n)
    (center z : ℝ) {s : ℝ} (hs : 0 < s) :
    {r : Fin m → ℝ | (sampleProfilePrice n c hn r-center)/s ≤ z} =
      {r | sampleProfilePrice n c hn r ≤ center+s*z} := by
  ext r
  simp only [mem_setOf_eq,div_le_iff₀ hs]
  constructor <;> intro h <;> nlinarith

theorem cdf_standardized_sampleProfilePrice_eq {m n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (center z : ℝ) {s : ℝ} (hs : 0 < s) :
    cdf (μ.map (fun r => (sampleProfilePrice n c hn r-center)/s)) z =
      μ.real {r | sampleProfilePrice n c hn r ≤ center+s*z} := by
  have hm := ((measurable_sampleProfilePrice (m := m) (c := c) hn).sub_const center).div_const s
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hm.aemeasurable
  rw [cdf_eq_real,map_measureReal_apply hm measurableSet_Iic]
  exact congrArg μ.real (sampleProfilePrice_standardized_event hn center z hs)

end FCAppendix.PayOnce.DummyKernel
