import FCAppendix.PayOnce.CompactKernelRareSuccess

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.CommonList FCAppendix.PayOnce.KernelTailEvent
open FCAppendix.PayOnce.KernelLawConvergence
open FCAppendix.PayOnce.CompactKernelRareSuccess

noncomputable def demand (n : ℕ) (G : Measure ENNReal) (L : ℝ) : ℝ :=
  ∫ b, compactKernel n b L ∂G

theorem demand_antitone {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L T : ℝ}
    (hL : 0 < L) (hT : 0 < T) (hLT : L ≤ T) : demand n G T ≤ demand n G L :=
  integral_mono (integrable_compactKernel hn G hT) (integrable_compactKernel hn G hL)
    (compactKernel_antitone_price hn hL hT hLT)

theorem compactKernel_endpoint_of_eq {n : ℕ} (hn : 2 ≤ n) {L T : ℝ}
    (hL : 0 < L) (hLT : L < T) (b : ENNReal)
    (he : compactKernel n b L = compactKernel n b T) :
    compactKernel n b L = 0 ∨ compactKernel n b L = 1 := by
  by_cases hb : b = ⊤
  · exact Or.inr (by simp [hb])
  · simp only [compactKernel, if_neg hb] at he ⊢
    by_cases hbl : b.toReal ≤ L
    · exact Or.inl (kernel_of_le n hbl)
    · have hbp : 0 < b.toReal := hL.trans (lt_of_not_ge hbl)
      have hT : 0 < T := hL.trans hLT
      have hp := scalarThreshold_kernel n hn hbp hL
      by_contra hnot
      have hp0 : 0 < kernel n b.toReal L :=
        lt_of_le_of_ne hp.1 (fun h => hnot (Or.inl h.symm))
      have hp1 : kernel n b.toReal L < 1 :=
        lt_of_le_of_ne hp.2.1 (fun h => hnot (Or.inr h))
      have hq := scalarThreshold_kernel n hn hbp hT
      have ha := hp.2.2.2.2 hp0 hp1
      have hb := hq.2.2.2.2 (he ▸ hp0) (he ▸ hp1)
      rw [← he] at hb
      exact hLT.ne (ha.symm.trans hb)

theorem ae_compactKernel_eq_of_demand_eq {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L T : ℝ}
    (hL : 0 < L) (hT : 0 < T) (hLT : L ≤ T)
    (he : demand n G L = demand n G T) :
    (fun b => compactKernel n b L) =ᵐ[G] fun b => compactKernel n b T := by
  have hd : ∀ᵐ b ∂G, 0 ≤ compactKernel n b L - compactKernel n b T :=
    .of_forall fun b => sub_nonneg.mpr (compactKernel_antitone_price hn hL hT hLT b)
  have hi := (integrable_compactKernel hn G hL).sub (integrable_compactKernel hn G hT)
  have hz : (∫ b, compactKernel n b L - compactKernel n b T ∂G) = 0 := by
    rw [integral_sub (integrable_compactKernel hn G hL) (integrable_compactKernel hn G hT)]
    exact sub_eq_zero.mpr he
  have hae := (integral_eq_zero_iff_of_nonneg_ae hd hi).mp hz
  exact hae.mono fun _ h => sub_eq_zero.mp h

theorem ae_endpoints_of_two_roots {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L T ρ : ℝ}
    (hL : 0 < L) (hLT : L < T)
    (hrootL : demand n G L = ρ) (hrootT : demand n G T = ρ) :
    ∀ᵐ b ∂G, compactKernel n b L = 0 ∨ compactKernel n b L = 1 := by
  have he := ae_compactKernel_eq_of_demand_eq hn G hL (hL.trans hLT) hLT.le
    (hrootL.trans hrootT.symm)
  exact he.mono fun b hb => compactKernel_endpoint_of_eq hn hL hLT b hb

theorem saturated_mass_eq_of_two_roots {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L T ρ : ℝ}
    (hL : 0 < L) (hLT : L < T)
    (hrootL : demand n G L = ρ) (hrootT : demand n G T = ρ) :
    G.real {b | compactKernel n b L = 1} = ρ := by
  let E := {b | compactKernel n b L = 1}
  have hE : MeasurableSet E := measurableSet_eq_fun
    (continuous_compactKernel hn hL).measurable measurable_const
  have he : (fun b => compactKernel n b L) =ᵐ[G] E.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_endpoints_of_two_roots hn G hL hLT hrootL hrootT] with b hb
    rcases hb with hb | hb <;> simp [E, hb]
  have hi := integral_congr_ae he
  rw [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one] at hi
  exact hi.symm.trans hrootL

theorem root_unique_of_no_saturated_mass {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L T ρ : ℝ}
    (hρ : 0 < ρ) (hL : 0 < L) (hT : 0 < T)
    (hrootL : demand n G L = ρ) (hrootT : demand n G T = ρ)
    (hno : G.real {b | compactKernel n b L = 1} = 0) : L = T := by
  rcases lt_trichotomy L T with h | h | h
  · have hh := saturated_mass_eq_of_two_roots hn G hL h hrootL hrootT
    rw [hno] at hh
    exact False.elim (hρ.ne' hh.symm)
  · exact h
  · have hh := saturated_mass_eq_of_two_roots hn G hT h hrootT hrootL
    have he := ae_compactKernel_eq_of_demand_eq hn G hT hL h.le (hrootT.trans hrootL.symm)
    have hsets : {b | compactKernel n b T = 1} =ᵐ[G] {b | compactKernel n b L = 1} :=
      he.mono fun b hb => congrArg (fun p : ℝ => p = 1) hb
    have hm := measureReal_congr hsets
    rw [hno, hh] at hm
    exact False.elim (hρ.ne' hm)

noncomputable def boundedKernel {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) :
    BoundedContinuousFunction ENNReal ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun b => compactKernel n b L)
    (continuous_compactKernel hn hL) 1 (fun b => by
      rw [Real.norm_eq_abs, abs_of_nonneg (compactKernel_bounds hn hL b).1]
      exact (compactKernel_bounds hn hL b).2)

theorem tendsto_demand {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {G : α → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G l (𝓝 G₀)) {L : α → ℝ} {T : ℝ}
    (hL : ∀ a, 0 < L a) (hT : 0 < T) (hLT : Tendsto L l (𝓝 T)) :
    Tendsto (fun a => demand n (G a : Measure ENNReal) (L a)) l
      (𝓝 (demand n (G₀ : Measure ENNReal) T)) :=
  tendsto_integral_varying_test hweak (fun a => boundedKernel hn (hL a))
    (boundedKernel hn hT) (tendstoUniformly_compactKernel hn hT hLT)

theorem demand_price_difference {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G] {L T ℓ : ℝ}
    (hℓ : 0 < ℓ) (hL : ℓ ≤ L) (hT : ℓ ≤ T) :
    |demand n G L - demand n G T| ≤ ((n : ℝ) / ℓ) * |L - T| := by
  have hh := norm_integral_le_of_norm_le_const (μ := G)
    (f := fun b => compactKernel n b L - compactKernel n b T)
    (C := ((n : ℝ) / ℓ) * |L - T|)
    (.of_forall fun b => by
      simpa only [Real.norm_eq_abs] using compactKernel_price_difference hn hℓ hL hT b)
  rw [integral_sub (integrable_compactKernel hn G (hℓ.trans_le hL))
    (integrable_compactKernel hn G (hℓ.trans_le hT)), probReal_univ, mul_one, Real.norm_eq_abs] at hh
  exact hh

theorem continuousOn_demand {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal) :
    ContinuousOn (demand n (G : Measure ENNReal)) (Ioi (0 : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_iff_continuousAt.mpr
  intro L
  exact tendsto_demand hn tendsto_const_nhds (fun T : Ioi (0 : ℝ) => T.property)
    L.property continuous_subtype_val.continuousAt

theorem tendsto_compactKernel_zero {α : Type*} {l : Filter α} {n : ℕ} (hn : 2 ≤ n)
    {L : α → ℝ} (hL : ∀ a, 0 < L a) (hL0 : Tendsto L l (𝓝 0)) (b : ENNReal) :
    Tendsto (fun a => compactKernel n b (L a)) l (𝓝 (if b = 0 then 0 else 1)) := by
  by_cases hb0 : b = 0
  · subst b
    have he : (fun a => compactKernel n 0 (L a)) = fun _ => (0 : ℝ) := by
      funext a
      simp only [compactKernel, ENNReal.zero_ne_top, if_false, ENNReal.toReal_zero]
      exact kernel_of_le n (hL a).le
    rw [he]
    simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 (0 : ℝ)))
  · rw [if_neg hb0]
    by_cases hbtop : b = ⊤
    · simp only [hbtop, compactKernel_top]
      exact tendsto_const_nhds
    · have hbp : 0 < b.toReal := ENNReal.toReal_pos hb0 hbtop
      have he : ∀ᶠ a in l, compactKernel n b (L a) = 1 := by
        filter_upwards [(hL0.const_mul (n : ℝ)).eventually_le_const (by simpa using hbp)] with a ha
        rw [compactKernel, if_neg hbtop]
        exact kernel_of_ge n hn (hL a) ha
      exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)

theorem tendsto_compactKernel_atTop {α : Type*} {l : Filter α} {n : ℕ}
    {L : α → ℝ} (hL : Tendsto L l atTop) (b : ENNReal) :
    Tendsto (fun a => compactKernel n b (L a)) l (𝓝 (if b = ⊤ then 1 else 0)) := by
  by_cases hb : b = ⊤
  · simp only [hb, compactKernel_top]
    exact tendsto_const_nhds
  · rw [if_neg hb]
    have he : ∀ᶠ a in l, compactKernel n b (L a) = 0 := by
      filter_upwards [hL.eventually_ge_atTop b.toReal] with a ha
      rw [compactKernel, if_neg hb]
      exact kernel_of_le n ha
    exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)

theorem tendsto_demand_zero {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G]
    {L : ℕ → ℝ} (hL : ∀ m, 0 < L m) (hL0 : Tendsto L atTop (𝓝 0)) :
    Tendsto (fun m => demand n G (L m)) atTop (𝓝 (G.real ({0}ᶜ))) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := G) (bound := fun _ => (1 : ℝ))
    (fun m => (continuous_compactKernel hn (hL m)).aestronglyMeasurable)
    (integrable_const 1)
    (fun m => Filter.Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs, abs_of_nonneg (compactKernel_bounds hn (hL m) b).1]
      exact (compactKernel_bounds hn (hL m) b).2)
    (Filter.Eventually.of_forall fun b => tendsto_compactKernel_zero hn hL hL0 b)
  have he : (fun b : ENNReal => if b = 0 then (0 : ℝ) else 1) =
      (({0}ᶜ : Set ENNReal).indicator (fun _ => (1 : ℝ))) := by
    funext b
    simp [indicator, ite_not]
  rw [he, integral_indicator (measurableSet_singleton (0 : ENNReal)).compl,
    setIntegral_const, smul_eq_mul, mul_one] at hh
  exact hh

theorem tendsto_demand_atTop {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ENNReal) [IsProbabilityMeasure G]
    {L : ℕ → ℝ} (hLpos : ∀ m, 0 < L m) (hL : Tendsto L atTop atTop) :
    Tendsto (fun m => demand n G (L m)) atTop (𝓝 (G.real {⊤})) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := G) (bound := fun _ => (1 : ℝ))
    (fun m => (continuous_compactKernel hn (hLpos m)).aestronglyMeasurable)
    (integrable_const 1)
    (fun m => Filter.Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs, abs_of_nonneg (compactKernel_bounds hn (hLpos m) b).1]
      exact (compactKernel_bounds hn (hLpos m) b).2)
    (Filter.Eventually.of_forall fun b => tendsto_compactKernel_atTop hL b)
  have he : (fun b : ENNReal => if b = ⊤ then (1 : ℝ) else 0) =
      (({⊤} : Set ENNReal).indicator (fun _ => (1 : ℝ))) := by
    funext b
    simp [indicator]
  rw [he, integral_indicator (measurableSet_singleton (⊤ : ENNReal)),
    setIntegral_const, smul_eq_mul, mul_one] at hh
  exact hh

theorem exists_capacity_root {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {ρ : ℝ} (hinfty : (G : Measure ENNReal).real {⊤} < ρ)
    (hpos : ρ < (G : Measure ENNReal).real ({0}ᶜ)) :
    ∃ L : ℝ, 0 < L ∧ demand n (G : Measure ENNReal) L = ρ := by
  let small := fun m : ℕ => 1 / ((m : ℝ) + 1)
  let large := fun m : ℕ => (m : ℝ) + 1
  have hsmall : ∀ m, 0 < small m := fun m => by dsimp [small]; positivity
  have hlarge : ∀ m, 0 < large m := fun m => by dsimp [large]; positivity
  have hs0 : Tendsto small atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlTop : Tendsto large atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨m, hm⟩ := ((tendsto_demand_zero hn (G : Measure ENNReal) hsmall hs0).eventually_const_lt hpos).exists
  obtain ⟨k, hk, hmk⟩ := (((tendsto_demand_atTop hn (G : Measure ENNReal) hlarge hlTop).eventually_lt_const hinfty).and
    (hlTop.eventually_ge_atTop (small m))).exists
  have hsub : Icc (small m) (large k) ⊆ Ioi (0 : ℝ) :=
    fun L hL => (hsmall m).trans_le hL.1
  obtain ⟨L, hL, hd⟩ := intermediate_value_Icc' hmk
    ((continuousOn_demand hn G).mono hsub) ⟨hk.le, hm.le⟩
  exact ⟨L, (hsmall m).trans_le hL.1, hd⟩

end FCAppendix.PayOnce.KernelDemand
