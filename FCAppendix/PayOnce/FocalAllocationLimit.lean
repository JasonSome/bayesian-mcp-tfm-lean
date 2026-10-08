import FCAppendix.PayOnce.FocalAllocationBounds
import FCAppendix.PayOnce.RivalDemandLimit
import FCAppendix.PayOnce.CoverageDerivative

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open KernelLawConvergence KernelTailEvent CompactifiedBidLaws
open scoped BigOperators

theorem tendsto_focal_allocation_kernel_error
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 < b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ} (hc : ∀ t, c t ≤ Fintype.card (Fin (N t))+1)
    {ρ L : ℝ} (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T, 0 < T → KernelDemand.demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hcapacity : Tendsto (fun t => (c t:ℝ)/N t) atTop (𝓝 ρ))
    (x : ℕ → ℝ) (hx : ∀ t, 0 < x t) :
    Tendsto (fun t => ∫ r : Fin (N t) → ℝ,
      |allocation n (c t) hn (hc t) r (x t)-kernel n (x t) L|
        ∂Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) atTop (𝓝 0) := by
  let P := fun t => Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))
  have hI t {T : ℝ} (hT : 0 < T) (u : ℝ) : Integrable
      (fun r : Fin (N t) → ℝ => |(∑ j, kernel n (r j) T)/(N t:ℝ)-u|) (P t) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro j _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hT).measurable.comp (measurable_pi_apply j))
      (fun r => (kernel_bounds hn hT (r j)).1) (fun r => (kernel_bounds hn hT (r j)).2)
  have halloc t : Integrable (fun r : Fin (N t) → ℝ =>
      |allocation n (c t) hn (hc t) r (x t)-kernel n (x t) L|) (P t) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    exact UnitInterval.integrable _ _ (measurable_allocation_rivals hn (hc t) (hx t))
      (fun r => (allocation_bounds hn (hc t) r (x t)).1)
      (fun r => (allocation_bounds hn (hc t) r (x t)).2)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K : ℝ := (n:ℝ)/(L/2)
  have hK : 0 < K := div_pos (Nat.cast_pos.mpr (by omega)) (by linarith)
  let η := min (L/4) (ε/(4*K))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηL : η ≤ L/2 := (min_le_left _ _).trans (by linarith)
  have hKη : K*η ≤ ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (L/4) (ε/(4*K))) hK.le
    have he : K*(ε/(4*K)) = ε/4 := by field_simp
    exact hh.trans_eq he
  have hlo : 0 < L-η := by linarith
  have hhi : 0 < L+η := by linarith
  let Dlo := KernelDemand.demand n (G₀ : Measure ENNReal) (L-η)
  let Dhi := KernelDemand.demand n (G₀ : Measure ENNReal) (L+η)
  have hdlo : ρ < Dlo := by
    have hle := KernelDemand.demand_antitone hn (G₀ : Measure ENNReal) hlo hL (by linarith : L-η ≤ L)
    rw [hroot] at hle
    apply lt_of_le_of_ne hle
    intro he
    have hh := hunique (L-η) hlo he.symm
    linarith
  have hdhi : Dhi < ρ := by
    have hle := KernelDemand.demand_antitone hn (G₀ : Measure ENNReal) hL hhi (by linarith : L ≤ L+η)
    rw [hroot] at hle
    apply lt_of_le_of_ne hle
    intro he
    have hh := hunique (L+η) hhi he
    linarith
  let δlo := (Dlo-ρ)/2
  let δhi := (ρ-Dhi)/2
  have hδlo : 0 < δlo := by dsimp only [δlo]; linarith
  have hδhi : 0 < δhi := by dsimp only [δhi]; linarith
  have hcm1 : Tendsto (fun t => ((c t:ℝ)-1)/N t) atTop (𝓝 ρ) := by
    have hinv : Tendsto (fun t => ((N t:ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
    have hh := hcapacity.sub hinv
    simpa only [sub_zero, Function.comp_def, sub_div, one_div] using hh
  have hclo := hcapacity.eventually_lt_const (show ρ < Dlo-δlo by dsimp only [δlo]; linarith)
  have hchi := hcm1.eventually_const_lt (show Dhi+δhi < ρ by dsimp only [δhi]; linarith)
  let E := fun t =>
    (∫ r : Fin (N t) → ℝ, |(∑ j, kernel n (r j) (L-η))/(N t:ℝ)-Dlo| ∂P t)/δlo +
    (∫ r : Fin (N t) → ℝ, |(∑ j, kernel n (r j) (L+η))/(N t:ℝ)-Dhi| ∂P t)/δhi
  have hE : Tendsto E atTop (𝓝 0) := by
    have hh := ((tendsto_rival_kernel_error N hN hn G hpos hweak hlo).div_const δlo).add
      ((tendsto_rival_kernel_error N hN hn G hpos hweak hhi).div_const δhi)
    simpa only [zero_div, zero_add, E, P, Dlo, Dhi] using hh
  filter_upwards [hclo,hchi,hE.eventually_lt_const (by linarith : 0 < ε/2)] with t htlo hthi hEt
  have hpositive : ∀ᵐ r ∂P t, ∀ j, 0 < r j :=
    Filter.eventually_all.mpr fun _ => Measure.tendsto_eval_ae_ae.eventually (hpos t)
  have hbound := integral_mono_ae (halloc t)
    (((integrable_const (K*η)).add ((hI t hlo Dlo).div_const δlo)).add ((hI t hhi Dhi).div_const δhi))
    (hpositive.mono fun r hr => allocation_error_le_rival_errors (hNpos t) hn (hc t) r hr
      (hx t) hL hη hηL hδlo hδhi htlo.le hthi.le)
  have hh : (∫ r : Fin (N t) → ℝ, |allocation n (c t) hn (hc t) r (x t)-kernel n (x t) L| ∂P t) ≤ K*η+E t := by
    have hs : Integrable (fun r : Fin (N t) → ℝ =>
        K*η+|(∑ j, kernel n (r j) (L-η))/(N t:ℝ)-Dlo|/δlo) (P t) :=
      (integrable_const (K*η)).add ((hI t hlo Dlo).div_const δlo)
    simp only [Pi.add_apply] at hbound
    rw [integral_add hs ((hI t hhi Dhi).div_const δhi),
      integral_add (integrable_const (K*η)) ((hI t hlo Dlo).div_const δlo),
      integral_div, integral_div] at hbound
    simpa only [integral_const, probReal_univ, one_smul, E, add_assoc] using hbound
  have hfinal : (∫ r : Fin (N t) → ℝ,
      |allocation n (c t) hn (hc t) r (x t)-kernel n (x t) L| ∂P t) < ε := by linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] using hfinal

theorem integral_success_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (p : Ω → ℝ) (hp : Measurable p) (hpb : ∀ z, p z ∈ Icc (0:ℝ) 1)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    |(∫ z, success n (p z) ∂P)-success n q| ≤ (n:ℝ)*(∫ z, |p z-q| ∂P) := by
  have hpi := UnitInterval.integrable P p hp (fun z => (hpb z).1) (fun z => (hpb z).2)
  have hsi := UnitInterval.integrable_success P p hp (fun z => (hpb z).1) (fun z => (hpb z).2) n
  have he : (∫ z, success n (p z) ∂P)-success n q = ∫ z, success n (p z)-success n q ∂P := by
    rw [integral_sub hsi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  rw [he]
  have hh : |∫ z, success n (p z)-success n q ∂P| ≤ ∫ z, |success n (p z)-success n q| ∂P := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => success n (p z)-success n q)
  apply hh.trans
  have hm := integral_mono ((hsi.sub (integrable_const _)).abs)
    (((hpi.sub (integrable_const q)).abs).const_mul (n:ℝ))
    (fun z => OwnImpact.success_abs_sub_le n (hpb z) hq)
  simpa only [Pi.sub_apply, integral_const_mul] using hm

theorem tendsto_focal_coverage
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 < b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ} (hc : ∀ t, c t ≤ Fintype.card (Fin (N t))+1)
    {ρ L : ℝ} (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T, 0 < T → KernelDemand.demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hcapacity : Tendsto (fun t => (c t:ℝ)/N t) atTop (𝓝 ρ))
    (x : ℕ → ℝ) (hx : ∀ t, 0 < x t) {x₀ : ℝ} (hxx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun t => coverage n (c t) hn (hc t)
      (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (x t)) atTop
        (𝓝 (success n (kernel n x₀ L))) := by
  have herr := tendsto_focal_allocation_kernel_error N hNpos hN hn G hpos hweak hc hL hroot hunique hcapacity x hx
  have hzero : Tendsto (fun t => coverage n (c t) hn (hc t)
      (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (x t)-success n (kernel n (x t) L)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero (fun _ => abs_nonneg _) _ (by simpa only [mul_zero] using herr.const_mul (n:ℝ))
    intro t
    exact integral_success_error_le _ n _ (measurable_allocation_rivals hn (hc t) (hx t))
      (fun r => allocation_bounds hn (hc t) r (x t)) (kernel_bounds hn hL (x t))
  have hs := (continuous_success n).continuousAt.tendsto.comp
    ((continuous_kernel_bid hn hL).continuousAt.tendsto.comp hxx)
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hzero.add hs

end FCAppendix.PayOnce.AnalyticalKernel
