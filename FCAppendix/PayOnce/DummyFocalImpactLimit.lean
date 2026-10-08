import FCAppendix.PayOnce.DummyFocalImpactBounds
import FCAppendix.PayOnce.InteriorRivalCounts
import FCAppendix.PayOnce.DummyFocalLimit

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open KernelLawConvergence KernelTailEvent CompactifiedBidLaws OwnImpact RareSuccessSlope TruncatedFOC
open AnalyticalKernel (slope_correction_bounds eventually_window_mass_pos integrable_rival_window_error tendsto_rival_window_error tendsto_rival_kernel_error_nonneg)
open scoped BigOperators

theorem tendsto_focal_slope_correction
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ}
    {ρ L : ℝ} (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T, 0 < T → KernelDemand.demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hcapacity : Tendsto (fun t => (c t:ℝ)/N t) atTop (𝓝 ρ))
    {a z : ℝ} (ha : L < a) (haz : a < z) (hz : z < (n:ℝ)*L)
    (hwin : 0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z)))
    (x : ℕ → ℝ) (hx : ∀ t, 0 < x t)
    (w : ∀ t, (Fin (N t) → ℝ) → ℝ)
    (hw : ∀ t, Measurable (w t)) (hwb : ∀ t r, w t r ∈ Icc (0:ℝ) 1)
    (hreg : ∀ t, ∀ᵐ r ∂Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ)),
      RegularClearing n (c t) r (x t))
    (hweight : ∀ t, ∀ᵐ r ∂Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ)),
      x t*deriv (fun b => success n (allocation n (c t) hn r b)) (x t) =
        weightedSlope n (allocation n (c t) hn r (x t)) (w t r)) :
    Tendsto (fun t => ∫ r : Fin (N t) → ℝ,
      baseSlope n (allocation n (c t) hn r (x t))-
        weightedSlope n (allocation n (c t) hn r (x t)) (w t r)
          ∂Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) atTop (𝓝 0) := by
  classical
  let P := fun t => Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))
  let p := fun t (r : Fin (N t) → ℝ) => allocation n (c t) hn r (x t)
  have hp t : Measurable (p t) := measurable_allocation_rivals hn (hx t)
  have hpb t r : p t r ∈ Icc (0:ℝ) 1 := allocation_bounds hn r (x t)
  have hI t : Integrable (fun r => baseSlope n (p t r)-weightedSlope n (p t r) (w t r)) (P t) := by
    apply Integrable.of_bound ((measurable_baseSlope n |>.comp (hp t)).sub
      ((measurable_weightedSlope n).comp ((hp t).prodMk (hw t)))).aestronglyMeasurable ((n:ℝ)^2)
    filter_upwards [] with r
    have hh := slope_correction_bounds hn (hpb t r) (hwb t r)
    change ‖baseSlope n (p t r)-weightedSlope n (p t r) (w t r)‖ ≤ (n:ℝ)^2
    rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
    exact hh.2.trans (mul_le_of_le_one_right (sq_nonneg _) (hwb t r).2)
  have hNR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  let η := min (L/4) (min ((a-L)/2) (((n:ℝ)*L-z)/(2*n)))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by linarith) (by positivity))
  have hηL : η ≤ L/4 := min_le_left _ _
  have hηa : η ≤ (a-L)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηz : η ≤ ((n:ℝ)*L-z)/(2*n) := (min_le_right _ _).trans (min_le_right _ _)
  have hlo : 0 < L-η := by linarith
  have hhi : 0 < L+η := by linarith
  have ha' : L+η < a := by linarith
  have hz' : z < (n:ℝ)*(L-η) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(n:ℝ))).mp hηz
    nlinarith
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
  have hinv : Tendsto (fun t => ((N t:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hcm1 : Tendsto (fun t => ((c t:ℝ)-1)/N t) atTop (𝓝 ρ) := by
    simpa only [sub_zero, Function.comp_def, sub_div, one_div] using hcapacity.sub hinv
  have hclo := hcapacity.eventually_lt_const (show ρ < Dlo-δlo by dsimp only [δlo]; linarith)
  have hchi := hcm1.eventually_const_lt (show Dhi+δhi < ρ by dsimp only [δhi]; linarith)
  obtain ⟨q,hq,hqmass⟩ := eventually_window_mass_pos G hweak (hL.trans ha) haz hwin
  let E₀ := fun t (r : Fin (N t) → ℝ) => |(∑ j, kernel n (r j) (L-η))/(N t:ℝ)-Dlo|/δlo
  let E₁ := fun t (r : Fin (N t) → ℝ) => |(∑ j, kernel n (r j) (L+η))/(N t:ℝ)-Dhi|/δhi
  let E₂ := fun t (r : Fin (N t) → ℝ) =>
    2*|((Finset.univ.filter fun j => r j ∈ Ioo a z).card:ℝ)/(N t:ℝ)-(G t : Measure ℝ).real (Ioo a z)|/q
  let s := fun t => 2*(n:ℝ)^3/(q*N t)
  have hKI t {T : ℝ} (hT : 0 < T) (u : ℝ) : Integrable
      (fun r : Fin (N t) → ℝ => |(∑ j, kernel n (r j) T)/(N t:ℝ)-u|) (P t) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro j _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hT).measurable.comp (measurable_pi_apply j))
      (fun r => (kernel_bounds hn hT (r j)).1) (fun r => (kernel_bounds hn hT (r j)).2)
  have hE₀ t : Integrable (E₀ t) (P t) := (hKI t hlo Dlo).div_const δlo
  have hE₁ t : Integrable (E₁ t) (P t) := (hKI t hhi Dhi).div_const δhi
  have hE₂ t : Integrable (E₂ t) (P t) :=
    ((integrable_rival_window_error (G t : Measure ℝ) (N t) a z
      ((G t : Measure ℝ).real (Ioo a z))).const_mul 2).div_const q
  have hs : Tendsto s atTop (𝓝 0) := by
    have hh := hinv.const_mul (2*(n:ℝ)^3/q)
    simpa only [s, div_mul_eq_div_mul_one_div, one_div, mul_zero] using hh
  have he₀ : Tendsto (fun t => ∫ r, E₀ t r ∂P t) atTop (𝓝 0) := by
    simpa only [E₀, P, Dlo, integral_div, zero_div] using
      (tendsto_rival_kernel_error_nonneg N hN hn G hpos hweak hlo).div_const δlo
  have he₁ : Tendsto (fun t => ∫ r, E₁ t r ∂P t) atTop (𝓝 0) := by
    simpa only [E₁, P, Dhi, integral_div, zero_div] using
      (tendsto_rival_kernel_error_nonneg N hN hn G hpos hweak hhi).div_const δhi
  have he₂ : Tendsto (fun t => ∫ r, E₂ t r ∂P t) atTop (𝓝 0) := by
    simpa only [E₂, P, integral_div, integral_const_mul, zero_div, mul_zero] using
      ((tendsto_rival_window_error N hN G a z).const_mul 2).div_const q
  have hlim : Tendsto (fun t => (n:ℝ)^2*(s t+(∫ r, E₀ t r ∂P t)+
      (∫ r, E₁ t r ∂P t)+(∫ r, E₂ t r ∂P t))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (((hs.add he₀).add he₁).add he₂).const_mul ((n:ℝ)^2)
  apply squeeze_zero' (Eventually.of_forall fun t => integral_nonneg fun r =>
    (slope_correction_bounds hn (hpb t r) (hwb t r)).1) _ hlim
  filter_upwards [hclo,hchi,hqmass] with t htlo hthi hqt
  have hi := integral_mono_ae (hI t)
    (((((integrable_const (s t)).add (hE₀ t)).add (hE₁ t)).add (hE₂ t)).const_mul ((n:ℝ)^2)) ?_
  · have hi₀ : Integrable (fun r : Fin (N t) → ℝ => s t+E₀ t r) (P t) :=
      (integrable_const (s t)).add (hE₀ t)
    have hi₁ : Integrable (fun r : Fin (N t) → ℝ => s t+E₀ t r+E₁ t r) (P t) :=
      hi₀.add (hE₁ t)
    simp only [Pi.add_apply] at hi
    rw [integral_const_mul,integral_add hi₁ (hE₂ t),integral_add hi₀ (hE₁ t),
      integral_add (integrable_const (s t)) (hE₀ t),integral_const,probReal_univ,one_smul] at hi
    exact hi
  · filter_upwards [hreg t,hweight t] with r hr hwr
    exact slope_correction_le_rival_errors (hNpos t) hn r (hx t) hr hlo hhi ha' hz'
      hδlo hδhi hq hqt htlo.le hthi.le (hwb t r) hwr

end FCAppendix.PayOnce.DummyKernel
