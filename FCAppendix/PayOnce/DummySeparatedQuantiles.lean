import FCAppendix.PayOnce.DummyQuantileCoverageBounds
import FCAppendix.PayOnce.QuantileTailComparison

namespace FCAppendix.PayOnce.DummyQuantileTailComparison
open MeasureTheory ProbabilityTheory Set Filter Topology Real CommonList DummyKernel
open QuantileTailComparison
open scoped BigOperators

theorem coverage_ratio_zero_of_separated_quantiles
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) {c : ℕ → ℕ}
    (bid : ℕ → ℝ → ℝ) (hbid : ∀ t, Measurable (bid t))
    (hmono : ∀ t, Monotone (bid t))
    (a b : ℕ → ℝ) (ha : ∀ t, 0 < a t) (hb : ∀ t, 0 < b t)
    {x y : ℝ} (hxy : x < y) (hx : ∀ t, 0 < bid t x)
    (hmass : 0 < F (Ioc x y)) (hleft : 0 < F (Iic y))
    (hsepX : Tendsto (fun t => a t / bid t x) atTop (𝓝 0))
    (hsepY : Tendsto (fun t => bid t y / b t) atTop (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) (hmean : ρ < F.real (Ioi y))
    (hcap : Tendsto (fun t => (c t:ℝ)/N t) atTop (𝓝 ρ)) :
    (∀ᶠ t in atTop, 0 < coverage n (c t) hn
      (Measure.pi (fun _ : Fin (N t) => F.map (bid t))) (b t)) ∧
    Tendsto (fun t =>
      coverage n (c t) hn (Measure.pi (fun _ : Fin (N t) => F.map (bid t))) (a t) /
      coverage n (c t) hn (Measure.pi (fun _ : Fin (N t) => F.map (bid t))) (b t))
      atTop (𝓝 0) := by
  let P := fun t => Measure.pi (fun _ : Fin (N t) => F)
  let A := fun t => (P t).real {ω | ∑ i, (Ioi x).indicator (fun _ => (1:ℝ)) (ω i) ≤ (c t:ℝ)}
  let B := fun t => (P t).real {ω | ∑ i, (Ioi y).indicator (fun _ => (1:ℝ)) (ω i) ≤ (c t:ℝ)-1}
  let Q := fun t v => coverage n (c t) hn
    (Measure.pi (fun _ : Fin (N t) => F.map (bid t))) v
  have hr : Tendsto (fun t => ((c t:ℝ)-1)/N t) atTop (𝓝 ρ) := by
    have ht : Tendsto (fun t => (1:ℝ)/N t) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN) :
          Tendsto (fun t => ((N t:ℝ))⁻¹) atTop (𝓝 0))
    simpa only [sub_div, sub_zero] using hcap.sub ht
  obtain ⟨hBpos, hratio⟩ := nested_event_tail_ratio (⟨F, inferInstance⟩ : ProbabilityMeasure ℝ)
    N hNpos hN measurableSet_Ioi measurableSet_Ioi (Ioi_subset_Ioi hxy.le)
    (by change 0 < F (Ioi x \ Ioi y); simpa only [Ioi_sdiff_Ioi] using hmass)
    (by change 0 < F (Ioi y)ᶜ; simpa only [compl_Ioi] using hleft)
    hρ hmean hr hcap
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hhigh := hsepX.eventually_le_const (one_div_pos.mpr hnr)
  have hlow := hsepY.eventually_le_const (H_pos n (by omega) 1 zero_le_one le_rfl)
  have hupper : ∀ᶠ t in atTop, Q t (a t) ≤ A t := by
    filter_upwards [hhigh] with t ht
    apply coverage_le_high_count hn F (bid t) (hbid t) measurableSet_Ioi (ha t)
    intro v hv
    have hh := (div_le_div_iff₀ (hx t) hnr).mp ht
    have hle : (n:ℝ)*a t ≤ bid t x := by simpa only [one_mul, mul_one, mul_comm] using hh
    exact hle.trans (hmono t hv.le)
  have hlower : ∀ᶠ t in atTop, B t ≤ Q t (b t) := by
    filter_upwards [hlow] with t ht
    have hh := low_count_le_coverage (ι := Fin (N t)) (c := c t) hn F (bid t) (hbid t) measurableSet_Ioi
      (hb t) (s := 1) zero_lt_one le_rfl (fun v hv => by
        have hvy : v ≤ y := le_of_not_gt hv
        have hh := (div_le_iff₀ (hb t)).mp ht
        exact (hmono t hvy).trans (by simpa only [mul_comm] using hh))
    simpa only [success, sub_self, zero_pow (by omega : n ≠ 0), sub_zero, one_mul] using hh
  have hQpos : ∀ᶠ t in atTop, 0 < Q t (b t) := by
    filter_upwards [hBpos, hlower] with t ht hl
    exact ht.trans_le hl
  refine ⟨hQpos, ?_⟩
  apply squeeze_zero' ?_ ?_ hratio
  · filter_upwards [hQpos] with t ht
    apply div_nonneg _ ht.le
    apply integral_nonneg
    intro ω
    have hp := allocation_bounds hn (c := c t) ω (a t)
    unfold success
    exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1]))
  · filter_upwards [hQpos, hBpos, hupper, hlower] with t hq hb hu hl
    exact (div_le_div_of_nonneg_right hu hq.le).trans
      (div_le_div_of_nonneg_left measureReal_nonneg hb hl)

end FCAppendix.PayOnce.DummyQuantileTailComparison
