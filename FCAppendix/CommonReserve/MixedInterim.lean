import FCAppendix.CommonReserve.Interim

noncomputable section
namespace FCAppendix.CommonReserve.InterimProblem

open MeasureTheory Filter Topology

variable {A : Type*} [MeasurableSpace A]

theorem integrable_success (P : InterimProblem A) (ν : Measure A)
    [IsProbabilityMeasure ν] (hS : Measurable P.success) :
    Integrable P.success ν := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) hS.aestronglyMeasurable
  exact ae_of_all _ fun a => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (P.success_nonneg a)] using
      P.success_le_one a

theorem mixed_success_nonneg (P : InterimProblem A) (ν : Measure A) :
    0 ≤ ∫ a, P.success a ∂ν := integral_nonneg P.success_nonneg

theorem mixed_success_le_one (P : InterimProblem A) (ν : Measure A)
    [IsProbabilityMeasure ν] (hS : Measurable P.success) :
    (∫ a, P.success a ∂ν) ≤ 1 := by
  calc
    _ ≤ ∫ _a, (1 : ℝ) ∂ν := integral_mono_ae (P.integrable_success ν hS)
      (integrable_const _) (ae_of_all _ P.success_le_one)
    _ = _ := by simp

theorem mixed_supporting_line (P : InterimProblem A) (ν : Measure A)
    [IsProbabilityMeasure ν] (hS : Measurable P.success) (v w : ℝ)
    (hbr : ∀ᵐ a ∂ν, P.BestResponse v a) :
    P.envelope v + (w - v) * (∫ a, P.success a ∂ν) ≤ P.envelope w := by
  have hI := (integrable_const (P.envelope v)).add
    ((P.integrable_success ν hS).const_mul (w - v))
  have h := integral_mono_ae hI (integrable_const (P.envelope w))
    (hbr.mono fun a ha => P.supporting_line v a ha w)
  simpa only [Pi.add_apply,
    integral_add (integrable_const _) ((P.integrable_success ν hS).const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul] using h

theorem mixed_secants (P : InterimProblem A) (ν : Measure A)
    [IsProbabilityMeasure ν] (hS : Measurable P.success) (v h : ℝ)
    (hh : 0 < h) (hbr : ∀ᵐ a ∂ν, P.BestResponse v a) :
    (P.envelope v - P.envelope (v - h)) / h ≤ (∫ a, P.success a ∂ν) ∧
      (∫ a, P.success a ∂ν) ≤ (P.envelope (v + h) - P.envelope v) / h := by
  have hl := P.mixed_supporting_line ν hS v (v - h) hbr
  have hu := P.mixed_supporting_line ν hS v (v + h) hbr
  constructor
  · apply (div_le_iff₀ hh).mpr
    nlinarith
  · apply (le_div_iff₀ hh).mpr
    nlinarith

omit [MeasurableSpace A] in
theorem bestResponse_cost_bounds (P : InterimProblem A) (v : ℝ) (a : A)
    (hfee : 0 ≤ P.g + P.r) (ha : P.BestResponse v a) :
    0 ≤ P.cost a ∧ P.cost a ≤ max v 0 := by
  have hs0 := P.success_nonneg a
  have hs1 := P.success_le_one a
  have hc := P.cost_floor a
  have hu : 0 ≤ P.payoff v a := by
    rw [(P.bestResponse_iff_attains v a).mp ha]
    exact P.envelope_nonneg v
  have hprod : v * P.success a ≤ max v 0 := by
    by_cases hv : 0 ≤ v
    · rw [max_eq_left hv]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hv)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv) hs0
  unfold payoff at hu
  exact ⟨(mul_nonneg hfee hs0).trans hc, by linarith⟩

theorem integrable_cost_of_bestResponse (P : InterimProblem A) (ν : Measure A)
    [IsProbabilityMeasure ν] (hC : Measurable P.cost) (v : ℝ)
    (hfee : 0 ≤ P.g + P.r) (hbr : ∀ᵐ a ∂ν, P.BestResponse v a) :
    Integrable P.cost ν := by
  apply Integrable.mono' (integrable_const (max v 0)) hC.aestronglyMeasurable
  filter_upwards [hbr] with a ha
  obtain ⟨h0, h1⟩ := P.bestResponse_cost_bounds v a hfee ha
  simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1

theorem mixed_cost_identity (P : InterimProblem A) (ν : Measure A)
    [IsProbabilityMeasure ν] (hS : Measurable P.success) (v : ℝ)
    (hbr : ∀ᵐ a ∂ν, P.BestResponse v a) :
    (∫ a, P.cost a ∂ν) = v * (∫ a, P.success a ∂ν) - P.envelope v := by
  calc
    _ = ∫ a, v * P.success a - P.envelope v ∂ν := by
      apply integral_congr_ae
      filter_upwards [hbr] with a ha
      have h := (P.bestResponse_iff_attains v a).mp ha
      unfold payoff at h
      linarith
    _ = _ := by
      rw [integral_sub ((P.integrable_success ν hS).const_mul v) (integrable_const _)]
      simp [integral_const_mul]

theorem mixed_success_tendsto (P : ℕ → InterimProblem A)
    (ν : ℕ → Measure A) [∀ k, IsProbabilityMeasure (ν k)]
    (hS : ∀ k, Measurable (P k).success) (c v : ℝ) (hv : v ≠ c)
    (hbr : ∀ k, ∀ᵐ a ∂ν k, (P k).BestResponse v a)
    (hU : ∀ w, Tendsto (fun k => (P k).envelope w) atTop (𝓝 (max (w - c) 0))) :
    Tendsto (fun k => ∫ a, (P k).success a ∂ν k) atTop
      (𝓝 (if c < v then 1 else 0)) := by
  let w := (v + c) / 2
  rcases lt_or_gt_of_ne hv with hvc | hcv
  · have hwc : w < c := by dsimp [w]; linarith
    have hvw : 0 < w - v := by dsimp [w]; linarith
    have hz : Tendsto
        (fun k => ((P k).envelope w - (P k).envelope v) / (w - v)) atTop (𝓝 0) := by
      have h := ((hU w).sub (hU v)).div_const (w - v)
      simpa [max_eq_right (sub_nonpos.mpr hwc.le),
        max_eq_right (sub_nonpos.mpr hvc.le)] using h
    rw [if_neg (not_lt.mpr hvc.le)]
    apply squeeze_zero (fun k => (P k).mixed_success_nonneg (ν k)) _ hz
    intro k
    apply (le_div_iff₀ hvw).mpr
    have h := (P k).mixed_supporting_line (ν k) (hS k) v w (hbr k)
    nlinarith
  · have hcw : c < w := by dsimp [w]; linarith
    have hwv : 0 < v - w := by dsimp [w]; linarith
    have ho : Tendsto
        (fun k => ((P k).envelope v - (P k).envelope w) / (v - w)) atTop (𝓝 1) := by
      have h := ((hU v).sub (hU w)).div_const (v - w)
      simpa [max_eq_left (sub_nonneg.mpr hcw.le),
        max_eq_left (sub_nonneg.mpr hcv.le), div_self hwv.ne'] using h
    rw [if_pos hcv]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le ho tendsto_const_nhds
    · intro k
      apply (div_le_iff₀ hwv).mpr
      have h := (P k).mixed_supporting_line (ν k) (hS k) v w (hbr k)
      nlinarith
    · intro k
      exact (P k).mixed_success_le_one (ν k) (hS k)

theorem mixed_cost_tendsto (P : ℕ → InterimProblem A)
    (ν : ℕ → Measure A) [∀ k, IsProbabilityMeasure (ν k)]
    (hS : ∀ k, Measurable (P k).success) (c v : ℝ) (hv : v ≠ c)
    (hbr : ∀ k, ∀ᵐ a ∂ν k, (P k).BestResponse v a)
    (hU : ∀ w, Tendsto (fun k => (P k).envelope w) atTop (𝓝 (max (w - c) 0))) :
    Tendsto (fun k => ∫ a, (P k).cost a ∂ν k) atTop
      (𝓝 (c * if c < v then 1 else 0)) := by
  have h := ((mixed_success_tendsto P ν hS c v hv hbr hU).const_mul v).sub (hU v)
  have he : v * (if c < v then (1 : ℝ) else 0) - max (v - c) 0 =
      c * (if c < v then (1 : ℝ) else 0) := by
    by_cases hcv : c < v
    · simp [hcv, max_eq_left (sub_nonneg.mpr hcv.le)]
    · simp [hcv, max_eq_right (sub_nonpos.mpr (le_of_not_gt hcv))]
  rw [he] at h
  exact h.congr fun k => ((P k).mixed_cost_identity (ν k) (hS k) v (hbr k)).symm

end FCAppendix.CommonReserve.InterimProblem
