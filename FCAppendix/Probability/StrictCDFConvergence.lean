import FCAppendix.Probability.UniformMovingThreshold
import Mathlib.Probability.CDF

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem uniform_strictCDF_moving_threshold {ι : Type*}
    (μ : ℕ → ι → Measure ℝ) [∀ t i, IsProbabilityMeasure (μ t i)]
    (P : ι → Prop) (G : ℝ → ℝ) (hG : Continuous G)
    (hfixed : ∀ x ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i, P i →
      |cdf (μ t i) x-G x| < ε)
    (x : ℕ → ℝ) {z : ℝ} (hx : Tendsto x atTop (𝓝 z)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i, P i →
      |(μ t i).real (Iio (x t))-G z| < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hG.continuousAt (ε/2) (by positivity)
  have hlo : |G (z-δ/2)-G z| < ε/2 := by
    have hh := hcont (show dist (z-δ/2) z < δ by
      rw [Real.dist_eq]
      have he : z-δ/2-z = -δ/2 := by ring
      rw [he,abs_div,abs_neg,abs_of_pos hδ,abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith)
    simpa only [Real.dist_eq] using hh
  have hhi : |G (z+δ/2)-G z| < ε/2 := by
    have hh := hcont (show dist (z+δ/2) z < δ by
      rw [Real.dist_eq,add_sub_cancel_left,abs_of_pos (by positivity : 0 < δ/2)]
      linarith)
    simpa only [Real.dist_eq] using hh
  filter_upwards [hfixed (z-δ/2) (ε/2) (by positivity),
    hfixed (z+δ/2) (ε/2) (by positivity),
    hx.eventually (Ioo_mem_nhds (by linarith : z-δ/2 < z) (by linarith : z < z+δ/2))]
    with t htlo hthi ht
  intro i hi
  have h₁ := abs_lt.mp (htlo i hi)
  have h₂ := abs_lt.mp (hthi i hi)
  have h₃ := abs_lt.mp hlo
  have h₄ := abs_lt.mp hhi
  have hlower : cdf (μ t i) (z-δ/2) ≤ (μ t i).real (Iio (x t)) := by
    rw [cdf_eq_real]
    exact measureReal_mono fun _ ha => ha.trans_lt ht.1
  have hupper : (μ t i).real (Iio (x t)) ≤ cdf (μ t i) (z+δ/2) := by
    rw [cdf_eq_real]
    exact measureReal_mono fun _ ha => (ha.trans ht.2).le
  apply abs_lt.mpr
  constructor <;> linarith

theorem strictCDF_moving_threshold_tendsto
    (μ : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (μ t)]
    (G : ℝ → ℝ) (hG : Continuous G)
    (hfixed : ∀ x, Tendsto (fun t => cdf (μ t) x) atTop (𝓝 (G x)))
    (x : ℕ → ℝ) {z : ℝ} (hx : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun t => (μ t).real (Iio (x t))) atTop (𝓝 (G z)) := by
  have hh := uniform_strictCDF_moving_threshold (fun t (_ : Unit) => μ t)
    (fun _ => True) G hG (fun y ε hε => by
      filter_upwards [(Metric.tendsto_nhds.mp (hfixed y)) ε hε] with t ht _ _
      simpa only [Real.dist_eq] using ht) x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hh ε hε] with t ht
  simpa only [Real.dist_eq] using ht () trivial

end FCAppendix.Probability
