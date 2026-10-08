import FCAppendix.Probability.UniformMovingThreshold
import Mathlib.Probability.CDF

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem cdf_recenter_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (bar center scale x : ℝ) :
    cdf (μ.map (fun ω => (X ω-center)/scale)) x =
      cdf (μ.map (fun ω => (X ω-bar)/scale)) (x-(bar-center)/scale) := by
  haveI : IsProbabilityMeasure (μ.map (fun ω => (X ω-center)/scale)) :=
    Measure.isProbabilityMeasure_map ((hX.sub_const center).div_const scale).aemeasurable
  haveI : IsProbabilityMeasure (μ.map (fun ω => (X ω-bar)/scale)) :=
    Measure.isProbabilityMeasure_map ((hX.sub_const bar).div_const scale).aemeasurable
  rw [cdf_eq_real,cdf_eq_real,
    map_measureReal_apply ((hX.sub_const center).div_const scale) measurableSet_Iic,
    map_measureReal_apply ((hX.sub_const bar).div_const scale) measurableSet_Iic]
  congr 1
  ext ω
  change (X ω-center)/scale ≤ x ↔ (X ω-bar)/scale ≤ x-(bar-center)/scale
  have hid : (X ω-center)/scale=(X ω-bar)/scale+(bar-center)/scale := by ring
  rw [hid]
  constructor <;> intro hh <;> linarith

theorem cdf_recenter_tendsto {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)]
    (X : ∀ t, Ω t → ℝ) (hX : ∀ t, Measurable (X t))
    (bar center scale : ℕ → ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (hshift : Tendsto (fun t => (bar t-center t)/scale t) atTop (𝓝 0))
    (hCDF : ∀ x, Tendsto (fun t => cdf ((μ t).map (fun ω => (X t ω-bar t)/scale t)) x)
      atTop (𝓝 (G x))) (x : ℝ) :
    Tendsto (fun t => cdf ((μ t).map (fun ω => (X t ω-center t)/scale t)) x)
      atTop (𝓝 (G x)) := by
  have hx : Tendsto (fun t => x-(bar t-center t)/scale t) atTop (𝓝 x) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hshift
  have hh := moving_threshold_tendsto_of_monotone
    (fun t => cdf ((μ t).map (fun ω => (X t ω-bar t)/scale t))) G
    (fun _ => monotone_cdf _) hG hCDF _ hx
  apply hh.congr
  intro t
  exact (cdf_recenter_eq (μ t) (hX t) (bar t) (center t) (scale t) x).symm

theorem cdf_recenter_uniform {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] {ι : Type*}
    (μ : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)]
    (X : ∀ t, ι → Ω t → ℝ) (P : ι → Prop) (hX : ∀ t i, P i → Measurable (X t i))
    (bar center scale : ℕ → ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (hshift : Tendsto (fun t => (bar t-center t)/scale t) atTop (𝓝 0))
    (hCDF : ∀ x ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i, P i →
      |cdf ((μ t).map (fun ω => (X t i ω-bar t)/scale t)) x-G x| < ε) (x : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i, P i →
      |cdf ((μ t).map (fun ω => (X t i ω-center t)/scale t)) x-G x| < ε := by
  have hx : Tendsto (fun t => x-(bar t-center t)/scale t) atTop (𝓝 x) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hshift
  have hh := uniform_moving_threshold_of_monotone
    (fun t i => cdf ((μ t).map (fun ω => (X t i ω-bar t)/scale t))) P G
    (fun _ _ _ => monotone_cdf _) hG hCDF _ hx
  intro ε hε
  filter_upwards [hh ε hε] with t ht
  intro i hi
  rw [cdf_recenter_eq (μ t) (hX t i hi)]
  exact ht i hi

end FCAppendix.Probability
