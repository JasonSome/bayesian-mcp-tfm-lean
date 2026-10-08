import FCAppendix.Probability.BoundedLawConvergence
import Mathlib.Analysis.SpecificLimits.Basic

namespace FCAppendix.TriangularCramerBounds
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.ExponentialTilt FCAppendix.BoundedLawConvergence

variable {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (Y : ∀ m, Fin (m + 1) → Ω m → ℝ)
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}

def tailProbability (r : ℕ → ℝ) (m : ℕ) : ℝ :=
  (P m).real {ω | rowSum (Y m) ω ≤ r m}

omit [∀ m, IsProbabilityMeasure (P m)] in

theorem coordinate_bounded
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (m : ℕ) (i : Fin (m + 1)) : ∀ᵐ ω ∂P m, Y m i ω ∈ Icc (0 : ℝ) 1 :=
  (hlaw m i).symm.ae_mem_snd measurableSet_Icc (hν m)

theorem coordinate_tilted_mean
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (m : ℕ) (i : Fin (m + 1)) (u : ℝ) :
    (∫ ω, Y m i ω ∂((P m).tilted (fun ω => u * Y m i ω))) =
      ∫ x, x ∂((ν m : Measure ℝ).tilted (fun x => u * x)) := by
  apply tilted_mean_eq_of_identDistrib (hlaw m i)
  · rw [integrableExpSet_eq_univ_of_bounded (P m) (hlaw m i).aemeasurable_fst
      (coordinate_bounded P Y hν hlaw m i), interior_univ]
    trivial
  · rw [integrableExpSet_eq_univ_of_bounded (ν m : Measure ℝ)
      measurable_id.aemeasurable (hν m), interior_univ]
    trivial

theorem eventually_log_lower_of_tilt
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ u ε c : ℝ}
    (hr : Tendsto (fun m => r m / (m + 1 : ℕ)) atTop (𝓝 ρ))
    (hu : u ≤ 0) (hε : 0 < ε)
    (hz : (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) + ε < ρ)
    (hc : c < cgf id (μ : Measure ℝ) u -
      u * ((∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) - ε)) :
    ∀ᶠ m in atTop, 0 < tailProbability P Y r m ∧
      c ≤ log (tailProbability P Y r m) / (m + 1 : ℕ) := by
  let z : ℕ → ℝ := fun m => ∫ x, x ∂((ν m : Measure ℝ).tilted (fun x => u * x))
  have hzlim := tendsto_tilted_mean hν hμ hweak u
  have hgap := (hzlim.add_const ε).sub hr
  have hthreshold : ∀ᶠ m in atTop, z m + ε ≤ r m / (m + 1 : ℕ) := by
    filter_upwards [hgap.eventually_lt_const (show
      (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) + ε - ρ < 0 by linarith)] with m hm
    change z m + ε - r m / (m + 1 : ℕ) < 0 at hm
    linarith
  have hmTop : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlarge : ∀ᶠ m : ℕ in atTop, 2 ≤ 4 * (m + 1 : ℕ) * ε ^ 2 := by
    have hh := (hmTop.const_mul_atTop (show 0 < 4 * ε ^ 2 by positivity)).eventually_ge_atTop 2
    filter_upwards [hh] with m hm
    nlinarith
  have hlogzero : Tendsto (fun m : ℕ => log 2 / (m + 1 : ℕ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (log 2) |>.comp (tendsto_add_atTop_nat 1)
  have hlower := ((tendsto_cgf hν hμ hweak u).sub
    ((hzlim.sub_const ε).const_mul u)).sub hlogzero
  have hbound : ∀ᶠ m in atTop,
      c < cgf id (ν m : Measure ℝ) u - u * (z m - ε) - log 2 / (m + 1 : ℕ) := by
    exact hlower.eventually_const_lt (by simpa using hc)
  filter_upwards [hthreshold, hlarge, hbound] with m hth hla hlo
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hf := iid_row_log_lower_bound (r := r m) (P m) (hY m)
    (coordinate_bounded P Y hν hlaw m) (hind m) (0 : Fin (m + 1))
    (fun j => (hlaw m j).trans (hlaw m 0).symm) hu hε hla
  rw [coordinate_tilted_mean P Y hν hlaw] at hf
  have ht : (m + 1 : ℕ) * (z m + ε) ≤ r m := by
    simpa only [mul_comm] using (le_div_iff₀ hm).mp hth
  have hh := hf ht
  rw [cgf_eq_of_identDistrib (hlaw m 0)] at hh
  exact ⟨hh.1, hlo.le.trans hh.2⟩

theorem eventually_log_lower
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ u c : ℝ}
    (hr : Tendsto (fun m => r m / (m + 1 : ℕ)) atTop (𝓝 ρ))
    (hu : u ≤ 0)
    (hz : (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))) < ρ)
    (hc : c < cgf id (μ : Measure ℝ) u -
      u * (∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x)))) :
    ∀ᶠ m in atTop, 0 < tailProbability P Y r m ∧
      c ≤ log (tailProbability P Y r m) / (m + 1 : ℕ) := by
  let z := ∫ x, x ∂((μ : Measure ℝ).tilted (fun x => u * x))
  let a := cgf id (μ : Measure ℝ) u - u * z
  let ε := min ((ρ - z) / 2) ((a - c) / (2 * (|u| + 1)))
  have hd : 0 < 2 * (|u| + 1) := by positivity
  have hε : 0 < ε := lt_min (by dsimp [z]; linarith) (div_pos (sub_pos.mpr hc) hd)
  have hε₁ : ε ≤ (ρ - z) / 2 := min_le_left _ _
  have hε₂ : ε * (2 * (|u| + 1)) ≤ a - c :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  have huε := mul_le_mul_of_nonneg_right (neg_le_abs u) hε.le
  apply eventually_log_lower_of_tilt P Y hY hind hν hμ hlaw hweak hr hu hε
  · change z + ε < ρ
    linarith
  · change c < cgf id (μ : Measure ℝ) u - u * (z - ε)
    dsimp [a] at hε₂
    nlinarith

theorem eventually_log_upper
    (hY : ∀ m i, Measurable (Y m i)) (hind : ∀ m, iIndepFun (Y m) (P m))
    (hν : ∀ m, ∀ᵐ x ∂(ν m : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hlaw : ∀ m i, IdentDistrib (Y m i) id (P m) (ν m : Measure ℝ))
    (hweak : Tendsto ν atTop (𝓝 μ)) {r : ℕ → ℝ} {ρ u c : ℝ}
    (hr : Tendsto (fun m => r m / (m + 1 : ℕ)) atTop (𝓝 ρ))
    (hpos : ∀ᶠ m in atTop, 0 < tailProbability P Y r m)
    (hu : u ≤ 0) (hc : cgf id (μ : Measure ℝ) u - u * ρ < c) :
    ∀ᶠ m in atTop, log (tailProbability P Y r m) / (m + 1 : ℕ) ≤ c := by
  have hl := (tendsto_cgf hν hμ hweak u).sub (hr.const_mul u)
  filter_upwards [hpos, hl.eventually_lt_const hc] with m hp hm
  have hf := iid_row_log_upper_bound (P m) (hY m)
    (coordinate_bounded P Y hν hlaw m) (hind m) (0 : Fin (m + 1))
    (fun j => (hlaw m j).trans (hlaw m 0).symm) hu hp
  rw [cgf_eq_of_identDistrib (hlaw m 0)] at hf
  exact hf.trans hm.le

end FCAppendix.TriangularCramerBounds
