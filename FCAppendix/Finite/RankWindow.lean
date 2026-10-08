import FCAppendix.Finite.PairRanks
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Topology Set

theorem rankThreshold_tendsto {T : Type*} {l : Filter T}
    (N C : T → ℕ) (p : T → ℝ) (ρ s : ℝ)
    (hN : Tendsto N l atTop) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hp : Tendsto p l (𝓝 ρ))
    (hC : Tendsto (fun k => ((C k : ℝ) - N k * ρ) / Real.sqrt (N k)) l (𝓝 0))
    (hs : Tendsto (fun k => Real.sqrt (N k) * (p k - ρ)) l (𝓝 s)) :
    Tendsto (fun k => pairRankThreshold (N k) (C k) (p k)
      (Real.sqrt ((N k : ℝ) * p k * (1 - p k)))) l
      (𝓝 (-s / Real.sqrt (ρ * (1 - ρ)))) := by
  have hNr : Tendsto (fun k => (N k : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hN
  have hr := Real.tendsto_sqrt_atTop.comp hNr
  have hv : Tendsto (fun k => Real.sqrt (p k * (1 - p k))) l
      (𝓝 (Real.sqrt (ρ * (1 - ρ)))) := (hp.mul (tendsto_const_nhds.sub hp)).sqrt
  have hvpos : 0 < Real.sqrt (ρ * (1 - ρ)) := Real.sqrt_pos.mpr (by positivity)
  have hi : Tendsto (fun k => 1 / Real.sqrt (N k)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hr
  have hh := ((hC.sub hi).sub hs).div hv hvpos.ne'
  simp only [sub_zero, zero_sub] at hh
  apply hh.congr'
  filter_upwards [hN.eventually_gt_atTop 0] with k hk
  have hpos : 0 < Real.sqrt (N k) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ N k by positivity)
  rw [pairRankThreshold, mul_assoc, Real.sqrt_mul (show (0 : ℝ) ≤ N k by positivity)]
  dsimp only [Pi.div_apply]
  rw [div_mul_eq_div_div]
  congr 1
  field_simp
  rw [hsq]
  ring

theorem rankStdDev_tendsto_atTop {T : Type*} {l : Filter T}
    (N : T → ℕ) (p : T → ℝ) (ρ : ℝ)
    (hN : Tendsto N l atTop) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hp : Tendsto p l (𝓝 ρ)) :
    Tendsto (fun k => Real.sqrt ((N k : ℝ) * p k * (1 - p k))) l atTop := by
  have hNr : Tendsto (fun k => (N k : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hN
  exact Real.tendsto_sqrt_atTop.comp
    (by simpa only [mul_assoc] using (Filter.Tendsto.atTop_mul_pos
      (show 0 < ρ * (1 - ρ) from by positivity) hNr (hp.mul (tendsto_const_nhds.sub hp))))

end FCAppendix.Bayes
