import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

namespace FCAppendix.Probability
open Set Filter Topology

theorem uniform_moving_threshold_of_monotone {ι : Type*}
    (Q : ℕ → ι → ℝ → ℝ) (P : ι → Prop) (G : ℝ → ℝ)
    (hmono : ∀ t i, P i → Monotone (Q t i)) (hG : Continuous G)
    (hfixed : ∀ x ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i, P i → |Q t i x-G x| < ε)
    (x : ℕ → ℝ) {z : ℝ} (hx : Tendsto x atTop (𝓝 z)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i, P i → |Q t i (x t)-G z| < ε := by
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
  have hlower := hmono t i hi ht.1.le
  have hupper := hmono t i hi ht.2.le
  apply abs_lt.mpr
  constructor <;> linarith

theorem moving_threshold_tendsto_of_monotone
    (Q : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (hmono : ∀ t, Monotone (Q t)) (hG : Continuous G)
    (hfixed : ∀ x, Tendsto (fun t => Q t x) atTop (𝓝 (G x)))
    (x : ℕ → ℝ) {z : ℝ} (hx : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun t => Q t (x t)) atTop (𝓝 (G z)) := by
  have hh := uniform_moving_threshold_of_monotone (fun t (_ : Unit) => Q t) (fun _ => True) G
    (fun t _ _ => hmono t) hG (fun y ε hε => by
      filter_upwards [(Metric.tendsto_nhds.mp (hfixed y)) ε hε] with t ht _ _
      simpa only [Real.dist_eq] using ht) x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hh ε hε] with t ht
  simpa only [Real.dist_eq] using ht () trivial

end FCAppendix.Probability
