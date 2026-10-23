import FCAppendix.Finite.CutoffIdentification
import FCAppendix.Finite.NearPPILimit

namespace FCAppendix.CommonReserve
open MeasureTheory Filter Set Topology

theorem price_eq_max_of_tail_conditions (F : Measure ℝ) [IsFiniteMeasure F]
    (g r p vstar β : ℝ) (hp : r ≤ p)
    (hcut : F.real (Ioi vstar) = β)
    (hleft : ∀ v < vstar, 0 < F.real (Ioo v vstar))
    (hright : ∀ v > vstar, 0 < F.real (Ioo vstar v))
    (hfill : r < p → F.real (Ioi (g + p)) = β)
    (hbind : p = r → F.real (Ioi (g + r)) ≤ β) :
    p = max r (vstar - g) := by
  rcases eq_or_lt_of_le hp with h | h
  · have hpr : p = r := h.symm
    have hv : vstar - g ≤ r := by
      by_contra hn
      have hgr : g + r < vstar := by linarith
      have ht := Bayes.tail_strict_of_interval_mass F (g + r) vstar hgr (hleft _ hgr)
      rw [hcut] at ht
      exact (not_le_of_gt ht) (hbind hpr)
    simpa [max_eq_left hv] using hpr
  · have he : g + p = vstar := Bayes.eq_cutoff_of_tail_eq F vstar (g + p)
      hleft hright ((hfill h).trans hcut.symm)
    have he' : p = vstar - g := by linarith
    rw [max_eq_right (by linarith : r ≤ vstar - g)]
    exact he'

theorem price_pos_of_scarcity (F : Measure ℝ) [IsFiniteMeasure F]
    (g p β : ℝ) (hp : 0 ≤ p) (hscarce : β < F.real (Ioi g))
    (hcap : F.real (Ioi (g + p)) ≤ β) : 0 < p := by
  by_contra hn
  have hz : p = 0 := le_antisymm (le_of_not_gt hn) hp
  simp only [hz, add_zero] at hcap
  exact (not_le_of_gt hscarce) hcap

theorem binding_utility_limit {U δ : ℕ → ℝ → ℝ} (g r : ℝ)
    (hlower : ∀ k v, max (v - g - r) 0 - δ k v ≤ U k v)
    (hupper : ∀ k v, U k v ≤ max (v - g - r) 0)
    (hδ : ∀ v, Tendsto (fun k => δ k v) atTop (𝓝 0)) :
    ∀ v, Tendsto (fun k => U k v) atTop (𝓝 (max (v - g - r) 0)) := by
  intro v
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun k => max (v - g - r) 0 - δ k v) atTop
      (𝓝 (max (v - g - r) 0)) from by simpa using tendsto_const_nhds.sub (hδ v))
    tendsto_const_nhds (fun k => hlower k v) (fun k => hupper k v)

theorem moving_price_count_limits {n : ℕ} (μ : ℕ → CountLaw n)
    (U e δ t : ℕ → ℝ) (w p : ℝ) (hwp : w - p ≠ 0) (hp : 0 < p)
    (hU : ∀ k, 0 ≤ U k) (he : ∀ k, 0 ≤ e k) (hδ : ∀ k, 0 ≤ δ k)
    (hupper : ∀ k, U k ≤ (w - t k) * (μ k).success - t k * (μ k).duplicates + e k)
    (hlower : ∀ k, max (w - p) 0 - δ k ≤ U k)
    (he0 : Tendsto e atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 p))
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto U atTop (𝓝 (max (w - p) 0)) ∧
    Tendsto (fun k => (μ k).success) atTop (𝓝 (NearPPI.cutoffSuccess (w - p))) ∧
    Tendsto (fun k => (μ k).duplicates) atTop (𝓝 0) ∧
    Tendsto (fun k => (μ k).load) atTop (𝓝 (NearPPI.cutoffSuccess (w - p))) ∧
    Tendsto (fun k => (μ k).prob (fun q => q.val ≠ if 0 < w - p then 1 else 0))
      atTop (𝓝 0) := by
  have herr : Tendsto (fun k => e k + (n : ℝ) * |t k - p|) atTop (𝓝 0) := by
    have h := he0.add (((ht.sub_const p).abs).const_mul (n : ℝ))
    simpa using h
  exact NearPPI.count_limits μ hwp hp hU
    (fun k => add_nonneg (he k) (mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)))
    hδ (fun k => NearPPI.change_price (μ k) (hupper k)) hlower herr hδ0

end FCAppendix.CommonReserve
