import FCAppendix.PayOnce.InactiveEventualPureBids
import FCAppendix.PayOnce.GaussianParameters

namespace FCAppendix.PayOnce
open MeasureTheory Set Filter Topology

theorem monotone_entry_barrier (F : Measure ℝ) {n : ℕ} {g L : ℝ}
    (hL : 0 < L) (hlocal : GaussianParameters.LocalFullSupport
      (F.map (fun v => max (v-g) 0)) L)
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar n L (max (v-g) 0))))
    (bar : ℕ → ℝ) (hbar : Tendsto bar atTop (𝓝 L)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ t in atTop, ∀ v : ℝ,
      bar t ≤ v-g → bar t-η < b t v := by
  intro η hη
  obtain ⟨ε,hε,hsupport⟩ := hlocal
  let r := min (ε/2) (min (η/4) (L/2))
  have hr : 0 < r := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hrε : r ≤ ε/2 := min_le_left _ _
  have hrη : r ≤ η/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hrL : r ≤ L/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hmass := hsupport (L-r) (L-r/2) (by linarith) (by linarith) (by linarith)
  have hm : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub measurable_const).max measurable_const
  rw [Measure.map_apply hm measurableSet_Ioo] at hmass
  obtain ⟨v₀,hv₀,hconv⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hmass.ne' (ae_restrict_of_ae hlim)
  change L-r < max (v₀-g) 0 ∧ max (v₀-g) 0 < L-r/2 at hv₀
  have hwpos : 0 < v₀-g := by
    have hh : 0 < max (v₀-g) 0 := lt_trans (by linarith) hv₀.1
    simpa only [lt_max_iff,lt_self_iff_false,or_false] using hh
  rw [max_eq_left hwpos.le] at hv₀ hconv
  rw [Limit.bidStar_of_le (by linarith : v₀-g ≤ L),max_eq_left hwpos.le] at hconv
  have hlow : L-η/2 < v₀-g := by linarith
  filter_upwards [hconv.eventually (eventually_gt_nhds hlow),
    hbar.eventually (eventually_lt_nhds (by linarith : L < L+η/2)),
    hbar.eventually (eventually_gt_nhds (by linarith : v₀-g < L))]
    with t ht hb ht₀
  intro v hv
  have horder : v₀ ≤ v := by linarith
  exact lt_of_lt_of_le (by linarith : bar t-η < b t v₀) (hmono t horder)

end FCAppendix.PayOnce
