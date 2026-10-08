import FCAppendix.PayOnce.MonotoneEntryBarrier

namespace FCAppendix.PayOnce
open MeasureTheory Set Filter Topology

theorem monotone_entry_bid_tendsto (F : Measure ℝ) {n : ℕ} {g L : ℝ}
    (hL : 0<L) (hlocal : GaussianParameters.LocalFullSupport
      (F.map (fun v => max (v-g) 0)) L)
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (hbound : ∀ t v, b t v ≤ max (v-g) 0)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar n L (max (v-g) 0))))
    (v : ℕ → ℝ) (hv : Tendsto (fun t => v t-g) atTop (𝓝 L)) :
    Tendsto (fun t => b t (v t)) atTop (𝓝 L) := by
  have hbarrier := monotone_entry_barrier F hL hlocal b hmono hlim (fun t => v t-g) hv
  have herr : Tendsto (fun t => b t (v t)-(v t-g)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hbarrier ε hε,hv.eventually_const_lt hL] with t ht hvt
    have hlo := ht (v t) le_rfl
    have hhi : b t (v t) ≤ v t-g := by simpa only [max_eq_left hvt.le] using hbound t (v t)
    rw [Real.dist_eq,sub_zero,abs_of_nonpos (sub_nonpos.mpr hhi)]
    linarith
  have hh := herr.add hv
  simpa only [sub_add_cancel,zero_add] using hh

end FCAppendix.PayOnce
