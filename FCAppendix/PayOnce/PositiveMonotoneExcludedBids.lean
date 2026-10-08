import FCAppendix.PayOnce.MonotoneExcludedBids

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory Set Filter Topology

theorem ae_positive_left_interval_pos (F : Measure ℝ) {g : ℝ}
    (hatom : ∀ v : ℝ, g < v → F {v} = 0) :
    ∀ᵐ v ∂F, g < v → ∀ a < v, 0 < F (Ioo a v) := by
  haveI : NullSingletonClass (F.restrict (Ioi g)) := by
    constructor
    intro v
    rw [Measure.restrict_apply (measurableSet_singleton v)]
    by_cases hv : g < v
    · rw [singleton_inter_of_mem (show v ∈ Ioi g from hv),hatom v hv]
    · rw [singleton_inter_of_notMem (show v ∉ Ioi g from hv),measure_empty]
  have hh := (ae_restrict_iff' measurableSet_Ioi).mp (ae_left_interval_pos (F.restrict (Ioi g)))
  filter_upwards [hh] with v hv hpos a ha
  have hm := hv hpos a ha
  rw [Measure.restrict_apply measurableSet_Ioo] at hm
  exact hm.trans_le (measure_mono inter_subset_left)

theorem ae_positive_excluded_bid_limit_of_surplus_mass
    (F : Measure ℝ) {g : ℝ}
    (hatom : ∀ v : ℝ, g < v → F {v} = 0)
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    {L : ℝ} (hbound : ∀ t v, b t v ≤ max (v-g) 0)
    (hdefect : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun t => F {v | δ ≤ v-g-b t v ∧ b t v ≤ L}) atTop (𝓝 0)) :
    ∀ᵐ v ∂F, g < v → v-g ≤ L → Tendsto (fun t => b t v) atTop (𝓝 (v-g)) := by
  filter_upwards [ae_positive_left_interval_pos F hatom] with v hv hvg hvL
  have hv := hv hvg
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let a := (r+g+v)/2
    have ha : a < v := by dsimp only [a]; linarith
    have hδ : 0 < a-g-r := by dsimp only [a]; linarith
    have ht := (hdefect (a-g-r) hδ).eventually_lt_const (hv a ha)
    filter_upwards [ht] with t ht
    by_contra hn
    have hsub : Ioo a v ⊆ {x | a-g-r ≤ x-g-b t x ∧ b t x ≤ L} := by
      intro x hx
      have hbx : b t x ≤ r := (hmono t hx.2.le).trans (le_of_not_gt hn)
      constructor
      · linarith [hx.1]
      · exact hbx.trans (hr.le.trans hvL)
    exact ht.not_ge (measure_mono hsub)
  · intro r hr
    apply Filter.Eventually.of_forall
    intro t
    have hb := hbound t v
    rw [max_eq_left (sub_pos.mpr hvg).le] at hb
    exact hb.trans_lt hr

end FCAppendix.PayOnce.VanishingBidIC
