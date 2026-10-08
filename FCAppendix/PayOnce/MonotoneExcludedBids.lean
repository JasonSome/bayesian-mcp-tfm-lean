import FCAppendix.PayOnce.ExcludedSurplusLimit

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory Set Filter Topology

theorem ae_left_interval_pos (F : Measure ℝ) [NullSingletonClass F] :
    ∀ᵐ v ∂F, ∀ a < v, 0 < F (Ioo a v) := by
  have hacc := SupportedFOC.ae_two_sided_accumulation F (Measure.support_mem_ae (μ := F))
  filter_upwards [hacc] with v hv a ha
  letI : (𝓝[F.support ∩ Iio v] v).NeBot := hv.1
  have hs : ∀ᶠ y in 𝓝[F.support ∩ Iio v] v, y ∈ F.support ∩ Iio v := self_mem_nhdsWithin
  have hl : ∀ᶠ y in 𝓝[F.support ∩ Iio v] v, a < y :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha)
  obtain ⟨y,hy,hay⟩ := (hs.and hl).exists
  exact (Measure.mem_support_iff_forall (μ := F) y).mp hy.1 _ (Ioo_mem_nhds hay hy.2)

theorem ae_excluded_bid_limit_of_surplus_mass
    (F : Measure ℝ) [NullSingletonClass F]
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    {g L : ℝ} (hbound : ∀ t v, b t v ≤ max (v-g) 0)
    (hdefect : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun t => F {v | δ ≤ v-g-b t v ∧ b t v ≤ L}) atTop (𝓝 0)) :
    ∀ᵐ v ∂F, g < v → v-g ≤ L → Tendsto (fun t => b t v) atTop (𝓝 (v-g)) := by
  filter_upwards [ae_left_interval_pos F] with v hv hvg hvL
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
