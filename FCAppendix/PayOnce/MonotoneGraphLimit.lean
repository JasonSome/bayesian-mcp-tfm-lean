import FCAppendix.PayOnce.MonotoneExcludedBids

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory Set Filter Topology

theorem ae_right_interval_pos (F : Measure ℝ) [NullSingletonClass F] :
    ∀ᵐ v ∂F, ∀ a, v < a → 0 < F (Ioo v a) := by
  have hacc := SupportedFOC.ae_two_sided_accumulation F (Measure.support_mem_ae (μ := F))
  filter_upwards [hacc] with v hv a ha
  letI : (𝓝[F.support ∩ Ioi v] v).NeBot := hv.2
  have hs : ∀ᶠ y in 𝓝[F.support ∩ Ioi v] v, y ∈ F.support ∩ Ioi v := self_mem_nhdsWithin
  have hl : ∀ᶠ y in 𝓝[F.support ∩ Ioi v] v, y < a :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ha)
  obtain ⟨y,hy,hya⟩ := (hs.and hl).exists
  exact (Measure.mem_support_iff_forall (μ := F) y).mp hy.1 _ (Ioo_mem_nhds hy.2 hya)

theorem ae_monotone_limit_of_defect_mass
    (F : Measure ℝ) [NullSingletonClass F]
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (f : ℝ → ℝ) (hf : Continuous f)
    (hdefect : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun t => F {v | δ ≤ |b t v-f v|}) atTop (𝓝 0)) :
    ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop (𝓝 (f v)) := by
  filter_upwards [ae_left_interval_pos F,ae_right_interval_pos F] with v hvleft hvright
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let δ := (f v-r)/2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    obtain ⟨ε,hε,he⟩ := Metric.continuousAt_iff.mp hf.continuousAt δ hδ
    have hmass : 0 < F (Ioo (v-ε) v) := hvleft (v-ε) (by linarith)
    filter_upwards [(hdefect δ hδ).eventually_lt_const hmass] with t ht
    by_contra hn
    have hb : b t v ≤ r := le_of_not_gt hn
    have hsub : Ioo (v-ε) v ⊆ {x | δ ≤ |b t x-f x|} := by
      intro x hx
      have hd : dist x v < ε := by rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hx.2)]; linarith [hx.1]
      have hfx := (abs_lt.mp (show |f x-f v| < δ from he hd)).1
      have hbx := (hmono t hx.2.le).trans hb
      have hh := le_abs_self (f x-b t x)
      rw [abs_sub_comm (f x)] at hh
      change δ ≤ |b t x-f x|
      dsimp only [δ] at hfx ⊢
      linarith
    exact ht.not_ge (measure_mono hsub)
  · intro r hr
    let δ := (r-f v)/2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    obtain ⟨ε,hε,he⟩ := Metric.continuousAt_iff.mp hf.continuousAt δ hδ
    have hmass : 0 < F (Ioo v (v+ε)) := hvright (v+ε) (by linarith)
    filter_upwards [(hdefect δ hδ).eventually_lt_const hmass] with t ht
    by_contra hn
    have hb : r ≤ b t v := le_of_not_gt hn
    have hsub : Ioo v (v+ε) ⊆ {x | δ ≤ |b t x-f x|} := by
      intro x hx
      have hd : dist x v < ε := by rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hx.1)]; linarith [hx.2]
      have hfx := (abs_lt.mp (show |f x-f v| < δ from he hd)).2
      have hbx := hb.trans (hmono t hx.1.le)
      have hh := le_abs_self (b t x-f x)
      change δ ≤ |b t x-f x|
      dsimp only [δ] at hfx ⊢
      linarith
    exact ht.not_ge (measure_mono hsub)

end FCAppendix.PayOnce.VanishingBidIC
