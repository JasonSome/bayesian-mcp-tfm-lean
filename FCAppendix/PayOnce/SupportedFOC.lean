import FCAppendix.PayOnce.Sorting

namespace FCAppendix.PayOnce.SupportedFOC

open MeasureTheory Filter Topology Set

theorem ae_two_sided_accumulation (μ : Measure ℝ) [NullSingletonClass μ]
    {S : Set ℝ} (hS : ∀ᵐ b ∂μ, b ∈ S) :
    ∀ᵐ b ∂μ, (𝓝[S ∩ Iio b] b).NeBot ∧ (𝓝[S ∩ Ioi b] b).NeBot := by
  have hleft := (countable_setOf_isolated_left_within (s := S)).ae_notMem μ
  have hright := (countable_setOf_isolated_right_within (s := S)).ae_notMem μ
  filter_upwards [hS, hleft, hright] with b hb hl hr
  exact ⟨⟨fun he => hl ⟨hb, he⟩⟩, ⟨fun he => hr ⟨hb, he⟩⟩⟩

theorem derivative_zero_on_two_sided_set {f : ℝ → ℝ} {f' b : ℝ} {S : Set ℝ}
    (hf : HasDerivAt f f' b)
    (hl : (𝓝[S ∩ Iio b] b).NeBot) (hr : (𝓝[S ∩ Ioi b] b).NeBot)
    (hmax : ∀ x ∈ S, f x ≤ f b) : f' = 0 := by
  letI := hl
  letI := hr
  apply le_antisymm
  · have ht := hf.tendsto_slope.mono_left
      (nhdsWithin_mono b (show S ∩ Ioi b ⊆ {b}ᶜ from fun x hx => ne_of_gt hx.2))
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmax x hx.1))
      (sub_nonneg.mpr hx.2.le)
  · have ht := hf.tendsto_slope.mono_left
      (nhdsWithin_mono b (show S ∩ Iio b ⊆ {b}ᶜ from fun x hx => ne_of_lt hx.2))
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr (hmax x hx.1))
      (sub_nonpos.mpr hx.2.le)

theorem payOnce_first_order_condition {Q : ℝ → ℝ} {Q' b w : ℝ} {S : Set ℝ}
    (hQ : HasDerivAt Q Q' b)
    (hl : (𝓝[S ∩ Iio b] b).NeBot) (hr : (𝓝[S ∩ Ioi b] b).NeBot)
    (hmax : ∀ x ∈ S, (w - x) * Q x ≤ (w - b) * Q b) :
    Q b = (w - b) * Q' := by
  have hh := (((hasDerivAt_id b).const_sub w).mul hQ)
  have hz := derivative_zero_on_two_sided_set hh hl hr hmax
  dsimp only [id_eq] at hz
  linarith

end FCAppendix.PayOnce.SupportedFOC
