import FCAppendix.PayOnce.MonotoneGraphLimit

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory Set Filter Topology

theorem ae_positive_monotone_limit_of_defect_mass
    (F : Measure ℝ) {g : ℝ}
    (hatom : ∀ v : ℝ, g < v → F {v} = 0)
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (f : ℝ → ℝ) (hf : Continuous f)
    (hdefect : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun t => F {v | δ ≤ |b t v-f v|}) atTop (𝓝 0)) :
    ∀ᵐ v ∂F, g < v → Tendsto (fun t => b t v) atTop (𝓝 (f v)) := by
  haveI : NullSingletonClass (F.restrict (Ioi g)) := by
    constructor
    intro v
    rw [Measure.restrict_apply (measurableSet_singleton v)]
    by_cases hv : g < v
    · rw [singleton_inter_of_mem (show v ∈ Ioi g from hv),hatom v hv]
    · rw [singleton_inter_of_notMem (show v ∉ Ioi g from hv),measure_empty]
  apply (ae_restrict_iff' measurableSet_Ioi).mp
  apply ae_monotone_limit_of_defect_mass (F.restrict (Ioi g)) b hmono f hf
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hdefect δ hδ)
    (fun _ => bot_le) ?_
  intro t
  exact Measure.restrict_le_self _

end FCAppendix.PayOnce.VanishingBidIC
