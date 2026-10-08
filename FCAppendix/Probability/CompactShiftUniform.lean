import FCAppendix.Probability.CompactSequentialUniform

namespace FCAppendix.Probability
open Set Filter Topology

theorem tendsto_of_compact_uniform_labeled
    {β : ℕ → Type*} (f : (t : ℕ) → ℝ → β t → ℝ) (g : ℝ → ℝ)
    (A : (t : ℕ) → ℝ → β t → Prop) (hg : Continuous g)
    (h : ∀ S : Set ℝ, IsCompact S → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t in atTop, ∀ x ∈ S, ∀ b : β t, A t x b → |f t x b-g x| < ε)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (x : ℕ → ℝ) {x₀ : ℝ}
    (hx : Tendsto x atTop (𝓝 x₀)) (b : ∀ t, β (φ t))
    (hA : ∀ᶠ t in atTop, A (φ t) (x t) (b t)) :
    Tendsto (fun t => f (φ t) (x t) (b t)) atTop (𝓝 (g x₀)) := by
  have hb := hx.eventually (Icc_mem_nhds (by linarith : x₀-1 < x₀) (by linarith : x₀ < x₀+1))
  have he : Tendsto (fun t => f (φ t) (x t) (b t)-g (x t)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hφ.eventually (h (Icc (x₀-1) (x₀+1)) isCompact_Icc ε hε),hb,hA] with t ht hxt hAt
    simpa only [Real.dist_eq,sub_zero] using ht (x t) hxt (b t) hAt
  have hh := he.add (hg.continuousAt.tendsto.comp hx)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hh

theorem eventually_uniform_shifted_abs_lt
    {β : ℕ → Type*} (f : (t : ℕ) → ℝ → β t → ℝ) (g : ℝ → ℝ)
    (A : (t : ℕ) → ℝ → β t → Prop) (hg : Continuous g)
    (h : ∀ S : Set ℝ, IsCompact S → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t in atTop, ∀ x ∈ S, ∀ b : β t, A t x b → |f t x b-g x| < ε)
    (δ e : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ x ∈ S, ∀ b : β t, A t (x+δ t) b →
      |f t (x+δ t) b+e t-g x| < ε := by
  apply eventually_uniform_abs_lt_of_compact_labeled_sequences hS _ _ _ hg.continuousOn ?_ hε
  intro φ hφ x x₀ _hx₀ _hxS b hA hx
  have hx' : Tendsto (fun t => x t+δ (φ t)) atTop (𝓝 x₀) := by simpa using hx.add (hδ.comp hφ)
  have hh := (tendsto_of_compact_uniform_labeled f g A hg h φ hφ _ hx' b hA).add (he.comp hφ)
  simpa only [Function.comp_def,add_zero] using hh

end FCAppendix.Probability
