import FCAppendix.Probability.GaussianMeanConvergence
import Mathlib.Topology.Sequences

namespace FCAppendix.Probability
open Set Filter Topology

theorem eventually_uniform_abs_lt_of_compact_sequences
    {S : Set ℝ} (hS : IsCompact S) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hg : ContinuousOn g S)
    (h : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      ∀ y : ℕ → ℝ, ∀ z ∈ S, (∀ t, y t ∈ S) → Tendsto y atTop (𝓝 z) →
        Tendsto (fun t => f (φ t) (y t)) atTop (𝓝 (g z)))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, ∀ y ∈ S, |f t y-g y| < ε := by
  apply eventually_uniform_abs_lt_of_all_choices S (fun t y => f t y-g y) _ hε
  intro y hy
  apply tendsto_of_subseq_tendsto
  intro φ hφ
  obtain ⟨z,hz,χ,hχ,hconv⟩ := hS.isSeqCompact (fun t => hy (φ t))
  have hf := h (φ ∘ χ) (hφ.comp hχ.tendsto_atTop) (y ∘ φ ∘ χ) z hz
    (fun t => hy (φ (χ t))) hconv
  have hg' : Tendsto (fun t => g (y (φ (χ t)))) atTop (𝓝 (g z)) :=
    (hg z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hconv,.of_forall fun t => hy (φ (χ t))⟩)
  refine ⟨χ,?_⟩
  simpa only [sub_self,Function.comp_def] using hf.sub hg'

theorem eventually_uniform_abs_lt_of_compact_admissible_sequences
    {S : Set ℝ} (hS : IsCompact S) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (A : ℕ → ℝ → Prop) (hg : ContinuousOn g S)
    (h : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      ∀ y : ℕ → ℝ, ∀ z ∈ S, (∀ t, y t ∈ S) →
        (∀ᶠ t in atTop, A (φ t) (y t)) → Tendsto y atTop (𝓝 z) →
          Tendsto (fun t => f (φ t) (y t)) atTop (𝓝 (g z)))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, ∀ y ∈ S, A t y → |f t y-g y| < ε := by
  classical
  by_contra hn
  have hfreq : ∃ᶠ t in atTop, ∃ y ∈ S, A t y ∧ ε ≤ |f t y-g y| := by
    simpa only [not_eventually,not_forall,not_lt,exists_prop] using hn
  obtain ⟨φ,hφ,hbad⟩ := extraction_of_frequently_atTop hfreq
  choose y hyS hyA hybad using hbad
  obtain ⟨z,hz,χ,hχ,hconv⟩ := hS.isSeqCompact hyS
  have hf := h (φ ∘ χ) (hφ.tendsto_atTop.comp hχ.tendsto_atTop) (y ∘ χ) z hz
    (fun t => hyS (χ t)) (.of_forall fun t => hyA (χ t)) hconv
  have hg' : Tendsto (fun t => g (y (χ t))) atTop (𝓝 (g z)) :=
    (hg z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hconv,.of_forall fun t => hyS (χ t)⟩)
  have he := (Metric.tendsto_nhds.mp (hf.sub hg')) ε hε
  obtain ⟨t,ht⟩ := he.exists
  simp only [sub_self,Real.dist_eq,sub_zero,Function.comp_def] at ht
  exact (not_lt_of_ge (hybad (χ t))) ht

theorem eventually_uniform_abs_lt_of_compact_labeled_sequences
    {S : Set ℝ} (hS : IsCompact S) {β : ℕ → Type*}
    (f : (t : ℕ) → ℝ → β t → ℝ) (g : ℝ → ℝ)
    (A : (t : ℕ) → ℝ → β t → Prop) (hg : ContinuousOn g S)
    (h : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      ∀ y : ℕ → ℝ, ∀ z ∈ S, (∀ t, y t ∈ S) → ∀ b : ∀ t, β (φ t),
        (∀ᶠ t in atTop, A (φ t) (y t) (b t)) → Tendsto y atTop (𝓝 z) →
          Tendsto (fun t => f (φ t) (y t) (b t)) atTop (𝓝 (g z)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ y ∈ S, ∀ b : β t, A t y b → |f t y b-g y| < ε := by
  classical
  by_contra hn
  have hfreq : ∃ᶠ t in atTop, ∃ y ∈ S, ∃ b : β t, A t y b ∧ ε ≤ |f t y b-g y| := by
    simpa only [not_eventually,not_forall,not_lt,exists_prop] using hn
  obtain ⟨φ,hφ,hbad⟩ := extraction_of_frequently_atTop hfreq
  choose y hyS b hyA hybad using hbad
  obtain ⟨z,hz,χ,hχ,hconv⟩ := hS.isSeqCompact hyS
  have hf := h (φ ∘ χ) (hφ.tendsto_atTop.comp hχ.tendsto_atTop) (y ∘ χ) z hz
    (fun t => hyS (χ t)) (fun t => b (χ t)) (.of_forall fun t => hyA (χ t)) hconv
  have hg' : Tendsto (fun t => g (y (χ t))) atTop (𝓝 (g z)) :=
    (hg z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hconv,.of_forall fun t => hyS (χ t)⟩)
  have he := (Metric.tendsto_nhds.mp (hf.sub hg')) ε hε
  obtain ⟨t,ht⟩ := he.exists
  simp only [sub_self,Real.dist_eq,sub_zero,Function.comp_def] at ht
  exact (not_lt_of_ge (hybad (χ t))) ht

end FCAppendix.Probability
