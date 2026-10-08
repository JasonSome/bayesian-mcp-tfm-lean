import Mathlib

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace FCAppendix.Ample.DownstreamNormalizationCore

universe u v

structure AffineMenu (A : Type u) where
  failure : A → ℝ
  payment : A → ℝ
  failure_nonneg : ∀ a, 0 ≤ failure a
  payment_nonneg : ∀ a, 0 ≤ payment a

def IsEnvelope {A : Type u} (M : AffineMenu A) (f : ℝ → ℝ) : Prop :=
  ∀ w : ℝ, 0 ≤ w →
    (∀ a, f w ≤ w * M.failure a + M.payment a) ∧
    (∀ t : ℝ, (∀ a, t ≤ w * M.failure a + M.payment a) → t ≤ f w)

def IsBestReply {A : Type u} (M : AffineMenu A) (w : ℝ) (a : A) : Prop :=
  ∀ a', w * M.failure a + M.payment a ≤
    w * M.failure a' + M.payment a'

theorem envelope_monotone {A : Type u} {M : AffineMenu A}
    {f : ℝ → ℝ} (h : IsEnvelope M f) :
    MonotoneOn f (Ici 0) := by
  intro w hw y hy hwy
  apply (h y hy).2
  intro a
  calc
    f w ≤ w * M.failure a + M.payment a := (h w hw).1 a
    _ ≤ y * M.failure a + M.payment a :=
      add_le_add (mul_le_mul_of_nonneg_right hwy (M.failure_nonneg a)) le_rfl

theorem envelope_nonneg {A : Type u} {M : AffineMenu A}
    {f : ℝ → ℝ} (h : IsEnvelope M f) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ f w := by
  apply (h w hw).2
  intro a
  exact add_nonneg (mul_nonneg hw (M.failure_nonneg a))
    (M.payment_nonneg a)

theorem bestReply_touches {A : Type u} {M : AffineMenu A}
    {f : ℝ → ℝ} (h : IsEnvelope M f) {w : ℝ} (hw : 0 ≤ w)
    {a : A} (ha : IsBestReply M w a) :
    f w = w * M.failure a + M.payment a := by
  apply le_antisymm ((h w hw).1 a)
  exact (h w hw).2 _ ha

theorem touching_bound {A : Type u} {M : AffineMenu A}
    {f : ℝ → ℝ} (h : IsEnvelope M f) {w y : ℝ}
    (hw : 0 ≤ w) (hy : 0 ≤ y) {a : A}
    (ha : IsBestReply M w a) :
    f y ≤ f w + (y - w) * M.failure a := by
  calc
    f y ≤ y * M.failure a + M.payment a := (h y hy).1 a
    _ = f w + (y - w) * M.failure a := by
      rw [bestReply_touches h hw ha]
      ring

theorem exists_good_in_band {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (band : Set α) (P : α → Prop)
    (D : α → ℝ) (δ : ℝ)
    (hP : ∀ᵐ x ∂μ, P x)
    (hmass : μ {x | δ < D x} < μ band) :
    ∃ x, x ∈ band ∧ P x ∧ D x ≤ δ := by
  classical
  by_contra h
  have hnull : μ {x | ¬ P x} = 0 := by
    simpa only [ae_iff] using hP
  have hsub : band ⊆ {x | δ < D x} ∪ {x | ¬ P x} := by
    intro x hx
    by_cases hp : P x
    · left
      by_contra hd
      exact h ⟨x, hx, hp, le_of_not_gt hd⟩
    · exact Or.inr hp
  have hle : μ band ≤ μ {x | δ < D x} := by
    calc
      μ band ≤ μ ({x | δ < D x} ∪ {x | ¬ P x}) := measure_mono hsub
      _ ≤ μ {x | δ < D x} + μ {x | ¬ P x} := measure_union_le _ _
      _ = μ {x | δ < D x} := by rw [hnull, add_zero]
  exact (not_le_of_gt hmass) hle

theorem normalized_distance_le {f : ℝ → ℝ} {w z t d : ℝ}
    (hf : MonotoneOn f (Ici 0))
    (hw : 0 ≤ w) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (htw : t ≤ w) (htz : t ≤ z) (hd : 0 ≤ d)
    (hC : 0 < f z)
    (hTouch : ∀ y : ℝ, 0 ≤ y → f y ≤ f t + (y - t) * d) :
    |f w / f z - 1| ≤ max w z * (d / f z) := by
  have hdiff : |f w - f z| ≤ max w z * d := by
    rcases le_total w z with hwz | hzw
    · have hfwz := hf hw hz hwz
      have hftw := hf ht hw htw
      have htz' := hTouch z hz
      have htd : 0 ≤ t * d := mul_nonneg ht hd
      rw [abs_of_nonpos (sub_nonpos.mpr hfwz), max_eq_right hwz]
      nlinarith
    · have hfzw := hf hz hw hzw
      have hftz := hf ht hz htz
      have htw' := hTouch w hw
      have htd : 0 ≤ t * d := mul_nonneg ht hd
      rw [abs_of_nonneg (sub_nonneg.mpr hfzw), max_eq_left hzw]
      nlinarith
  calc
    |f w / f z - 1| = |(f w - f z) / f z| := by
      rw [sub_div, div_self (ne_of_gt hC)]
    _ = |f w - f z| / f z := by rw [abs_div, abs_of_pos hC]
    _ ≤ (max w z * d) / f z :=
      (div_le_div_iff_of_pos_right hC).2 hdiff
    _ = max w z * (d / f z) := by ring

section VaryingSpaces

variable {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]

def ProbZero (μ : (m : ℕ) → Measure (Ω m))
    (X : (m : ℕ) → Ω m → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
    ∀ᶠ m in atTop, μ m {ω | ε < |X m ω|} < ENNReal.ofReal η

def PositiveLowerBands (μ : (m : ℕ) → Measure (Ω m))
    (V : (m : ℕ) → Ω m → ℝ) (ell : ℝ) : Prop :=
  ∀ a : ℝ, ell < a →
    ∃ β : ℝ, 0 < β ∧
      ∀ m, ENNReal.ofReal β ≤ μ m {ω | V m ω ≤ a}

def CompactContainment (μ : (m : ℕ) → Measure (Ω m))
    (V : (m : ℕ) → Ω m → ℝ) (ell : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ a b : ℝ, ell < a ∧ a ≤ b ∧
      ∀ m, μ m {ω | V m ω < a ∨ b < V m ω} < ENNReal.ofReal η

variable {A : ℕ → Type v}

structure Request02UsedFailure
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (chosen : (m : ℕ) → Ω m → A m) (z : ℝ) : Prop where
  scale_pos : ∀ m, 0 < f m z
  failure_small :
    ProbZero μ (fun m ω => (M m).failure (chosen m ω) / f m z)

structure Request02NormalizationInput
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    (K S : (m : ℕ) → Ω m → ℝ) (z : ℝ) : Prop
    extends Request02UsedFailure μ M f chosen z where
  scale_small : Tendsto (fun m => f m z) atTop (𝓝 0)
  uniform_routed_acceptance :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      ∀ᵐ ω ∂μ m, 0 < K m ω → |S m ω / K m ω - 1| ≤ ε

theorem pointwise_deficit_normalization_of_band
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (V : (m : ℕ) → Ω m → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    {w z : ℝ} (hw : 0 ≤ w) (hz : 0 < z)
    (hE : ∀ m, IsEnvelope (M m) (f m))
    (hBest : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ V m ω ∧ IsBestReply (M m) (V m ω) (chosen m ω))
    (hUp : Request02UsedFailure μ M f chosen z)
    (hBand : ∃ β : ℝ, 0 < β ∧
      ∀ m, ENNReal.ofReal β ≤ μ m {ω | V m ω ≤ min w z}) :
    Tendsto (fun m => f m w / f m z) atTop (𝓝 1) := by
  have hw0 : 0 ≤ w := hw
  have hz0 : 0 ≤ z := le_of_lt hz
  have hL : 0 < max w z := lt_of_lt_of_le hz (le_max_right _ _)
  obtain ⟨β, hβ, hBandβ⟩ := hBand
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hδ : 0 < ε / (2 * max w z) := div_pos hε (mul_pos (by norm_num) hL)
  filter_upwards [hUp.failure_small (ε / (2 * max w z)) hδ β hβ] with m hm
  have hmass :
      μ m {ω | ε / (2 * max w z) <
        (M m).failure (chosen m ω) / f m z} <
      μ m {ω | V m ω ≤ min w z} := by
    calc
      μ m {ω | ε / (2 * max w z) <
          (M m).failure (chosen m ω) / f m z}
          ≤ μ m {ω | ε / (2 * max w z) <
            |(M m).failure (chosen m ω) / f m z|} := by
              apply measure_mono
              intro ω hω
              exact lt_of_lt_of_le
                (show ε / (2 * max w z) <
                  (M m).failure (chosen m ω) / f m z from hω) (le_abs_self _)
      _ < ENNReal.ofReal β := hm
      _ ≤ μ m {ω | V m ω ≤ min w z} := hBandβ m
  obtain ⟨ω, hωband, hωbest, hωsmall⟩ :=
    exists_good_in_band (μ m) {ω | V m ω ≤ min w z}
      (fun ω => 0 ≤ V m ω ∧ IsBestReply (M m) (V m ω) (chosen m ω))
      (fun ω => (M m).failure (chosen m ω) / f m z)
      (ε / (2 * max w z)) (hBest m) hmass
  have hbound :
      |f m w / f m z - 1| ≤ max w z *
        ((M m).failure (chosen m ω) / f m z) :=
    normalized_distance_le (envelope_monotone (hE m)) hw0 hz0 hωbest.1
      (le_trans hωband (min_le_left _ _))
      (le_trans hωband (min_le_right _ _))
      ((M m).failure_nonneg _) (hUp.scale_pos m)
      (fun y hy => touching_bound (hE m) hωbest.1 hy hωbest.2)
  have hsmall : |f m w / f m z - 1| < ε := by
    calc
      |f m w / f m z - 1|
          ≤ max w z * ((M m).failure (chosen m ω) / f m z) := hbound
      _ ≤ max w z * (ε / (2 * max w z)) :=
        mul_le_mul_of_nonneg_left hωsmall (le_of_lt hL)
      _ = ε / 2 := by field_simp [ne_of_gt hL]
      _ < ε := by linarith
  simpa only [Real.dist_eq] using hsmall

theorem pointwise_deficit_normalization
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (V : (m : ℕ) → Ω m → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    {ell z : ℝ} (hell : 0 ≤ ell) (hz : ell < z)
    (hE : ∀ m, IsEnvelope (M m) (f m))
    (hBest : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ V m ω ∧ IsBestReply (M m) (V m ω) (chosen m ω))
    (hBands : PositiveLowerBands μ V ell)
    (hUp : Request02UsedFailure μ M f chosen z)
    {w : ℝ} (hw : ell < w) :
    Tendsto (fun m => f m w / f m z) atTop (𝓝 1) := by
  apply pointwise_deficit_normalization_of_band μ M f V chosen
    (le_trans hell (le_of_lt hw)) (lt_of_le_of_lt hell hz) hE hBest hUp
  exact hBands (min w z) (lt_min hw hz)

theorem uniform_between_normalized_points
    (f : ℕ → ℝ → ℝ) {z a b : ℝ}
    (ha0 : 0 ≤ a) (_hab : a ≤ b)
    (hMono : ∀ m, MonotoneOn (f m) (Ici 0))
    (hC : ∀ m, 0 < f m z)
    (hPointA : Tendsto (fun m => f m a / f m z) atTop (𝓝 1))
    (hPointB : Tendsto (fun m => f m b / f m z) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ w ∈ Icc a b, |f m w / f m z - 1| < ε := by
  have hea := (Metric.tendsto_nhds.1 hPointA) ε hε
  have heb := (Metric.tendsto_nhds.1 hPointB) ε hε
  filter_upwards [hea, heb] with m hma hmb
  intro w hw
  have hw0 : 0 ≤ w := le_trans ha0 hw.1
  have hb0 : 0 ≤ b := le_trans hw0 hw.2
  have hlow : f m a / f m z ≤ f m w / f m z :=
    (div_le_div_iff_of_pos_right (hC m)).2 ((hMono m) ha0 hw0 hw.1)
  have hupp : f m w / f m z ≤ f m b / f m z :=
    (div_le_div_iff_of_pos_right (hC m)).2 ((hMono m) hw0 hb0 hw.2)
  rw [Real.dist_eq] at hma hmb
  rcases abs_lt.mp hma with ⟨hmaL, _⟩
  rcases abs_lt.mp hmb with ⟨_, hmbU⟩
  apply abs_lt.mpr
  constructor <;> linarith

theorem compact_uniform_normalization
    (f : ℕ → ℝ → ℝ) {ell z a b : ℝ}
    (hell : 0 ≤ ell) (ha : ell < a) (hab : a ≤ b)
    (hMono : ∀ m, MonotoneOn (f m) (Ici 0))
    (hC : ∀ m, 0 < f m z)
    (hPoint : ∀ w : ℝ, ell < w →
      Tendsto (fun m => f m w / f m z) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ w ∈ Icc a b, |f m w / f m z - 1| < ε :=
  uniform_between_normalized_points f (le_trans hell (le_of_lt ha)) hab
    hMono hC (hPoint a ha) (hPoint b (lt_of_lt_of_le ha hab)) hε

theorem random_deficit_normalization
    (μ : (m : ℕ) → Measure (Ω m))
    (V : (m : ℕ) → Ω m → ℝ)
    (f : ℕ → ℝ → ℝ) {ell z : ℝ}
    (hell : 0 ≤ ell)
    (hMono : ∀ m, MonotoneOn (f m) (Ici 0))
    (hC : ∀ m, 0 < f m z)
    (hPoint : ∀ w : ℝ, ell < w →
      Tendsto (fun m => f m w / f m z) atTop (𝓝 1))
    (hCompact : CompactContainment μ V ell) :
    ProbZero μ (fun m ω => f m (V m ω) / f m z - 1) := by
  intro ε hε η hη
  obtain ⟨a, b, ha, hab, htail⟩ := hCompact η hη
  filter_upwards
    [compact_uniform_normalization f hell ha hab hMono hC hPoint hε] with m hm
  apply lt_of_le_of_lt _ (htail m)
  apply measure_mono
  intro ω hω
  by_cases hlo : V m ω < a
  · exact Or.inl hlo
  by_cases hhi : b < V m ω
  · exact Or.inr hhi
  have hgood := hm (V m ω) ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩
  exact False.elim ((not_lt_of_ge (le_of_lt hgood)) hω)

end VaryingSpaces
end FCAppendix.Ample.DownstreamNormalizationCore
