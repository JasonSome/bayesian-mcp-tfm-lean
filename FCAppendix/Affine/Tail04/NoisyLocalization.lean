import FCAppendix.Existence.R01Distributional
import Mathlib.MeasureTheory.Measure.Portmanteau

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Filter Topology

section Algebra
variable {T A : Type*}

theorem reference_gap_improves_noisy {u reference : T × A → ℝ}
    {x : T × A} {a : A} {err gap : ℝ}
    (hinc : |u x - reference x| ≤ err)
    (htest : |u (x.1, a) - reference (x.1, a)| ≤ err)
    (hgap : gap ≤ reference (x.1, a) - reference x)
    (hmargin : 2 * err < gap) :
    u x < u (x.1, a) := by
  rcases abs_le.mp hinc with ⟨hincL, hincU⟩
  rcases abs_le.mp htest with ⟨htestL, htestU⟩
  linarith

end Algebra

section NoisyIC
variable {T A : Type*} [MeasurableSpace T] [MeasurableSpace A]

theorem noisy_IC_excludes_reference_gap
    (ν : Measure (T × A)) (u reference : T × A → ℝ)
    (test : T × A → A) (bad : Set (T × A)) (err gap : ℝ)
    (happrox : ∀ x, |u x - reference x| ≤ err)
    (hgap : ∀ x ∈ bad, gap ≤ reference (x.1, test x) - reference x)
    (hmargin : 2 * err < gap)
    (hIC : ∀ᵐ x ∂ν, ∀ a : A, u (x.1, a) ≤ u x) :
    ν bad = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hIC] with x hx
  intro hbad
  have himprove := reference_gap_improves_noisy (happrox x)
    (happrox (x.1, test x)) (hgap x hbad) hmargin
  exact (not_lt_of_ge (hx (test x))) himprove

theorem noisy_IC_excludes_value_weighted_gap
    (ν : Measure (T × A)) (u reference : T × A → ℝ)
    (test : T × A → A) (bad : Set (T × A)) (err gap : T → ℝ)
    (happrox : ∀ x, |u x - reference x| ≤ err x.1)
    (hgap : ∀ x ∈ bad, gap x.1 ≤ reference (x.1, test x) - reference x)
    (hmargin : ∀ x ∈ bad, 2 * err x.1 < gap x.1)
    (hIC : ∀ᵐ x ∂ν, ∀ a : A, u (x.1, a) ≤ u x) :
    ν bad = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hIC] with x hx
  intro hbad
  have himprove := reference_gap_improves_noisy (happrox x)
    (happrox (x.1, test x)) (hgap x hbad) (hmargin x hbad)
  exact (not_lt_of_ge (hx (test x))) himprove

end NoisyIC

section WeakSupport
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem closed_support_of_noisy_support
    (ν : ℕ → ProbabilityMeasure X) (ν₀ : ProbabilityMeasure X)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (C : Set X) (hC : IsClosed C)
    (hsupport : ∀ j, ∀ᵐ x ∂(ν j : Measure X), x ∈ C) :
    ∀ᵐ x ∂(ν₀ : Measure X), x ∈ C := by
  have hzero (j : ℕ) : (ν j : Measure X) Cᶜ = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact (hsupport j).mono (fun _ hx hxc => hxc hx)
  have hliminf := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν hC.isOpen_compl
  simp_rw [hzero] at hliminf
  rw [liminf_const] at hliminf
  have hz : (ν₀ : Measure X) Cᶜ = 0 := le_antisymm hliminf bot_le
  exact (measure_eq_zero_iff_ae_notMem.mp hz).mono (fun _ hx => by simpa using hx)

end WeakSupport

end FCAppendix.Affine.Tail04
