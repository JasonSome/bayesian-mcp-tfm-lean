import FCAppendix.Affine.Hybrid.SourceCountBounds

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Classical
open Affine.LowBody

lemma low_count_positive_of_close {M LB : ℕ} {s δ : ℝ}
    (hM : 0 < M) (hδs : δ < s) (hclose : |(LB : ℝ)-(M : ℝ)*s| < M*δ) : 1 ≤ LB := by
  have hm : (0:ℝ) < M := Nat.cast_pos.mpr hM
  by_contra hz
  have hzero : LB=0 := by omega
  rw [hzero,Nat.cast_zero,zero_sub,abs_neg] at hclose
  have hh := le_abs_self ((M : ℝ)*s)
  have hmul := mul_lt_mul_of_pos_left hδs hm
  linarith

lemma low_count_positive_of_not_exception (s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G] {r N : ℕ}
    (fixed : Fin r → Fin 4) (row : Fin N → Fin 4) {δ : ℝ}
    (hM : 0 < N+r) (hδs : δ < s)
    (hgood : ¬ ∃ k : Fin 4, (N+r : ℕ)*δ ≤
      |(categoryCount k fixed : ℝ)+(categoryCount k row : ℝ)-
        (N+r : ℕ)*(categoryLaw s a h hs ha hh hsum G).mass k|) :
    1 ≤ fullCategoryCount fixed row 0 := by
  apply low_count_positive_of_close hM hδs
  have hg : |(categoryCount 0 fixed : ℝ)+(categoryCount 0 row : ℝ)-
      (N+r : ℕ)*(categoryLaw s a h hs ha hh hsum G).mass 0| < (N+r : ℕ)*δ :=
    lt_of_not_ge (fun he => hgood ⟨0,he⟩)
  simpa [fullCategoryCount,categoryLaw_mass] using hg

theorem low_seed_unavailable_probability_le (s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G] {r : ℕ}
    (fixed : Fin r → Fin 4) (N : ℕ) (hM : 0 < N+r) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδs : δ < s) (hprefix : (r : ℝ) ≤ (N : ℝ)*δ/2) :
    (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob
      (fun row => fullCategoryCount fixed row 0=0) ≤ 8*Real.exp (-(N : ℝ)*δ^2/2) := by
  have hb := forced_fractional_count_exception_le (categoryLaw s a h hs ha hh hsum G) fixed N hδ hprefix
  apply le_trans ?_ hb
  apply FiniteLaw.prob_mono
  intro row hzero
  by_contra hgood
  have hp := low_count_positive_of_not_exception s a h hs ha hh hsum G fixed row hM hδs hgood
  omega

end FCAppendix.Affine.Hybrid
