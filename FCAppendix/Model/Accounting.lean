import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace FCAppendix

def successIndicator (K : ℕ) : ℝ := if K = 0 then 0 else 1

def userPayoff (v b g : ℝ) (A G : ℕ → ℝ) (K : ℕ) : ℝ :=
  v * successIndicator K - b * A K - g * G K

def duplicateLoad (coverage load : ℝ) : ℝ := load - coverage

noncomputable def conditionalMultiplicity (coverage load : ℝ) : ℝ := load / coverage

theorem userPayoff_zero (v b g : ℝ) (A G : ℕ → ℝ)
    (hA : A 0 = 0) (hG : G 0 = 0) : userPayoff v b g A G 0 = 0 := by
  simp [userPayoff, successIndicator, hA, hG]

theorem coverage_add_duplicateLoad (coverage load : ℝ) :
    coverage + duplicateLoad coverage load = load := by
  unfold duplicateLoad
  ring

theorem conditionalMultiplicity_mul_coverage (coverage load : ℝ)
    (h : coverage ≠ 0) : conditionalMultiplicity coverage load * coverage = load := by
  unfold conditionalMultiplicity
  field_simp

end FCAppendix
