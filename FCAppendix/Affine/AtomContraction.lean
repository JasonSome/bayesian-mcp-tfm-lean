import FCAppendix.Probability.FiniteLaw

namespace FCAppendix
namespace Affine

theorem no_positive_atoms (mass : ℝ → ℝ) (ε κ : ℝ)
    (h0 : ∀ b, 0 ≤ mass b) (h1 : ∀ b, mass b ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (hκ : 0 < κ)
    (hcontract : ∀ b, 0 < b → mass b ≤ ε * (mass b + mass (κ * b))) :
    ∀ b, 0 < b → mass b = 0 := by
  let R : Set ℝ := {x | ∃ b : ℝ, 0 < b ∧ x = mass b}
  have hR : R.Nonempty := ⟨mass 1, 1, by norm_num, rfl⟩
  have hbdd : BddAbove R := ⟨1, by
    rintro x ⟨b, _, rfl⟩
    exact h1 b⟩
  let M : ℝ := sSup R
  have hle : ∀ b, 0 < b → mass b ≤ M := by
    intro b hb
    exact le_csSup hbdd ⟨b, hb, rfl⟩
  have hM0 : 0 ≤ M := le_trans (h0 1) (hle 1 (by norm_num))
  have hM : M ≤ 2 * ε * M := by
    apply csSup_le hR
    rintro x ⟨b, hb, rfl⟩
    have hbM := hle b hb
    have hkM := hle (κ * b) (mul_pos hκ hb)
    have hc := hcontract b hb
    have hs := mul_le_mul_of_nonneg_left (add_le_add hbM hkM) hε0
    nlinarith
  have hzero : M = 0 := by nlinarith
  intro b hb
  exact le_antisymm (by simpa [hzero] using hle b hb) (h0 b)

theorem coverage_from_receipts (P a β Q T : ℝ)
    (hP : 0 < P) (hlo : a ^ 2 * P * β ≤ T) (hhi : T ≤ P * Q) :
    a ^ 2 * β ≤ Q := by
  exact le_of_mul_le_mul_left (by nlinarith) hP

theorem duplicate_from_coverage (β Q D a : ℝ)
    (hD : D = β - Q) (hQ : β * a ^ 2 ≤ Q) : D ≤ β * (1 - a ^ 2) := by
  rw [hD]
  nlinarith

end Affine
end FCAppendix
