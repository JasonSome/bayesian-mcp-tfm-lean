import FCAppendix.Finite.Envelope

namespace FCAppendix
namespace Interim
namespace Problem

variable {n : ℕ}

theorem success_near_affine_slope (P : Problem n) (v h ε slope intercept : ℝ)
    (hh : 0 < h) (a : Game.JointAction n) (ha : P.BestResponse v a)
    (hcenter : |P.envelope v - (slope * v + intercept)| ≤ ε)
    (hleft : |P.envelope (v - h) - (slope * (v - h) + intercept)| ≤ ε)
    (hright : |P.envelope (v + h) - (slope * (v + h) + intercept)| ≤ ε) :
    slope - 2 * ε / h ≤ (P.outcome a).success ∧
      (P.outcome a).success ≤ slope + 2 * ε / h := by
  rcases abs_le.mp hcenter with ⟨hc0, hc1⟩
  rcases abs_le.mp hleft with ⟨hl0, hl1⟩
  rcases abs_le.mp hright with ⟨hr0, hr1⟩
  have hsL := P.supporting_line v a ha (v - h)
  have hsR := P.supporting_line v a ha (v + h)
  have he : (2 * ε / h) * h = 2 * ε := div_mul_cancel₀ _ (ne_of_gt hh)
  constructor
  · by_contra hnot
    have hlt : (P.outcome a).success < slope - 2 * ε / h := lt_of_not_ge hnot
    have hp := mul_pos hh (sub_pos.mpr hlt)
    nlinarith
  · by_contra hnot
    have hlt : slope + 2 * ε / h < (P.outcome a).success := lt_of_not_ge hnot
    have hp := mul_pos hh (sub_pos.mpr hlt)
    nlinarith

theorem positive_duplicate_penalty_contradiction
    (u w b S D H g δ ε : ℝ)
    (hb : 0 < b) (hD : δ ≤ D) (hH : 0 ≤ H) (hg : 0 ≤ g)
    (hS : S ≤ 1) (hmargin : 0 ≤ w - b)
    (hu : u = (w - b) * S - b * D - g * H)
    (hlower : w - b - ε ≤ u) (hgap : ε < b * δ) : False := by
  have hp := mul_nonneg hg hH
  have hBD := mul_le_mul_of_nonneg_left hD (le_of_lt hb)
  have hWS : (w - b) * S ≤ w - b := by nlinarith
  nlinarith

end Problem
end Interim
end FCAppendix
