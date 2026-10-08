import FCAppendix.Game.LocalInformation

namespace FCAppendix
namespace Finite

theorem success_difference_nested (K J : ℕ) (h : K ≤ J) :
    successIndicator J - successIndicator K = if K = 0 ∧ 0 < J then 1 else 0 := by
  by_cases hK : K = 0
  · subst K
    by_cases hJ : J = 0
    · simp [hJ, successIndicator]
    · simp [hJ, Nat.pos_of_ne_zero hJ, successIndicator]
  · have hJ : J ≠ 0 := by omega
    simp [hK, hJ, successIndicator]

theorem once_route_gain {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (K J : Ω → ℕ) (h : ∀ ω, K ω ≤ J ω) (v b g : ℝ) :
    μ.expect (fun ω => userPayoff v b g successIndicator successIndicator (J ω)) -
      μ.expect (fun ω => userPayoff v b g successIndicator successIndicator (K ω)) =
      (v - b - g) * μ.prob (fun ω => K ω = 0 ∧ 0 < J ω) := by
  classical
  rw [← μ.expect_sub]
  calc
    _ = μ.expect (fun ω => (v - b - g) *
        (successIndicator (J ω) - successIndicator (K ω))) := by
      apply μ.expect_congr
      intro ω
      unfold userPayoff
      ring
    _ = _ := by
      simp_rw [success_difference_nested _ _ (h _)]
      rw [μ.expect_const_mul, FiniteLaw.prob_eq_expect]

theorem once_route_gain_strict {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (K J : Ω → ℕ) (h : ∀ ω, K ω ≤ J ω) (v b g : ℝ)
    (hs : 0 < v - b - g) (hr : 0 < μ.prob (fun ω => K ω = 0 ∧ 0 < J ω)) :
    μ.expect (fun ω => userPayoff v b g successIndicator successIndicator (K ω)) <
      μ.expect (fun ω => userPayoff v b g successIndicator successIndicator (J ω)) := by
  have he := once_route_gain μ K J h v b g
  have hp := mul_pos hs hr
  linarith

theorem ppi_same_bid_identity (k q S b g w H : ℝ) :
    k * ((w - b) * q) - ((w - b) * S - b * (k * q - S) - g * H) =
      w * (k * q - S) + g * H := by ring

theorem receipt_shortfall_bound (v g p S L T e : ℝ)
    (hT : p * L - e ≤ T) :
    (v - g) * S - T ≤ (v - g - p) * S - p * (L - S) + e := by
  nlinarith

theorem costly_copy_exclusion (w d q0 : ℝ)
    (hgap : w * (1 - q0) < d * (2 * q0 - 1)) :
    w - d * (2 * q0 - 1) < w * q0 := by
  linarith

theorem pair_acceptance_from_marginals {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E F : Ω → Prop) (q0 : ℝ)
    (hE : q0 ≤ μ.prob E) (hF : q0 ≤ μ.prob F) :
    2 * q0 - 1 ≤ μ.prob (fun ω => E ω ∧ F ω) := by
  have h := μ.prob_inter_lower E F
  linarith

end Finite
end FCAppendix
