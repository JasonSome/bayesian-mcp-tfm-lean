import FCAppendix.Affine.Uniform07.RateDefinitions

namespace FCAppendix.Affine.Uniform07
open Set

theorem normalizedAcceptance_eq_source (i : Row) {z y : ℝ}
    (hz : z ∈ Icc (1/2) (x i)) (hy : y ∈ Ioc 0 1) :
    normalizedAcceptance i z y = max 0 ((1-z/normalizedBid i y)/xi i) := by
  have hx : 0 < x i := by cases i <;> norm_num [x,xQ]
  have hxi := xi_pos i
  by_cases hyz : y ≤ z
  · have hyx : y ≤ x i := hyz.trans hz.2
    rw [normalizedAcceptance,if_pos hyz,normalizedBid,if_pos hyx]
    have he : 1-z/y ≤ 0 := by
      have h1 : 1 ≤ z/y := (le_div_iff₀ hy.1).2 (by simpa using hyz)
      linarith
    rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg he hxi.le)]
  · have hzy : z ≤ y := (lt_of_not_ge hyz).le
    rw [normalizedAcceptance,if_neg hyz]
    by_cases hyx : y ≤ x i
    · rw [if_pos hyx,normalizedBid,if_pos hyx]
      have hf : (1-z/y)/xi i = pieceP (1/xi i) (z/xi i) y := by
        dsimp [pieceP]
        field_simp
      rw [hf,max_eq_right (low_piece_bounds i hz.1 hzy hyx).1]
    · rw [if_neg hyx,normalizedBid,if_neg hyx]
      have hk : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
      have hden : 0 < kappa i*y+xi i*x i :=
        add_pos (mul_pos hk hy.1) (mul_pos hxi hx)
      have hf : (1-z/(x i*y/(kappa i*y+xi i*x i)))/xi i =
          pieceP ((1-z*kappa i/x i)/xi i) z y := by
        dsimp [pieceP]
        field_simp [hy.1.ne',hx.ne',hxi.ne',hden.ne']
        ring
      rw [hf,max_eq_right (high_piece_bounds i hz.1 hz.2 (le_of_not_ge hyx) hy.2).1]
end FCAppendix.Affine.Uniform07
