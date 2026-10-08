import FCAppendix.Probability.WeakMomentConvergence

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem memLp_gaussian_positivePart_pow (z α : ℝ) (j : ℕ) :
    MemLp (fun Z : ℝ => (α*max (z-Z) 0)^j) 2 (gaussianReal 0 1) := by
  have h : MemLp (fun Z : ℝ => α*max (z-Z) 0) ((2*j:ℕ):ENNReal) (gaussianReal 0 1) := by
    have hn := memLp_id_gaussianReal' (μ := 0) (v := 1) ((2*j:ℕ):ENNReal) (by exact ENNReal.natCast_ne_top (2*j))
    exact ((memLp_const z).sub hn).pos_part.const_mul α
  have he (a : ℝ) : |a|^(2*j)=(a^j)^2 := by
    rw [pow_mul,sq_abs,← pow_mul,Nat.mul_comm 2 j,pow_mul]
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [Real.norm_eq_abs,he] using h.integrable_norm_pow'

end FCAppendix.Probability
