import FCAppendix.Probability.BoundedVectorApproximation

noncomputable section

namespace FCAppendix.CorrelationMatrix

open Matrix ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

def corr (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, r; r, 1]

lemma corr_hermitian (r : ℝ) : (corr r).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corr]

lemma corr_quadratic (r : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    x ⬝ᵥ corr r *ᵥ x = x 0 ^ 2 + x 1 ^ 2 + 2 * r * x 0 * x 1 := by
  simp [dotProduct, mulVec, Fin.sum_univ_two, corr]
  ring

lemma corr_lower (r : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    (1 - |r|) * ‖x‖ ^ 2 ≤ x ⬝ᵥ corr r *ᵥ x := by
  rw [corr_quadratic, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  have hab : 2 * |x 0 * x 1| ≤ x 0 ^ 2 + x 1 ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x 0| - |x 1|), sq_abs (x 0), sq_abs (x 1)]
  have hcross := neg_abs_le (r * (x 0 * x 1))
  rw [abs_mul] at hcross
  nlinarith [mul_le_mul_of_nonneg_left hab (abs_nonneg r)]

lemma corr_posDef {r : ℝ} (hr : |r| < 1) : (corr r).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (corr_hermitian r)
  intro x hx
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 x
  have hv : v ≠ 0 := by
    intro h
    apply hx
    exact (WithLp.toLp_injective 2) h
  have hpos := mul_pos (sub_pos.mpr hr) (sq_pos_of_pos (norm_pos_iff.mpr hv))
  exact hpos.trans_le (corr_lower r v)

theorem whitening_norm_le {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (η : ℝ) (hη : 0 < η)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d), η * ‖x‖ ^ 2 ≤ x ⬝ᵥ S *ᵥ x) :
    ‖bentkusWhiteningCLM S‖ ≤ 1 / Real.sqrt η := by
  let B := bentkusWhiteningCLM S
  have hroot : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hq : (B x) ⬝ᵥ S *ᵥ (B x) = ‖x‖ ^ 2 := by
    rw [← inner_toEuclideanCLM]
    calc
      inner ℝ (B x) (toEuclideanCLM (𝕜 := ℝ) S (B x)) =
          inner ℝ x (B.adjoint (toEuclideanCLM (𝕜 := ℝ) S (B x))) :=
        (B.adjoint_inner_right x (toEuclideanCLM (𝕜 := ℝ) S (B x))).symm
      _ = inner ℝ x (B (toEuclideanCLM (𝕜 := ℝ) S (B x))) := by
        rw [show B.adjoint = B from adjoint_bentkusWhiteningCLM S]
      _ = inner ℝ x x := by rw [bentkusWhiteningCLM_covariance_comp d S hS x]
      _ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have h := hlower (B x)
  rw [hq] at h
  have he := Real.sq_sqrt hη.le
  have hb : ‖B x‖ * Real.sqrt η ≤ ‖x‖ := by
    apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hroot.le) (norm_nonneg _)).mp
    nlinarith
  have hd := (le_div_iff₀ hroot).mpr hb
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hd

theorem corr_whitening_norm_le {r : ℝ} (hr : |r| < 1) :
    ‖bentkusWhiteningCLM (corr r)‖ ≤ 1 / Real.sqrt (1 - |r|) :=
  whitening_norm_le (corr r) (corr_posDef hr) (1 - |r|) (sub_pos.mpr hr) (corr_lower r)

theorem eventually_corr_whitening_bounded {r : ℕ → ℝ} {r₀ : ℝ}
    (hr : Tendsto r atTop (𝓝 r₀)) (hr₀ : |r₀| < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, (corr (r n)).PosDef ∧
      ‖bentkusWhiteningCLM (corr (r n))‖ ≤ K := by
  let η := (1 - |r₀|) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  refine ⟨1 / Real.sqrt η, by positivity, ?_⟩
  have hh := (hr.abs).eventually (eventually_lt_nhds
    (by dsimp [η]; linarith : |r₀| < 1 - η))
  filter_upwards [hh] with n hn
  have hn' : |r n| < 1 := by linarith
  refine ⟨corr_posDef hn', ?_⟩
  apply whitening_norm_le (corr (r n)) (corr_posDef hn') η hη
  intro x
  exact le_trans (mul_le_mul_of_nonneg_right (by linarith : η ≤ 1 - |r n|)
    (sq_nonneg ‖x‖)) (corr_lower (r n) x)

end FCAppendix.CorrelationMatrix
