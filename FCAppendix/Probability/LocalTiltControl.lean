import FCAppendix.Probability.MeanZeroTilt
import FCAppendix.PayOnce.GaussianTiltPrefactor

namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Set Real
open PayOnce.GaussianTilt

theorem prefactor_smallness_of_variance_floor {B a κ w u : ℝ} {N : ℕ}
    (hB : 0 < B) (hκ : 0 < κ) (hw : κ ≤ w) (hu : |u| ≤ a)
    (hBa : B*a ≤ lowerConstant/8)
    (hN : (8*B/lowerConstant)^2/κ ≤ (N:ℝ)) :
    0 < sqrt ((N:ℝ)*w) ∧
      (B/sqrt ((N:ℝ)*w))*(1+|u| *sqrt ((N:ℝ)*w)) ≤ lowerConstant/4 := by
  have hR : 0 < 8*B/lowerConstant := div_pos (by positivity) lowerConstant_pos
  have hNsq : (8*B/lowerConstant)^2 ≤ (N:ℝ)*w :=
    ((div_le_iff₀ hκ).mp hN).trans (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg N))
  have hroot := sqrt_le_sqrt hNsq
  rw [sqrt_sq hR.le] at hroot
  have hs : 0 < sqrt ((N:ℝ)*w) := hR.trans_le hroot
  refine ⟨hs,?_⟩
  have hfirst : B/sqrt ((N:ℝ)*w) ≤ lowerConstant/8 := by
    apply (div_le_iff₀ hs).mpr
    have hh := (div_le_iff₀ lowerConstant_pos).mp hroot
    nlinarith
  have hsecond : B*|u| ≤ lowerConstant/8 :=
    (mul_le_mul_of_nonneg_left hu hB.le).trans hBa
  have he : (B/sqrt ((N:ℝ)*w))*(1+|u| *sqrt ((N:ℝ)*w)) =
      B/sqrt ((N:ℝ)*w)+B*|u| := by field_simp
  rw [he]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ}

theorem exists_local_tilt_control (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) {a v B r : ℝ} {N : ℕ}
    (ha : 0 < a) (hv : 0 < v) (hB : 0 < B) (hvar : v ≤ variance X μ)
    (hr : 0 < (∫ ω, X ω ∂μ)-r)
    (hgap : (∫ ω, X ω ∂μ)-r < a*exp (-2*a)*v)
    (hBa : B*a ≤ lowerConstant/8)
    (hN : (8*B/lowerConstant)^2/(exp (-2*a)*v) ≤ (N:ℝ)) :
    ∃ u : ℝ, u ∈ Ioo (-a) 0 ∧
      (∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) = r ∧
      exp (-2*a)*((∫ ω, X ω ∂μ)-r) ≤ |u| ∧
      |u| ≤ (exp (2*a)/v)*((∫ ω, X ω ∂μ)-r) ∧
      exp (-2*a)*v ≤ variance X (μ.tilted (fun ω => u*X ω)) ∧
      variance X (μ.tilted (fun ω => u*X ω)) ≤ exp (2*a) ∧
      0 < sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))) ∧
      (B/sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))))*
        (1+|u| *sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω)))) ≤ lowerConstant/4 := by
  have hvarp := hv.trans_le hvar
  have hvar1 : variance X μ ≤ 1 := by
    have hh := variance_le_sq_of_bounded hb hX.aemeasurable
    norm_num at hh
    linarith
  obtain ⟨u,hu,hmean,hulo,huhi⟩ := exists_negative_tilt_of_mean_gap μ hX hb ha hvarp hr
    (hgap.trans_le (mul_le_mul_of_nonneg_left hvar (mul_pos ha (exp_pos _)).le))
  have hua : |u| ≤ a := by rw [abs_of_neg hu.2]; linarith [hu.1]
  have hvt := tilted_variance_bounds μ hX hb hua
  have hvlo : exp (-2*a)*v ≤ variance X (μ.tilted (fun ω => u*X ω)) :=
    (mul_le_mul_of_nonneg_left hvar (exp_pos _).le).trans hvt.1
  have hvhi : variance X (μ.tilted (fun ω => u*X ω)) ≤ exp (2*a) :=
    hvt.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hvar1 (exp_pos (2*a)).le)
  have hsmall := prefactor_smallness_of_variance_floor hB (mul_pos (exp_pos _) hv) hvlo hua hBa hN
  refine ⟨u,hu,hmean,?_,?_,hvlo,hvhi,hsmall⟩
  · have hh := div_le_div_of_nonneg_left hr.le (mul_pos (exp_pos (2*a)) hvarp)
      (show exp (2*a)*variance X μ ≤ exp (2*a) by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hvar1 (exp_pos (2*a)).le)
    apply le_trans _ (hh.trans hulo)
    rw [show -2*a = -(2*a) by ring,exp_neg,div_eq_mul_inv]
    exact le_of_eq (by ring)
  · have hh := div_le_div_of_nonneg_left hr.le (mul_pos (exp_pos (-2*a)) hv)
      (mul_le_mul_of_nonneg_left hvar (exp_pos (-2*a)).le)
    apply (huhi.trans hh).trans
    rw [show -2*a = -(2*a) by ring,exp_neg]
    exact le_of_eq (by field_simp)

universe w

theorem exists_uniform_local_tilt_control (B v : ℝ) (hB : 0 < B) (hv : 0 < v) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (r : ℝ) (N : ℕ),
        Measurable X → (∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) → v ≤ variance X μ →
        0 < (∫ ω, X ω ∂μ)-r → (∫ ω, X ω ∂μ)-r < δ → N₀ ≤ N →
        ∃ u : ℝ, u ∈ Ioo (-a) 0 ∧
          (∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) = r ∧
          exp (-2*a)*((∫ ω, X ω ∂μ)-r) ≤ |u| ∧
          |u| ≤ (exp (2*a)/v)*((∫ ω, X ω ∂μ)-r) ∧
          exp (-2*a)*v ≤ variance X (μ.tilted (fun ω => u*X ω)) ∧
          variance X (μ.tilted (fun ω => u*X ω)) ≤ exp (2*a) ∧
          0 < sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))) ∧
          (B/sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))))*
            (1+|u| *sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω)))) ≤ lowerConstant/4 := by
  let a := min 1 (lowerConstant/(8*B))
  have ha : 0 < a := lt_min (by norm_num) (div_pos lowerConstant_pos (by positivity))
  have hBa : B*a ≤ lowerConstant/8 := by
    have hh := (le_div_iff₀ (show 0 < 8*B by positivity)).mp (min_le_right 1 (lowerConstant/(8*B)))
    change a*(8*B) ≤ lowerConstant at hh
    nlinarith
  let δ := a*exp (-2*a)*v
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N₀,hN₀⟩ := exists_nat_ge ((8*B/lowerConstant)^2/(exp (-2*a)*v))
  refine ⟨a,δ,ha,hδ,N₀,?_⟩
  intro Ω _ μ _ X r N hX hb hvar hr hgap hN
  exact exists_local_tilt_control μ hX hb ha hv hB hvar hr hgap hBa
    (hN₀.trans (Nat.cast_le.mpr hN))

end FCAppendix.ExponentialTilt
