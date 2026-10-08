import FCAppendix.Probability.BoundedTiltTail
import FCAppendix.Probability.BoundedCGFComparison

namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Set
open PayOnce.GaussianTilt
universe w

theorem tail_ratio_of_exp_bounds {F₀ Fs E₀ Es v₀ vs Δ : ℝ}
    (hv₀ : 0 ≤ v₀) (hvs : 0 ≤ vs)
    (hlo : Real.exp E₀ * lowerConstant / (2 * (1+v₀)) ≤ F₀)
    (hup : Fs ≤ Real.exp Es * (3*upperConstant) / (2 * (1+vs)))
    (hgap : Es-E₀ ≤ -Δ) :
    0 < F₀ ∧ Fs/F₀ ≤ (3*upperConstant/lowerConstant) *
      ((1+v₀)/(1+vs)) * Real.exp (-Δ) := by
  have hd₀ : 0 < 1+v₀ := by linarith
  have hds : 0 < 1+vs := by linarith
  have hl : 0 < Real.exp E₀ * lowerConstant / (2 * (1+v₀)) :=
    div_pos (mul_pos (Real.exp_pos _) lowerConstant_pos) (by positivity)
  have hu : 0 < Real.exp Es * (3*upperConstant) / (2 * (1+vs)) :=
    div_pos (mul_pos (Real.exp_pos _) (mul_pos (by norm_num) upperConstant_pos)) (by positivity)
  have hF₀ := hl.trans_le hlo
  refine ⟨hF₀,?_⟩
  calc
    Fs/F₀ ≤ (Real.exp Es * (3*upperConstant) / (2 * (1+vs)))/F₀ :=
      div_le_div_of_nonneg_right hup hF₀.le
    _ ≤ (Real.exp Es * (3*upperConstant) / (2 * (1+vs))) /
        (Real.exp E₀ * lowerConstant / (2 * (1+v₀))) :=
      div_le_div_of_nonneg_left hu.le hl hlo
    _ = (3*upperConstant/lowerConstant) * ((1+v₀)/(1+vs)) * Real.exp (Es-E₀) := by
      rw [Real.exp_sub]
      field_simp
    _ ≤ (3*upperConstant/lowerConstant) * ((1+v₀)/(1+vs)) * Real.exp (-Δ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap)
        (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) upperConstant_pos.le)
          lowerConstant_pos.le) (div_nonneg hd₀.le hds.le))

theorem exists_bounded_iid_tilt_tail_ratio :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X Y : Ω → ℝ) (u w a r q : ℝ) (N : ℕ),
        Measurable X → Measurable Y →
        (∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) → (∀ᵐ ω ∂μ, Y ω ∈ Icc 0 1) →
        (∀ᵐ ω ∂μ, X ω ≤ Y ω) → u ≤ 0 → w ≤ 0 → |u| ≤ a →
        (∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) = r →
        (∫ ω, Y ω ∂μ.tilted (fun ω => w*Y ω)) = q →
        let sX := Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω)))
        let sY := Real.sqrt ((N:ℝ)*variance Y (μ.tilted (fun ω => w*Y ω)))
        0 < sX → 0 < sY →
        (C/sX)*(1+|u| *sX) ≤ lowerConstant/4 →
        (C/sY)*(1+|w| *sY) ≤ lowerConstant/4 →
        let F₀ := (Measure.pi (fun _ : Fin N => μ)).real {z | iidSum X N z < (N:ℝ)*r}
        let Fs := (Measure.pi (fun _ : Fin N => μ)).real {z | iidSum Y N z ≤ (N:ℝ)*q}
        0 < F₀ ∧ Fs/F₀ ≤ (3*upperConstant/lowerConstant) *
          ((1+|u| *sX)/(1+|w| *sY)) *
          Real.exp (-(N:ℝ)*(Real.exp (-a)*|u| *(∫ ω, Y ω-X ω ∂μ)+|u| *(r-q))) := by
  obtain ⟨C,hC,hbounds⟩ := exists_bounded_iid_tilt_tail_bounds.{w}
  refine ⟨C,hC,?_⟩
  intro Ω _ μ _ X Y u w a r q N hX hY hbX hbY hXY hu hw hua hmr hmq
  dsimp only
  intro hsX hsY hsmallX hsmallY
  have hXtail := (hbounds μ X u N hX hbX hu hsX hsmallX).2.1
  have hYtail := (hbounds μ Y w N hY hbY hw hsY hsmallY).1.2
  rw [hmr] at hXtail
  rw [hmq] at hYtail
  have hrate := tilted_rate_gap_lower_of_unitInterval_order μ hX hY hbX hbY hXY
    hu (abs_le.mp hua).1 hmq (r := r)
  have hgap : (N:ℝ)*(cgf Y μ w-w*q)-(N:ℝ)*(cgf X μ u-u*r) ≤
      -((N:ℝ)*(Real.exp (-a)*|u| *(∫ ω, Y ω-X ω ∂μ)+|u| *(r-q))) := by
    nlinarith [mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hh := tail_ratio_of_exp_bounds
    (mul_nonneg (abs_nonneg u) hsX.le) (mul_nonneg (abs_nonneg w) hsY.le)
    hXtail hYtail hgap
  simpa only [neg_mul] using hh

end FCAppendix.ExponentialTilt
