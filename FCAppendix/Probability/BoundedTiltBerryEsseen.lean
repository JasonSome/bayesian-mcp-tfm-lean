import FCAppendix.Probability.TiltedProduct
import FCAppendix.Probability.TriangularBoundedCLT

namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem memLp_tilted_centered_unitInterval (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1)
    (u : ℝ) (p : ENNReal) :
    MemLp (fun ω => X ω-∫ a, X a ∂μ.tilted (fun a => u*X a)) p
      (μ.tilted (fun ω => u*X ω)) := by
  let ν := μ.tilted (fun ω => u*X ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_unitInterval_tilted μ hX hb u
  have hB := unitInterval_tilted μ hb u
  have hm := Probability.unitInterval_mean_mem_Icc ν hX hB
  apply MemLp.of_bound (hX.sub_const _).aestronglyMeasurable 1
  filter_upwards [hB] with ω hω
  rw [Real.norm_eq_abs,abs_le]
  exact ⟨by linarith [hω.1,hm.2],by linarith [hω.2,hm.1]⟩

theorem tilted_centered_thirdMoment_le_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) (u : ℝ) :
    Integrable (fun ω => |X ω-∫ a, X a ∂μ.tilted (fun a => u*X a)|^3)
      (μ.tilted (fun ω => u*X ω)) ∧
    (∫ ω, |X ω-∫ a, X a ∂μ.tilted (fun a => u*X a)|^3 ∂μ.tilted (fun ω => u*X ω)) ≤
      variance X (μ.tilted (fun ω => u*X ω)) := by
  let ν := μ.tilted (fun ω => u*X ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_unitInterval_tilted μ hX hb u
  have hLp := memLp_tilted_centered_unitInterval μ hX hb u 3
  have hi : Integrable (fun ω => |X ω-∫ a, X a ∂ν|^3) ν := by
    simpa only [Real.norm_eq_abs] using hLp.integrable_norm_pow (by decide : (3:ℕ) ≠ 0)
  refine ⟨hi,?_⟩
  rw [variance_eq_integral hX.aemeasurable]
  apply integral_mono_ae hi ((hLp.mono_exponent (by norm_num : (2:ENNReal) ≤ 3)).integrable_sq)
  have hB := unitInterval_tilted μ hb u
  have hm := Probability.unitInterval_mean_mem_Icc ν hX hB
  filter_upwards [hB] with ω hω
  have hc : |X ω-∫ a, X a ∂ν| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hω.1,hm.2],by linarith [hω.2,hm.1]⟩
  calc
    _ = |X ω-∫ a, X a ∂ν| * (X ω-∫ a, X a ∂ν)^2 := by
      rw [pow_succ,sq_abs,mul_comm]
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem exists_tilted_iid_nonuniform_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (u : ℝ) (N : ℕ),
        Measurable X → (∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) →
        0 < Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))) → ∀ x : ℝ,
        |cdf (((Measure.pi (fun _ : Fin N => μ)).tilted (fun r => u*iidSum X N r)).map
          (fun r => (iidSum X N r-(N:ℝ)*(∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)))/
            Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))))) x -
          cdf (gaussianReal 0 1) x| ≤
          C/Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω)))/(1+|x|^3) := by
  obtain ⟨C,hC,hBE⟩ := Probability.exists_iid_unitInterval_nonuniform_bound.{u}
  refine ⟨C,hC,?_⟩
  intro Ω _ μ _ X u N hX hb hs x
  let ν := μ.tilted (fun ω => u*X ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_unitInterval_tilted μ hX hb u
  have hh := hBE ν X N hX (unitInterval_tilted μ hb u) hs x
  rw [← pi_tilted_eq_tilted_iidSum]
  have he : Probability.iidStandardizedSum ν X N = fun r =>
      (iidSum X N r-(N:ℝ)*(∫ ω, X ω ∂ν))/Real.sqrt ((N:ℝ)*variance X ν) := by
    funext r
    exact Probability.iidStandardizedSum_eq ν X N r
  rw [he] at hh
  exact hh

theorem exists_tilted_iid_uniform_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (u : ℝ) (N : ℕ),
        Measurable X → (∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) →
        0 < Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))) → ∀ x : ℝ,
        |cdf (((Measure.pi (fun _ : Fin N => μ)).tilted (fun r => u*iidSum X N r)).map
          (fun r => (iidSum X N r-(N:ℝ)*(∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)))/
            Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))))) x -
          cdf (gaussianReal 0 1) x| ≤
          C/Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))) := by
  obtain ⟨C,hC,hBE⟩ := exists_tilted_iid_nonuniform_bound.{u}
  refine ⟨C,hC,?_⟩
  intro Ω _ μ _ X u N hX hb hs x
  apply (hBE μ X u N hX hb hs x).trans
  exact div_le_self (div_nonneg hC.le hs.le) (le_add_of_nonneg_right (pow_nonneg (abs_nonneg x) _))

theorem exists_tilted_iid_uniform_bound_of_variance_lower :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (u : ℝ) (N : ℕ) (v : ℝ),
        Measurable X → (∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) → 0 < N → 0 < v →
        v ≤ variance X (μ.tilted (fun ω => u*X ω)) → ∀ x : ℝ,
        |cdf (((Measure.pi (fun _ : Fin N => μ)).tilted (fun r => u*iidSum X N r)).map
          (fun r => (iidSum X N r-(N:ℝ)*(∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)))/
            Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω))))) x -
          cdf (gaussianReal 0 1) x| ≤ (C/Real.sqrt v)/Real.sqrt N := by
  obtain ⟨C,hC,hBE⟩ := exists_tilted_iid_uniform_bound.{u}
  refine ⟨C,hC,?_⟩
  intro Ω _ μ _ X u N v hX hb hN hv hvar x
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hs := Real.sqrt_pos.mpr (mul_pos hNR (hv.trans_le hvar))
  apply (hBE μ X u N hX hb hs x).trans
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvar hNR.le)
  have hbnd := div_le_div_of_nonneg_left hC.le (Real.sqrt_pos.mpr (mul_pos hNR hv)) hroot
  calc
    _ ≤ C/Real.sqrt ((N:ℝ)*v) := hbnd
    _ = (C/Real.sqrt v)/Real.sqrt N := by rw [Real.sqrt_mul hNR.le]; ring

end FCAppendix.ExponentialTilt
