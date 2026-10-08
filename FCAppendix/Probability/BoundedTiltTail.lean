import FCAppendix.Probability.BoundedTiltBerryEsseen
import FCAppendix.Probability.StandardizedReverseTilt
import FCAppendix.PayOnce.GaussianTiltCDFComparison

noncomputable section
namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Set
open PayOnce.GaussianTilt
universe w

theorem exists_bounded_iid_tilt_prefactor_error :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (u : ℝ) (N : ℕ),
        Measurable X → (∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) → u ≤ 0 →
        let r := ∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)
        let s := Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω)))
        let A := Real.exp ((N:ℝ)*(cgf X μ u-u*r))
        0 < s →
        |(Measure.pi (fun _ : Fin N => μ)).real {q | iidSum X N q ≤ (N:ℝ)*r}/A-
          prefactor (|u| * s)| ≤ 2*C/s ∧
        |(Measure.pi (fun _ : Fin N => μ)).real {q | iidSum X N q < (N:ℝ)*r}/A-
          prefactor (|u| * s)| ≤ 2*C/s := by
  obtain ⟨C,hC,hBE⟩ := exists_tilted_iid_uniform_bound.{w}
  refine ⟨C,hC,?_⟩
  intro Ω _ μ _ X u N hX hb hu
  dsimp only
  intro hs
  let r := ∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)
  let s := Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω)))
  let P := Measure.pi (fun _ : Fin N => μ)
  let ν := standardizedTiltedLaw P (iidSum X N) u ((N:ℝ)*r) s
  let A := Real.exp ((N:ℝ)*(cgf X μ u-u*r))
  have ht := integrable_exp_mul_iidSum μ hX hb u N
  haveI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_standardizedTiltedLaw P (measurable_iidSum hX N) ht
  have hCDF : ∀ x : ℝ, |cdf ν x-cdf (gaussianReal 0 1) x| ≤ C/s :=
    hBE μ X u N hX hb hs
  have hv : 0 ≤ |u| * s := mul_nonneg (abs_nonneg u) hs.le
  have hparam : -u*s = |u| * s := by rw [abs_of_nonpos hu]
  have hA : 0 < A := Real.exp_pos _
  have hnorm : cgf (iidSum X N) P u-u*((N:ℝ)*r) = (N:ℝ)*(cgf X μ u-u*r) := by
    rw [cgf_iidSum]
    ring
  have hclosed : P.real {q | iidSum X N q ≤ (N:ℝ)*r}/A =
      ∫ z, negativeHalfExp (|u| * s) z ∂ν := by
    have he := lower_tail_eq_standardized_tilted_prefactor P (measurable_iidSum hX N) ht hs
      (r := (N:ℝ)*r)
    rw [hnorm,hparam] at he
    change P.real {q | iidSum X N q ≤ (N:ℝ)*r} = A*∫ z, negativeHalfExp (|u| * s) z ∂ν at he
    rw [he,mul_div_cancel_left₀ _ hA.ne']
  have hstrict : P.real {q | iidSum X N q < (N:ℝ)*r}/A =
      ∫ z, strictNegativeHalfExp (|u| * s) z ∂ν := by
    have he := strict_lower_tail_eq_standardized_tilted_prefactor P (measurable_iidSum hX N) ht hs
      (r := (N:ℝ)*r)
    rw [hnorm,hparam] at he
    change P.real {q | iidSum X N q < (N:ℝ)*r} = A*∫ z, strictNegativeHalfExp (|u| * s) z ∂ν at he
    rw [he,mul_div_cancel_left₀ _ hA.ne']
  change |P.real {q | iidSum X N q ≤ (N:ℝ)*r}/A-prefactor (|u| * s)| ≤ _ ∧
    |P.real {q | iidSum X N q < (N:ℝ)*r}/A-prefactor (|u| * s)| ≤ _
  rw [hclosed,hstrict]
  constructor
  · simpa only [mul_div_assoc] using integral_negativeHalfExp_sub_prefactor_le ν hCDF hv
  · simpa only [mul_div_assoc] using integral_strictNegativeHalfExp_sub_prefactor_le ν hCDF hv

theorem tail_bounds_of_prefactor_error {P A η v : ℝ} (hA : 0 < A) (hv : 0 ≤ v)
    (herr : |P/A-prefactor v| ≤ 2*η)
    (hsmall : η*(1+v) ≤ lowerConstant/4) :
    A*lowerConstant/(2*(1+v)) ≤ P ∧ P ≤ A*(3*upperConstant)/(2*(1+v)) := by
  have hd : 0 < 1+v := by linarith
  have hg := prefactor_bounds hv
  have he := abs_le.mp herr
  have hsmall' : 2*η ≤ (lowerConstant/(1+v))/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hPQ : lowerConstant/(2*(1+v)) ≤ P/A ∧ P/A ≤ 3*upperConstant/(2*(1+v)) := by
    constructor
    · have hh : lowerConstant/(2*(1+v)) = (lowerConstant/(1+v))/2 := by
        field_simp
      rw [hh]
      linarith [he.1,hg.1]
    · have hc : lowerConstant/(1+v) ≤ upperConstant/(1+v) := hg.1.trans hg.2
      have hh : 3*upperConstant/(2*(1+v)) = 3*(upperConstant/(1+v))/2 := by
        field_simp
      rw [hh]
      linarith [he.2,hg.2]
  constructor
  · have hh := (le_div_iff₀ hA).mp hPQ.1
    simpa only [div_mul_eq_mul_div, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hh
  · have hh := (div_le_iff₀ hA).mp hPQ.2
    simpa only [div_mul_eq_mul_div, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hh

theorem exists_bounded_iid_tilt_tail_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (u : ℝ) (N : ℕ),
        Measurable X → (∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) → u ≤ 0 →
        let r := ∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)
        let s := Real.sqrt ((N:ℝ)*variance X (μ.tilted (fun ω => u*X ω)))
        let A := Real.exp ((N:ℝ)*(cgf X μ u-u*r))
        0 < s → (C/s)*(1 + |u| * s) ≤ lowerConstant/4 →
        (A*lowerConstant/(2*(1 + |u| * s)) ≤
          (Measure.pi (fun _ : Fin N => μ)).real {q | iidSum X N q ≤ (N:ℝ)*r} ∧
          (Measure.pi (fun _ : Fin N => μ)).real {q | iidSum X N q ≤ (N:ℝ)*r} ≤
            A*(3*upperConstant)/(2*(1 + |u| * s))) ∧
        (A*lowerConstant/(2*(1 + |u| * s)) ≤
          (Measure.pi (fun _ : Fin N => μ)).real {q | iidSum X N q < (N:ℝ)*r} ∧
          (Measure.pi (fun _ : Fin N => μ)).real {q | iidSum X N q < (N:ℝ)*r} ≤
            A*(3*upperConstant)/(2*(1 + |u| * s))) := by
  obtain ⟨C,hC,herror⟩ := exists_bounded_iid_tilt_prefactor_error.{w}
  refine ⟨C,hC,?_⟩
  intro Ω _ μ _ X u N hX hb hu
  dsimp only
  intro hs hsmall
  have he := herror μ X u N hX hb hu hs
  have hv := mul_nonneg (abs_nonneg u) hs.le
  constructor
  · exact tail_bounds_of_prefactor_error (Real.exp_pos _) hv (by simpa only [mul_div_assoc] using he.1) hsmall
  · exact tail_bounds_of_prefactor_error (Real.exp_pos _) hv (by simpa only [mul_div_assoc] using he.2) hsmall

end FCAppendix.ExponentialTilt
