import FCAppendix.Affine.Uniform06.ExactUntilting

noncomputable section
namespace FCAppendix.Affine.Uniform06.OriginalDeficitMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MixedIntervalLLT MixedProductCharacteristic MixedCellSmoothing
open DeficitOrientation ExactUntilting WeightedIntervalLLT

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_reflected_deficit_cell (A : CenteredArray Ω)
    (U : ℕ → Ω → ℝ) (hU : ∀ n, Measurable (U n)) (r cap : ℕ → ℝ)
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω=U n ω-r n)
    (n : ℕ) (j y : ℤ) {F : ℝ → ℝ} (hF : Measurable F) :
    (∫ w,F w ∂productCell (A.law n) (fun ω => -U n ω) (A.Y n) (A.N n) (cap n) j y) =
      ∫ w,F w ∂productCell (A.law n) ((reflectX A).X n) (A.Y n) (A.N n)
        (cap n-(A.N n : ℝ)*r n) j y := by
  rw [integral_productCell _ (show Measurable (fun ω => -U n ω) from (hU n).neg) (A.measurable_Y n) _ _ _ _ hF,
    integral_productCell _ (show Measurable ((reflectX A).X n) from (A.measurable_X n).neg) (A.measurable_Y n) _ _ _ _ hF]
  apply integral_congr_ae
  filter_upwards [reflected_sum_eq_deficit A U r cap (fun _ => 0) hcenter n] with ω hω
  have hs : cap n+continuousSum (fun x => -U n x) (A.N n) ω =
      cap n-continuousSum (U n) (A.N n) ω := by
    simp only [continuousSum,Finset.sum_neg_distrib,sub_eq_add_neg]
  simp only [sub_zero] at hω
  rw [hs,hω]

theorem original_moment_scaled_eq (A : CenteredArray Ω)
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (U : ℕ → Ω → ℝ) (hU : ∀ n, Measurable (U n))
    (hbU : ∀ n, ∀ᵐ ω ∂μ n, U n ω ∈ Icc (0 : ℝ) 1)
    (r cap θn : ℕ → ℝ)
    (hlaw : ∀ n, A.law n=(μ n).tilted (fun ω => -θn n*U n ω))
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω=U n ω-r n)
    (n : ℕ) (y : ℤ) (k : ℕ) :
    (A.N n : ℝ)*Real.exp (cost (μ n) (U n) (θn n) (cap n) (A.N n))*
      originalMoment (μ n) (U n) (A.Y n) (A.N n) (cap n) y k =
        (A.N n : ℝ)*∫ w,exponentialTest k (θn n) 0 w
          ∂productCell (A.law n) ((reflectX A).X n) (A.Y n) (A.N n)
            (cap n-(A.N n : ℝ)*r n) 0 y := by
  letI := hμ n
  rw [original_moment_untilt (μ n) (hU n) (A.measurable_Y n) (hbU n)]
  rw [← hlaw n,integral_reflected_deficit_cell A U hU r cap hcenter n 0 y
    (measurable_exponentialTest k (θn n) 0)]
  have he : Real.exp (cost (μ n) (U n) (θn n) (cap n) (A.N n))*
      Real.exp (-cost (μ n) (U n) (θn n) (cap n) (A.N n))=1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  calc
    _ = (A.N n : ℝ)*
        (Real.exp (cost (μ n) (U n) (θn n) (cap n) (A.N n))*
          Real.exp (-cost (μ n) (U n) (θn n) (cap n) (A.N n)))*
        (∫ w,exponentialTest k (θn n) 0 w
          ∂productCell (A.law n) ((reflectX A).X n) (A.Y n) (A.N n)
            (cap n-(A.N n : ℝ)*r n) 0 y) := by ring
    _ = _ := by rw [he,mul_one]

theorem original_zeroth_first_second_moments (A : CenteredArray Ω) (hgap : A.CompactGap)
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (U : ℕ → Ω → ℝ) (hU : ∀ n, Measurable (U n))
    (hbU : ∀ n, ∀ᵐ ω ∂μ n, U n ω ∈ Icc (0 : ℝ) 1)
    (r cap θn : ℕ → ℝ) (y : ℕ → ℤ)
    (hlaw : ∀ n, A.law n=(μ n).tilted (fun ω => -θn n*U n ω))
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω=U n ω-r n)
    (hshift : Tendsto (fun n => A.d n*(cap n-(A.N n : ℝ)*r n)) atTop (𝓝 0))
    (hy : Tendsto (fun n => A.d n*((0-y n : ℤ) : ℝ)) atTop (𝓝 0))
    {θ lo hi : ℝ} (hlo : 0 < lo) (hbracket : ∀ n, lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ) :
    Tendsto (fun n => (A.N n : ℝ)*Real.exp (cost (μ n) (U n) (θn n) (cap n) (A.N n))*
      originalMoment (μ n) (U n) (A.Y n) (A.N n) (cap n) (y n) 0)
        atTop (𝓝 (density A.vX A.vY/θ)) ∧
    Tendsto (fun n => (A.N n : ℝ)*Real.exp (cost (μ n) (U n) (θn n) (cap n) (A.N n))*
      originalMoment (μ n) (U n) (A.Y n) (A.N n) (cap n) (y n) 1)
        atTop (𝓝 (density A.vX A.vY/θ^2)) ∧
    Tendsto (fun n => (A.N n : ℝ)*Real.exp (cost (μ n) (U n) (θn n) (cap n) (A.N n))*
      originalMoment (μ n) (U n) (A.Y n) (A.N n) (cap n) (y n) 2)
        atTop (𝓝 (density A.vX A.vY*(2/θ^3))) := by
  let R := reflectX A
  have hRgap : R.CompactGap := reflectX_compactGap A hgap
  let shift := fun n => cap n-(A.N n : ℝ)*r n
  have he (n k : ℕ) := original_moment_scaled_eq A μ hμ U hU hbU r cap θn hlaw hcenter n (y n) k
  have h₀ := tendsto_zeroth_moment_varying_tilt R hRgap shift (fun _ => 0) y
    hshift hy θn hlo hbracket hθn hθ
  have h₁ := tendsto_first_moment_varying_tilt R hRgap shift (fun _ => 0) y
    hshift hy θn hlo hbracket hθn hθ
  have h₂ := tendsto_second_moment_varying_tilt R hRgap shift (fun _ => 0) y
    hshift hy θn hlo hbracket hθn hθ
  refine ⟨?_,?_,?_⟩
  · simpa only [he,CenteredArray.cell,R,shift,reflectX] using h₀
  · simpa only [he,CenteredArray.cell,R,shift,reflectX] using h₁
  · simpa only [he,CenteredArray.cell,R,shift,reflectX] using h₂

end FCAppendix.Affine.Uniform06.OriginalDeficitMoments
