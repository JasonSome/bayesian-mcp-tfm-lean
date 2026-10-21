import FCAppendix.Affine.Uniform06.WeightedIntervalLLT
import FCAppendix.Affine.Uniform06.DeficitOrientation
import FCAppendix.Probability.TiltedProduct

noncomputable section
namespace FCAppendix.Affine.Uniform06.ExactUntilting

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
open FCAppendix.ExponentialTilt
open MixedProductCharacteristic MixedCellSmoothing WeightedIntervalLLT

variable {Ω : Type*} [MeasurableSpace Ω]

def cost (μ : Measure Ω) (X : Ω → ℝ) (θ cap : ℝ) (N : ℕ) : ℝ :=
  -θ*cap-(N : ℝ)*cgf X μ (-θ)

theorem integral_reverse_tilt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (u : ℝ)
    (ht : Integrable (fun ω => Real.exp (u*X ω)) μ) (F : Ω → ℝ) :
    (∫ ω,F ω ∂μ) =
      ∫ ω,Real.exp (cgf X μ u-u*X ω)*F ω ∂μ.tilted (fun ω => u*X ω) := by
  rw [integral_tilted_mul_eq_cgf _ ht]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    rw [smul_eq_mul,← mul_assoc,← Real.exp_add]
    have he : u*X ω-cgf X μ u+(cgf X μ u-u*X ω)=0 := by ring
    rw [he,Real.exp_zero,one_mul]

theorem iid_reverse_tilt (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1)
    (θ cap : ℝ) (N : ℕ) (F : (Fin N → Ω) → ℝ) :
    (∫ ω,F ω ∂Measure.pi (fun _ : Fin N => μ)) =
      Real.exp (-cost μ X θ cap N) *
        ∫ ω,Real.exp (-θ*(cap-iidSum X N ω))*F ω
          ∂Measure.pi (fun _ : Fin N => μ.tilted (fun x => -θ*X x)) := by
  rw [pi_tilted_eq_tilted_iidSum]
  have hh := integral_reverse_tilt (Measure.pi (fun _ : Fin N => μ)) (iidSum X N) (-θ)
    (integrable_exp_mul_iidSum μ hX hXb (-θ) N) F
  rw [cgf_iidSum] at hh
  rw [hh,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    unfold cost
    ring

theorem fixed_prefix_reverse_tilt (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1)
    (θ cap markSum : ℝ) (N k : ℕ) (F : (Fin N → Ω) → ℝ) :
    (∫ ω,F ω ∂Measure.pi (fun _ : Fin N => μ)) =
      Real.exp (-cost μ X θ cap (N+k)) *
      Real.exp (-θ*markSum-(k : ℝ)*cgf X μ (-θ)) *
        ∫ ω,Real.exp (-θ*(cap-markSum-iidSum X N ω))*F ω
          ∂Measure.pi (fun _ : Fin N => μ.tilted (fun x => -θ*X x)) := by
  rw [iid_reverse_tilt μ hX hXb θ (cap-markSum) N F]
  have hp : Real.exp (-cost μ X θ (cap-markSum) N) =
      Real.exp (-cost μ X θ cap (N+k))*
        Real.exp (-θ*markSum-(k : ℝ)*cgf X μ (-θ)) := by
    rw [← Real.exp_add]
    congr 1
    unfold cost
    push_cast
    ring
  rw [hp]

lemma integral_productCell (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {Y : Ω → ℤ} (hX : Measurable X) (hY : Measurable Y)
    (N : ℕ) (c : ℝ) (j y : ℤ) {F : ℝ → ℝ} (hF : Measurable F) :
    (∫ w,F w ∂productCell μ X Y N c j y) =
      ∫ ω,F (c+continuousSum X N ω)*
        (if j+integerSum Y N ω=y then (1 : ℝ) else 0)
          ∂Measure.pi (fun _ : Fin N => μ) := by
  have hsum : Measurable (fun ω : Fin N → Ω => c+continuousSum X N ω) :=
    measurable_const.add (measurable_continuousSum hX N)
  have hcell : MeasurableSet {ω : Fin N → Ω | j+integerSum Y N ω=y} :=
    measurableSet_eq_fun (measurable_const.add (measurable_integerSum hY N)) measurable_const
  unfold productCell
  rw [integral_map hsum.aemeasurable hF.aestronglyMeasurable,← integral_indicator hcell]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    by_cases h : j+integerSum Y N ω=y <;> simp [h]

lemma measurable_exponentialTest (k : ℕ) (θ s : ℝ) :
    Measurable (exponentialTest k θ s) := by
  unfold exponentialTest
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    (((measurable_id.sub_const s).pow_const k).mul
      (show Measurable (fun w : ℝ => Real.exp (-(θ*w))) by fun_prop)) measurable_const

def originalMoment (μ : Measure Ω) (X : Ω → ℝ) (Y : Ω → ℤ)
    (N : ℕ) (cap : ℝ) (y : ℤ) (k : ℕ) : ℝ :=
  ∫ ω : Fin N → Ω,
    (if 0 ≤ cap-iidSum X N ω then (cap-iidSum X N ω)^k else 0)*
      (if integerSum Y N ω=y then (1 : ℝ) else 0) ∂Measure.pi (fun _ : Fin N => μ)

theorem original_moment_untilt (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {Y : Ω → ℤ} (hX : Measurable X) (hY : Measurable Y)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1)
    (θ cap : ℝ) (N : ℕ) (y : ℤ) (k : ℕ) :
    originalMoment μ X Y N cap y k = Real.exp (-cost μ X θ cap N)*
      ∫ w,exponentialTest k θ 0 w
        ∂productCell (μ.tilted (fun x => -θ*X x)) (fun x => -X x) Y N cap 0 y := by
  letI := isProbabilityMeasure_unitInterval_tilted μ hX hXb (-θ)
  unfold originalMoment
  rw [iid_reverse_tilt μ hX hXb θ cap N]
  rw [integral_productCell _ (show Measurable (fun x => -X x) from hX.neg) hY N cap 0 y (measurable_exponentialTest k θ 0)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    have hs : cap+continuousSum (fun x => -X x) N ω=cap-iidSum X N ω := by
      simp only [continuousSum,iidSum,Finset.sum_neg_distrib,sub_eq_add_neg]
    dsimp only
    rw [hs]
    simp only [zero_add,exponentialTest,sub_zero]
    by_cases hw : 0 ≤ cap-iidSum X N ω <;>
      by_cases hy : integerSum Y N ω=y <;> simp [hw,hy,mul_comm]

end FCAppendix.Affine.Uniform06.ExactUntilting
