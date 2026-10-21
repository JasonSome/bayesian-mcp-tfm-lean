import FCAppendix.Affine.Uniform06.EntryActiveMoments
import FCAppendix.Probability.EmpiricalConcentration
import FCAppendix.Probability.TiltedProduct

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryProfileConcentration
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.ExponentialTilt FCAppendix.Probability
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

theorem actual_tilted_empirical_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X f : Ω → ℝ) (hX : Measurable X) (hf : Measurable f)
    (hXb : ∀ᵐ x ∂μ, X x ∈ Icc (0:ℝ) 1)
    (hfb : ∀ᵐ x ∂μ, f x ∈ Icc (0:ℝ) 1)
    (u : ℝ) (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    ((Measure.pi fun _ : Fin N => μ).tilted (fun r => u*iidSum X N r)).real
      {r | ε ≤ |(∑ j, f (r j))/(N:ℝ)-∫ x, f x ∂μ.tilted (fun x => u*X x)|} ≤
      2*Real.exp (-2*(N:ℝ)*ε^2) := by
  letI : IsProbabilityMeasure (μ.tilted (fun x => u*X x)) :=
    isProbabilityMeasure_tilted (integrable_exp_mul_of_bounded μ hX.aemeasurable hXb u)
  have hb : ∀ᵐ x ∂μ.tilted (fun x => u*X x), f x ∈ Icc (0:ℝ) 1 :=
    (tilted_absolutelyContinuous μ (fun x => u*X x)).ae_le hfb
  rw [← pi_tilted_eq_tilted_iidSum μ X u N]
  exact iid_empiricalMean_two_sided_le _ hf.aemeasurable hb N hN hε

theorem eventual_actual_profile_tail
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (X f : (m : ℕ) → Ω m → ℝ) (u : ℕ → ℝ) (N : ℕ → ℕ)
    (hX : ∀ m, Measurable (X m)) (hf : ∀ m, Measurable (f m))
    (hXb : ∀ m, ∀ᵐ x ∂μ m, X m x ∈ Icc (0:ℝ) 1)
    (hfb : ∀ m, ∀ᵐ x ∂μ m, f m x ∈ Icc (0:ℝ) 1)
    (hN : Tendsto N atTop atTop) {L : ℝ}
    (hmean : Tendsto (fun m => ∫ x, f m x ∂(μ m).tilted (fun x => u m*X m x)) atTop (𝓝 L))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop,
      ((Measure.pi fun _ : Fin (N m) => μ m).tilted (fun r => u m*iidSum (X m) (N m) r)).real
        {r | ε ≤ |(∑ j, f m (r j))/(N m : ℝ)-L|} ≤
        2*Real.exp (-(ε^2/2)*(N m : ℝ)) := by
  have hcl := (hmean.sub_const L).abs
  simp only [sub_self,abs_zero] at hcl
  filter_upwards [hN.eventually_gt_atTop 0,
    hcl.eventually_le_const (show (0:ℝ) < ε/2 by positivity)] with m hNm hm
  have hsub : {r : Fin (N m) → Ω m | ε ≤ |(∑ j, f m (r j))/(N m : ℝ)-L|} ⊆
      {r | ε/2 ≤ |(∑ j, f m (r j))/(N m : ℝ)-
        ∫ x, f m x ∂(μ m).tilted (fun x => u m*X m x)|} := by
    intro r hr
    have hbad : ε ≤ |(∑ j, f m (r j))/(N m:ℝ)-L| := hr
    have hh := abs_sub_le ((∑ j, f m (r j))/(N m : ℝ))
      (∫ x, f m x ∂(μ m).tilted (fun x => u m*X m x)) L
    change ε/2 ≤ _
    linarith
  have ht := (measureReal_mono hsub).trans
    (actual_tilted_empirical_tail (μ m) (X m) (f m) (hX m) (hf m) (hXb m) (hfb m)
      (u m) (N m) hNm (by positivity : 0 ≤ ε/2))
  convert! ht using 1
  congr 2
  ring

end FCAppendix.Affine.Uniform06.EntryProfileConcentration
