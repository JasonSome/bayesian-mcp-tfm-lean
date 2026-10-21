import FCAppendix.Probability.TiltedProduct

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryUntilting
open MeasureTheory ProbabilityTheory Real
open FCAppendix.ExponentialTilt

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exact_reverse_moment (μ : Measure Ω) (T F : Ω → ℝ) (θ c : ℝ)
    (ht : Integrable (fun ω => Real.exp (-θ*T ω)) μ) :
    (∫ ω, F ω ∂μ) = Real.exp (cgf T μ (-θ)+θ*c) *
      ∫ ω, Real.exp (-θ*(c-T ω))*F ω ∂μ.tilted (fun ω => -θ*T ω) := by
  rw [integral_tilted_mul_eq_cgf _ ht, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [smul_eq_mul]
  have he : Real.exp (cgf T μ (-θ)+θ*c) *
      (Real.exp (-θ*T ω-cgf T μ (-θ)) *
        (Real.exp (-θ*(c-T ω))*F ω)) = F ω := by
    rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
    have hex : cgf T μ (-θ)+θ*c +(-θ*T ω-cgf T μ (-θ)) +
        -θ*(c-T ω) = 0 := by ring
    rw [hex,Real.exp_zero,one_mul]
  exact he.symm

theorem exact_reverse_iid_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (N : ℕ) (F : (Fin N → Ω) → ℝ) (θ c : ℝ)
    (hX : Measurable X) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0:ℝ) 1) :
    (∫ ω, F ω ∂Measure.pi (fun _ : Fin N => μ)) =
      Real.exp ((N : ℝ)*cgf X μ (-θ)+θ*c) *
        ∫ ω, Real.exp (-θ*(c-iidSum X N ω))*F ω ∂
          Measure.pi (fun _ : Fin N => μ.tilted (fun a => -θ*X a)) := by
  rw [pi_tilted_eq_tilted_iidSum]
  simpa only [cgf_iidSum] using exact_reverse_moment
    (Measure.pi (fun _ : Fin N => μ)) (iidSum X N) F θ c
    (integrable_exp_mul_iidSum μ hX hb (-θ) N)

def deficitMoment (k : ℕ) (D : ℝ) : ℝ :=
  if k=0 then (if 0< D then 1 else 0) else (max D 0)^k

@[simp] theorem deficitMoment_zero (D : ℝ) :
    deficitMoment 0 D = if 0< D then 1 else 0 := by simp [deficitMoment]

@[simp] theorem deficitMoment_one (D : ℝ) : deficitMoment 1 D = max D 0 := by
  simp [deficitMoment]

@[simp] theorem deficitMoment_two (D : ℝ) : deficitMoment 2 D = (max D 0)^2 := by
  simp [deficitMoment]

lemma deficitMoment_nonneg (k : ℕ) (D : ℝ) : 0 ≤ deficitMoment k D := by
  unfold deficitMoment
  split_ifs <;> positivity

lemma deficitMoment_eq_zero_of_nonpos (k : ℕ) {D : ℝ} (hD : D ≤ 0) :
    deficitMoment k D=0 := by
  by_cases hk : k=0
  · simp [deficitMoment,hk,not_lt.mpr hD]
  · simp [deficitMoment,hk,max_eq_right hD,zero_pow hk]

theorem exact_reverse_good_deficit_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (N : ℕ) (D : (Fin N → Ω) → ℝ)
    (G : Set (Fin N → Ω)) (θ c : ℝ) (k : ℕ)
    (hX : Measurable X) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0:ℝ) 1) :
    (∫ ω, G.indicator (fun a => deficitMoment k (D a)) ω ∂Measure.pi (fun _ : Fin N => μ)) =
      Real.exp ((N : ℝ)*cgf X μ (-θ)+θ*c) *
        ∫ ω, Real.exp (-θ*(c-iidSum X N ω))*
          G.indicator (fun a => deficitMoment k (D a)) ω ∂
          Measure.pi (fun _ : Fin N => μ.tilted (fun a => -θ*X a)) :=
  exact_reverse_iid_moment μ X N (G.indicator (fun a => deficitMoment k (D a))) θ c hX hb

theorem cancel_common_moment_scales {a c P A B : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    (c*a*A)^2 / ((c*P)*(c*a^2*B)) = A^2/(P*B) := by
  by_cases hP : P = 0
  · simp [hP]
  by_cases hB : B = 0
  · simp [hB]
  field_simp [ha,hc,hP,hB]

theorem factorial_ratio_half {C θ : ℝ} (hC : C ≠ 0) (hθ : θ ≠ 0) :
    (C/θ^3)^2 / ((C/θ^2)*(2*C/θ^4)) = (1/2 : ℝ) := by
  field_simp [hC,hθ]

end FCAppendix.Affine.Uniform06.EntryUntilting
