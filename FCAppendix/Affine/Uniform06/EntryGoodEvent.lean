import FCAppendix.Affine.Uniform06.EntryUntilting
import FCAppendix.Probability.BoundedTiltVariance
import FCAppendix.Probability.ClippedSubGaussianMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryGoodEvent
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.ExponentialTilt

variable {Ω : Type*} [MeasurableSpace Ω]

theorem restricted_integral_error (μ : Measure Ω) [IsFiniteMeasure μ]
    (G : Set Ω) (hG : MeasurableSet G) (F : Ω → ℝ)
    (hF : Integrable F μ) (M : ℝ) (hM : ∀ᵐ ω ∂μ.restrict Gᶜ, |F ω| ≤ M) :
    |(∫ ω in G, F ω ∂μ)-(∫ ω, F ω ∂μ)| ≤ M*μ.real Gᶜ := by
  have hzero : (fun ω => G.indicator F ω-F ω) = -(Gᶜ.indicator F) := by
    funext ω
    by_cases hω : ω ∈ G <;> simp [hω]
  rw [← integral_indicator hG,← integral_sub (hF.indicator hG) hF,hzero]
  change |(∫ ω, -Gᶜ.indicator F ω ∂μ)| ≤ _
  rw [integral_neg,abs_neg,
    integral_indicator hG.compl]
  have hh := norm_integral_le_of_norm_le_const (μ := μ.restrict Gᶜ) (f := F)
    (by simpa only [Real.norm_eq_abs] using hM)
  simpa only [Real.norm_eq_abs,Measure.real,Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter,mul_comm] using hh

theorem actual_untilt_factor_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1)
    (N : ℕ) {θ c : ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c) :
    Real.exp (-θ*(N : ℝ)) ≤ Real.exp ((N : ℝ)*cgf X μ (-θ)+θ*c) := by
  have hcgf := (cgf_mem_Icc_of_unit_bounded μ hX hb
    (show |-θ| ≤ θ by rw [abs_neg,abs_of_nonneg hθ])).1
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hcgf (Nat.cast_nonneg N)
  nlinarith [mul_nonneg hθ hc]

theorem conditional_ratio_eq {g P A B : ℝ} (hg : g ≠ 0) :
    (A/g)^2/((P/g)*(B/g))=A^2/(P*B) := by
  by_cases hP : P=0
  · simp [hP]
  by_cases hB : B=0
  · simp [hB]
  field_simp [hg,hP,hB]

theorem polynomial_bad_error_over_untilt_tendsto_zero
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (θ Q e : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0))
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hQ : ∀ᶠ m in atTop, Real.exp (-θ m*(N m : ℝ)) ≤ Q m)
    (he0 : ∀ᶠ m in atTop, 0 ≤ e m)
    (he : ∀ᶠ m in atTop, e m ≤ C*Real.exp (-c*(N m : ℝ))) (j : ℕ) :
    Tendsto (fun m => (N m : ℝ)^j*e m/Q m) atTop (𝓝 0) := by
  have hNR : Tendsto (fun m => (N m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hbase : Tendsto (fun m => (N m : ℝ)^j*Real.exp (-(c/2)*(N m : ℝ)))
      atTop (𝓝 0) := by
    convert!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j : ℝ) (c/2) (by positivity)).comp hNR
      using 1; simp only [Function.comp_def, Real.rpow_natCast]
  have hlim : Tendsto (fun m => C*((N m : ℝ)^j*Real.exp (-(c/2)*(N m : ℝ))))
      atTop (𝓝 0) := by simpa using hbase.const_mul C
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hQ,he0] with m hQm hem
    exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hem)
      ((Real.exp_pos _).le.trans hQm)
  · filter_upwards [hQ,he,hθ.eventually (eventually_lt_nhds (show (0 : ℝ)< c/2 by positivity))]
      with m hQm hem hθm
    have hQpos : 0 < Q m := (Real.exp_pos _).trans_le hQm
    calc
      (N m : ℝ)^j*e m/Q m ≤
          (N m : ℝ)^j*(C*Real.exp (-c*(N m : ℝ)))/Q m :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hem (pow_nonneg (Nat.cast_nonneg _) _)) hQpos.le
      _ ≤ (N m : ℝ)^j*(C*Real.exp (-c*(N m : ℝ)))/
          Real.exp (-θ m*(N m : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hQm
      _ = C*(N m : ℝ)^j*Real.exp ((-c+θ m)*(N m : ℝ)) := by
        rw [show (N m : ℝ)^j*(C*Real.exp (-c*(N m : ℝ)))/
            Real.exp (-θ m*(N m : ℝ)) =
            (C*(N m : ℝ)^j)*(Real.exp (-c*(N m : ℝ))/Real.exp (-θ m*(N m : ℝ))) by ring,
          ← Real.exp_sub]
        congr 1; ring
      _ ≤ C*(N m : ℝ)^j*Real.exp (-(c/2)*(N m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (by linarith : -c+θ m ≤ -(c/2)) (Nat.cast_nonneg _)
      _ = C*((N m : ℝ)^j*Real.exp (-(c/2)*(N m : ℝ))) := by ring

theorem restricted_moment_relative_error_tendsto_zero
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : (m : ℕ) → Set (Ω m)) (hG : ∀ m, MeasurableSet (G m))
    (F : (m : ℕ) → Ω m → ℝ) (hF : ∀ m, Integrable (F m) (μ m))
    (θ Q : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0))
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hQ : ∀ᶠ m in atTop, Real.exp (-θ m*(N m : ℝ)) ≤ Q m)
    (hbad : ∀ᶠ m in atTop, (μ m).real (G m)ᶜ ≤ C*Real.exp (-c*(N m : ℝ)))
    (k j : ℕ)
    (hbound : ∀ m, ∀ᵐ ω ∂(μ m).restrict (G m)ᶜ, |F m ω| ≤ (N m : ℝ)^k) :
    Tendsto (fun m => (N m : ℝ)^j*
      |(∫ ω in G m, F m ω ∂μ m)-(∫ ω, F m ω ∂μ m)| /Q m) atTop (𝓝 0) := by
  have hrel := polynomial_bad_error_over_untilt_tendsto_zero N hN θ Q
    (fun m => (μ m).real (G m)ᶜ) hθ hc hC hQ
    (Eventually.of_forall fun _ => measureReal_nonneg) hbad (j+k)
  apply squeeze_zero' ?_ ?_ hrel
  · filter_upwards [hQ] with m hQm
    have hQpos : 0 < Q m := (Real.exp_pos _).trans_le hQm
    positivity
  · filter_upwards [hQ] with m hQm
    have hQpos := (Real.exp_pos _).trans_le hQm
    have hboundm := restricted_integral_error (μ m) (G m) (hG m) (F m) (hF m)
      ((N m : ℝ)^k) (hbound m)
    have he := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hboundm (pow_nonneg (Nat.cast_nonneg (N m)) j)) hQpos.le
    simpa only [pow_add,mul_assoc] using he

end FCAppendix.Affine.Uniform06.EntryGoodEvent
