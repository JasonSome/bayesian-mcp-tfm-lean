import FCAppendix.Affine.Tail04.ConditionalVersions
import FCAppendix.Existence.R01Distributional
import FCAppendix.Affine.LowBody.ICFromContinuousTests

noncomputable section
namespace FCAppendix.Affine.Tail04.FixedMarketLimitIC
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional

section Compact
variable {V A : Type*}
  [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  [MetricSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
  [SecondCountableTopology A]
  (μ : Measure V) [IsProbabilityMeasure μ]
  (π : ℕ→ Law (A:=A) μ) (π₀ : Law (A:=A) μ)
  (u : ℕ→ V×A→ℝ) (u₀ : C(V×A,ℝ))

def gainTest (j : ℕ) (b : A) (a : C(V×A,ℝ)) : ℝ :=
  ∫ x,a x*(u j (x.1,b)-u j x) ∂((π j).1 : Measure (V×A))

def limitGainTest (b : A) (a : C(V×A,ℝ)) : ℝ :=
  ∫ x,a x*(u₀ (x.1,b)-u₀ x) ∂(π₀.1 : Measure (V×A))

omit [BorelSpace V] [CompactSpace V] [BorelSpace A] [CompactSpace A]
  [SecondCountableTopology A] [IsProbabilityMeasure μ] in
theorem noisy_gainTest_nonpos
    (hopt : ∀ j,AllActionOptimal (π j) (u j))
    (j : ℕ) (b : A) (a : C(V×A,ℝ)) (ha : ∀ x,0≤ a x) :
    gainTest μ π u j b a≤0 := by
  apply integral_nonpos_of_ae
  filter_upwards [hopt j] with x hx
  exact mul_nonpos_of_nonneg_of_nonpos (ha x) (sub_nonpos.mpr (hx b))

omit [BorelSpace V] [CompactSpace V] [BorelSpace A] [CompactSpace A]
  [SecondCountableTopology A] [IsProbabilityMeasure μ] in

theorem limit_gainTest_nonpos
    (hopt : ∀ j,AllActionOptimal (π j) (u j))
    (hpass : ∀ (b : A) (a : C(V×A,ℝ)),(∀ x,0≤ a x)→
      Tendsto (fun j=> gainTest μ π u j b a) atTop
        (𝓝 (limitGainTest μ π₀ u₀ b a)))
    (b : A) (a : C(V×A,ℝ)) (ha : ∀ x,0≤ a x) :
    limitGainTest μ π₀ u₀ b a≤0 :=
  le_of_tendsto (hpass b a ha)
    (Eventually.of_forall (fun j=> noisy_gainTest_nonpos μ π u hopt j b a ha))

omit [IsProbabilityMeasure μ] in

theorem fixed_action_of_tests
    (htest : ∀ (b : A) (a : C(V×A,ℝ)),(∀ x,0≤ a x)→
      limitGainTest μ π₀ u₀ b a≤0) (b : A) :
    ∀ᵐ x ∂(π₀.1 : Measure (V×A)),u₀ (x.1,b)≤ u₀ x := by
  let f : V×A→ℝ := fun x=> u₀ (x.1,b)-u₀ x
  have hf : Continuous f :=
    (u₀.continuous.comp (continuous_fst.prodMk continuous_const)).sub u₀.continuous
  have hbound (x : V×A) : |f x|≤2*‖u₀‖ := by
    have h₁ : |u₀ (x.1,b)|≤‖u₀‖ := by
      simpa only [Real.norm_eq_abs] using u₀.norm_coe_le_norm (x.1,b)
    have h₂ : |u₀ x|≤‖u₀‖ := by
      simpa only [Real.norm_eq_abs] using u₀.norm_coe_le_norm x
    exact (abs_sub _ _).trans (by linarith)
  have h := LowBody.ae_nonpos_outside_closed_of_tests
    (π₀.1 : Measure (V×A)) f hf.measurable ∅ isClosed_empty
    (fun x _=> hf.continuousAt) (by positivity : 0≤2*‖u₀‖) hbound
    (fun a ha _=> htest b a ha)
  filter_upwards [h] with x hx
  exact sub_nonpos.mp (hx (by simp))

omit [IsProbabilityMeasure μ] in

theorem all_actions_from_actual_tests
    (hopt : ∀ j,AllActionOptimal (π j) (u j))
    (hpass : ∀ (b : A) (a : C(V×A,ℝ)),(∀ x,0≤ a x)→
      Tendsto (fun j=> gainTest μ π u j b a) atTop
        (𝓝 (limitGainTest μ π₀ u₀ b a))) :
    AllActionOptimal π₀ u₀ := by
  exact ConditionalVersions.common_all_actions (π₀.1 : Measure (V×A))
    (fun x b=> u₀ (x.1,b)) u₀
    (fun x=> u₀.continuous.comp (continuous_const.prodMk continuous_id))
    (fixed_action_of_tests μ π₀ u₀
      (limit_gainTest_nonpos μ π π₀ u u₀ hopt hpass))

end Compact

section Conditional
variable {V A : Type*} [MeasurableSpace V] [MeasurableSpace A]
  (μ : Measure V) [SFinite μ] (σ : Kernel V A) [IsSFiniteKernel σ]
  (π : Measure (V×A)) (hjoint : μ⊗ₘσ=π)
  (u : V×A→ℝ)

include hjoint in
theorem conditional_all_actions
    (hS : MeasurableSet {x : V×A | ∀ b,u (x.1,b)≤ u x})
    (hopt : ∀ᵐ x ∂π,∀ b,u (x.1,b)≤ u x) :
    ∀ᵐ v ∂μ,∀ᵐ a ∂σ v,∀ b,u (v,b)≤ u (v,a) := by
  rw [←hjoint] at hopt
  exact (Measure.ae_compProd_iff hS).mp hopt

end Conditional
end FCAppendix.Affine.Tail04.FixedMarketLimitIC
