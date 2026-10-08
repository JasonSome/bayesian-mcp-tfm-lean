import FCAppendix.PayOnce.DummyWeightedDerivative

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Filter Topology Set CommonList OwnImpact RareSuccessSlope
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

noncomputable def positiveSuccessDeriv (n c : ℕ) (hn : 2 ≤ n) (z : ℝ × (ι → ℝ)) : ℝ :=
  if 0 < z.1 then deriv (fun x => success n (allocation n c hn z.2 x)) z.1 else 0

theorem aestronglyMeasurable_positive_success_deriv_joint (G : Measure ℝ)
    [IsProbabilityMeasure G] (hatom : ∀ b : ℝ, 0 < b → G {b} = 0)
    {n c : ℕ} (hn : 2 ≤ n) :
    AEStronglyMeasurable (positiveSuccessDeriv n c hn : ℝ × (ι → ℝ) → ℝ)
      (G.prod (Measure.pi (fun _ : ι => G))) := by
  let F := fun z : ℝ × (ι → ℝ) => success n (allocation n c hn z.2 z.1)
  have hF : Measurable F := (continuous_success n).measurable.comp (measurable_allocation_joint hn)
  let δ : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun j => (hδ j).ne'⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun j z => if 0 < z.1 then (F (z.1+δ j,z.2)-F z)/δ j else 0)
  · intro j
    apply Measurable.aestronglyMeasurable
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      (((hF.comp ((measurable_fst.add_const (δ j)).prodMk measurable_snd)).sub hF).div_const (δ j))
      measurable_const
  · filter_upwards [ae_regularClearing_prod (ι := ι) (c := c) G hatom hn] with z hz
    by_cases hb : 0 < z.1
    · simp only [if_pos hb,positiveSuccessDeriv]
      have hp := differentiableAt_allocation_of_regular hn z.2 hb (hz hb)
      have hs : DifferentiableAt ℝ (fun x => F (x,z.2)) z.1 :=
        (differentiableAt_const (1:ℝ)).sub (((differentiableAt_const (1:ℝ)).sub hp).pow n)
      have hh := hs.hasDerivAt.tendsto_slope_zero.comp hδlim
      simpa only [Function.comp_def,F,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh
    · simp only [if_neg hb,positiveSuccessDeriv]
      exact tendsto_const_nhds

theorem exists_joint_measurable_weight (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {n c : ℕ} (hn : 2 ≤ n) :
    ∃ weight : ℝ × (ι → ℝ) → ℝ, Measurable weight ∧
      (∀ z, weight z ∈ Icc (0:ℝ) 1) ∧
      (∀ z, 1/((n:ℝ)^3+1) ≤ 1-weight z) ∧
      (∀ᵐ z ∂G.prod (Measure.pi (fun _ : ι => G)), 0 < z.1 →
        z.1*deriv (fun x => success n (allocation n c hn z.2 x)) z.1 =
          weightedSlope n (allocation n c hn z.2 z.1) (weight z)) ∧
      (∀ᵐ b ∂G, 0 < b → HasDerivAt (coverage n c hn (Measure.pi (fun _ : ι => G)))
        ((∫ r, weightedSlope n (allocation n c hn r b) (weight (b,r))
          ∂Measure.pi (fun _ : ι => G))/b) b) := by
  let p := fun z : ℝ × (ι → ℝ) => allocation n c hn z.2 z.1
  let d := positiveSuccessDeriv n c hn (ι := ι)
  have hd := aestronglyMeasurable_positive_success_deriv_joint (ι := ι) (c := c) G hatom hn
  let dm := hd.mk d
  let κ : ℝ := 1/((n:ℝ)^3+1)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκ1 : κ ≤ 1 := by
    dsimp only [κ]
    apply (div_le_one (by positivity : 0 < (n:ℝ)^3+1)).mpr
    linarith [pow_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) 3]
  let weight := fun z : ℝ × (ι → ℝ) => max 0 (min (1-κ) (1-z.1*dm z/phi n (p z)))
  have hw : Measurable weight :=
    measurable_const.max (measurable_const.min
      (measurable_const.sub ((measurable_fst.mul hd.measurable_mk).div
        ((measurable_phi n).comp (measurable_allocation_joint hn)))))
  have hw0 (z : ℝ × (ι → ℝ)) : 0 ≤ weight z := le_max_left _ _
  have hwcap (z : ℝ × (ι → ℝ)) : weight z ≤ 1-κ :=
    max_le (sub_nonneg.mpr hκ1) (min_le_left _ _)
  have hw1 (z : ℝ × (ι → ℝ)) : weight z ≤ 1 := (hwcap z).trans (by linarith)
  have he : ∀ᵐ z ∂G.prod (Measure.pi (fun _ : ι => G)), 0 < z.1 →
      z.1*deriv (fun x => success n (allocation n c hn z.2 x)) z.1 =
        weightedSlope n (p z) (weight z) := by
    filter_upwards [ae_regularClearing_prod (ι := ι) (c := c) G hatom hn,hd.ae_eq_mk] with z hz hdm hb
    obtain ⟨w,hwbound,hwgap,hderiv⟩ := AnalyticalKernel.exists_weight_success_derivative_of_regular
      hn (min_le_right c (Fintype.card (Active z.2)+1)) (fun j : Active z.2 => z.2 j.val) hb (hz hb)
    change z.1*deriv (fun x => success n (allocation n c hn z.2 x)) z.1 = weightedSlope n (p z) w at hderiv
    by_cases hi : 0 < p z ∧ p z < 1
    · have hφ := AnalyticalKernel.phi_pos_interior hn hi
      have hsolve : 1-z.1*dm z/phi n (p z) = w := by
        change d z = dm z at hdm
        rw [← hdm]
        simp only [d,positiveSuccessDeriv,if_pos hb]
        rw [hderiv,weightedSlope,if_pos hi]
        field_simp
        ring
      have hweight : weight z = w := by
        change max 0 (min (1-κ) (1-z.1*dm z/phi n (p z))) = w
        rw [hsolve,min_eq_right (by linarith [hwgap hi]),max_eq_right hwbound.1]
      rw [hweight]
      exact hderiv
    · simpa only [weightedSlope,if_neg hi] using hderiv
  refine ⟨weight,hw,fun z => ⟨hw0 z,hw1 z⟩,fun z => by linarith [hwcap z],he,?_⟩
  filter_upwards [ae_regularClearing (ι := ι) (c := c) G hatom hn,
    Measure.ae_ae_of_ae_prod he] with b hreg heq hb
  have hderiv := hasDerivAt_coverage_of_regular hn (Measure.pi (fun _ : ι => G)) hb (hreg hb)
  have hint : (∫ r, weightedSlope n (p (b,r)) (weight (b,r)) ∂Measure.pi (fun _ : ι => G)) =
      b * ∫ r, deriv (fun x => success n (allocation n c hn r x)) b ∂Measure.pi (fun _ : ι => G) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (heq.mono fun _ hh => (hh hb).symm)
  change HasDerivAt _ ((∫ r, weightedSlope n (p (b,r)) (weight (b,r))
    ∂Measure.pi (fun _ : ι => G))/b) b
  rw [hint,mul_div_cancel_left₀ _ hb.ne']
  exact hderiv.2

end FCAppendix.PayOnce.DummyKernel
