import FCAppendix.Affine.Uniform06.LiteralCenteredArray
import FCAppendix.Affine.Uniform06.EarlyMean

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.PhysicalExposureLimit

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.Uniform07
open MixedWeakLimits LiteralCenteredArray MixedIntervalLLT

theorem exposure_eq_clip {ξ z b : ℝ} (hξ : 0 < ξ) (_hz : 0 < z) (hb : 0 < b) :
    exposure ξ z b=FiniteGuards.clip01 ((b-z)/(ξ*b)) := by
  by_cases h : b ≤ z
  · rw [exposure_zero h,FiniteGuards.clip01_zero
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (mul_pos hξ hb).le)]
  · have hzb := lt_of_not_ge h
    have hratio : 0 ≤ (b-z)/(ξ*b) := div_nonneg (sub_nonneg.mpr hzb.le) (mul_pos hξ hb).le
    unfold exposure FiniteGuards.clip01
    rw [max_eq_left hzb.le,max_eq_right (sub_nonneg.mpr hzb.le),
      max_eq_right (le_min zero_le_one hratio)]

theorem exposure_price_lipschitz {ξ L T ell : ℝ}
    (hξ : 0 < ξ) (hell : 0 < ell) (hL : ell ≤ L) (hT : ell ≤ T) (b : ℝ) :
    |exposure ξ L b-exposure ξ T b| ≤ (1/(ξ*ell))*|L-T| := by
  by_cases hb : b ≤ ell
  · rw [exposure_zero (hb.trans hL),exposure_zero (hb.trans hT),sub_self,abs_zero]
    positivity
  · have heb := lt_of_not_ge hb
    have hb0 := hell.trans heb
    rw [exposure_eq_clip hξ (hell.trans_le hL) hb0,
      exposure_eq_clip hξ (hell.trans_le hT) hb0]
    have hh := FiniteGuards.clip01_lipschitz ((b-L)/(ξ*b)) ((b-T)/(ξ*b))
    have he : (b-L)/(ξ*b)-(b-T)/(ξ*b)=-(L-T)/(ξ*b) := by ring
    rw [he,abs_div,abs_neg,abs_of_pos (mul_pos hξ hb0)] at hh
    calc
      _ ≤ |L-T| /(ξ*b) := hh
      _ ≤ |L-T| /(ξ*ell) := div_le_div_of_nonneg_left (abs_nonneg _)
        (mul_pos hξ hell) (mul_le_mul_of_nonneg_left heb.le hξ.le)
      _ = _ := by ring

theorem exposure_uniform_price_limit {ξ : ℝ} (hξ : 0 < ξ)
    (b : ℕ → ℝ) {b0 : ℝ} (hb0 : 0 < b0) (hb : Tendsto b atTop (𝓝 b0)) :
    TendstoUniformly (fun n B => exposure ξ (b n) B) (exposure ξ b0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have herr : Tendsto (fun n => (1/(ξ*(b0/2)))*|b n-b0|) atTop (𝓝 0) := by
    simpa using ((hb.sub_const b0).abs).const_mul (1/(ξ*(b0/2)))
  filter_upwards [hb.eventually_const_le (by linarith : b0/2 < b0),
    herr.eventually_lt_const hε] with n hn he B
  have hh := exposure_price_lipschitz hξ (half_pos hb0) hn
    (by linarith : b0/2 ≤ b0) B
  simpa only [Real.dist_eq,abs_sub_comm] using hh.trans_lt he

def lowerProbability (i : Row) (G : ProbabilityMeasure (ℝ × ℝ))
    (b : ℝ) (hb : 0 < b) : ProbabilityMeasure ℝ :=
  ⟨MixedLaw.physicalLowerLaw i b (G:Measure (ℝ × ℝ)),
    MixedLaw.physicalLowerLaw_probability i hb (G:Measure (ℝ × ℝ))⟩

theorem lowerProbability_tendsto (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) {b0 : ℝ} (hb0 : 0 < b0)
    (hblim : Tendsto b atTop (𝓝 b0)) :
    Tendsto (fun n => lowerProbability i (G n) (b n) (hb n)) atTop
      (𝓝 (lowerProbability i G0 b0 hb0)) := by
  let F : ℕ → C(ℝ × ℝ,ℝ) := fun n =>
    ⟨fun p => exposure (xi i) (b n) p.2,
      (continuous_exposure (xi_pos i) (hb n)).comp continuous_snd⟩
  let f : C(ℝ × ℝ,ℝ) :=
    ⟨fun p => exposure (xi i) b0 p.2,
      (continuous_exposure (xi_pos i) hb0).comp continuous_snd⟩
  have hu : TendstoUniformly (fun n p => F n p) f atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp
      (exposure_uniform_price_limit (xi_pos i) b hb0 hblim) ε hε] with n hn p
    exact hn p.2
  exact FCAppendix.PayOnce.KernelLawConvergence.tendsto_map_varying hG F f hu
    (Eventually.of_forall fun n p => ⟨exposure_nonneg (xi_pos i) (hb n),exposure_le_one _ _ _⟩)
    (fun p => ⟨exposure_nonneg (xi_pos i) hb0,exposure_le_one _ _ _⟩)

theorem mixed_matching_tilts_tendsto (i : Row)
    (ν : ℕ → ProbabilityMeasure ℝ) (ν0 : ProbabilityMeasure ℝ)
    (hν : ∀ n, ∀ᵐ x ∂(ν n:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hν0 : ∀ᵐ x ∂(ν0:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hweak : Tendsto ν atTop (𝓝 ν0))
    {a b : ℝ} (hab : a < b) (hcomponent : volume.restrict (Ioo a b) ≪ (ν0:Measure ℝ))
    (θ r : ℕ → ℝ) {θ0 r0 : ℝ} (hr : Tendsto r atTop (𝓝 r0))
    (hmatch : ∀ᶠ n in atTop,
      SubentryTilt.mean (MixedLaw.law i (ν n:Measure ℝ)) Prod.fst (θ n)=r n)
    (hmatch0 : SubentryTilt.mean (MixedLaw.law i (ν0:Measure ℝ)) Prod.fst θ0=r0) :
    Tendsto θ atTop (𝓝 θ0) := by
  have hv : 0 < variance Prod.fst (MixedLaw.law i (ν0:Measure ℝ)) := by
    have hh := (source_variance_positive i ν0 hν0 hab hcomponent 0).1
    simpa only [MixedLaw.tiltedLaw,zero_mul,tilted_const] using hh
  have hstrict := TiltStability.strictAnti_mean (MixedLaw.law i (ν0:Measure ℝ))
    measurable_fst (MixedLaw.demand_bounds i _ hν0) hv
  have hanti (n : ℕ) := TiltStability.antitone_mean (MixedLaw.law i (ν n:Measure ℝ))
    measurable_fst (MixedLaw.demand_bounds i _ (hν n))
  have hfixed (v : ℝ) : Tendsto
      (fun n => SubentryTilt.mean (MixedLaw.law i (ν n:Measure ℝ)) Prod.fst v) atTop
      (𝓝 (SubentryTilt.mean (MixedLaw.law i (ν0:Measure ℝ)) Prod.fst v)) :=
    tilted_integral_tendsto i ν ν0 hν hν0 hweak (fun _ => -v) tendsto_const_nhds
      Prod.fst continuous_fst
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hl : r0 < SubentryTilt.mean (MixedLaw.law i (ν0:Measure ℝ)) Prod.fst (θ0-ε) := by
    rw [← hmatch0]
    exact hstrict (by linarith)
  have hu : SubentryTilt.mean (MixedLaw.law i (ν0:Measure ℝ)) Prod.fst (θ0+ε) < r0 := by
    rw [← hmatch0]
    exact hstrict (by linarith)
  filter_upwards [hmatch,Tendsto.eventually_lt hr (hfixed (θ0-ε)) hl,
    Tendsto.eventually_lt (hfixed (θ0+ε)) hr hu] with n hn hlo hhi
  have hleft : θ0-ε < θ n := by
    by_contra hh
    have hle := hanti n (le_of_not_gt hh)
    rw [hn] at hle
    linarith
  have hright : θ n < θ0+ε := by
    by_contra hh
    have hle := hanti n (le_of_not_gt hh)
    rw [hn] at hle
    linarith
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem source_array_from_early_joint_limit (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hvalue : (G0:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbelow : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)), p.2 ≤ p.1)
    (hactive : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)), p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1)
    (b θ : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    {z : ℝ} (hz : z ∈ Ico (1/2:ℝ) (x i))
    (hblim : Tendsto b atTop (𝓝 (z*cutoff i)))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hmatch : ∀ᶠ n in atTop,
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (b n)
        (G n:Measure (ℝ × ℝ)))) Prod.fst (θ n)=
          (capacity (m n):ℝ)/((m n-1:ℕ):ℝ)) :
    ∃ θ0 > (0:ℝ), Tendsto θ atTop (𝓝 θ0) ∧
      ∃ n0 : ℕ, ∃ A : CenteredArray (ℝ × ℝ),
        A.N=(fun n => m (n+n0)-1) ∧
        A.law=(fun n => MixedLaw.tiltedLaw i
          (MixedLaw.physicalLowerLaw i (b (n+n0)) (G (n+n0):Measure (ℝ × ℝ))) (-θ (n+n0))) ∧
        A.X=(fun n p => p.1-mean i (lowerProbability i (G (n+n0)) (b (n+n0)) (hb _)) (-θ (n+n0))) ∧
        A.Y=(fun _ => integerSign) ∧ A.CompactGap := by
  have hb0 : 0 < z*cutoff i := mul_pos (by linarith [hz.1]) (cutoff_pos i)
  let ν := fun n => lowerProbability i (G n) (b n) (hb n)
  let ν0 := lowerProbability i G0 (z*cutoff i) hb0
  have hν := fun n => MixedLaw.physicalLowerLaw_bounds i (hb n) (G n:Measure (ℝ × ℝ))
  have hν0 := MixedLaw.physicalLowerLaw_bounds i hb0 (G0:Measure (ℝ × ℝ))
  have hw : Tendsto ν atTop (𝓝 ν0) := lowerProbability_tendsto i G G0 hG b hb hb0 hblim
  have hc := ActiveGraphComponent.original_active_graph_continuous_component i
    (G0:Measure (ℝ × ℝ)) hvalue hactive z ⟨hz.1,hz.2.le⟩
  have hgap : rho < rho+(1-x i)*(entry i-z*cutoff i) := by
    have hx : 0 < 1-x i := by cases i <;> norm_num [x,xQ]
    have hbentry : 0 < entry i-z*cutoff i := by
      unfold entry
      nlinarith [cutoff_pos i,hz.2]
    linarith [mul_pos hx hbentry]
  obtain ⟨θ0,hθ0,hm0⟩ := EarlyMean.exists_matching_tilt_early_law i
    (G0:Measure (ℝ × ℝ)) hvalue hbelow hactive hz (by norm_num [rho] : 0 < rho) hgap
  have hθ : Tendsto θ atTop (𝓝 θ0) := mixed_matching_tilts_tendsto i ν ν0 hν hν0 hw
    hc.1 hc.2 θ (fun n => (capacity (m n):ℝ)/((m n-1:ℕ):ℝ))
    (PhysicalRates.rival_capacity_density_tendsto.comp hm) hmatch hm0
  have hN : Tendsto (fun n => m n-1) atTop atTop := PhysicalRates.rivals_tendsto.comp hm
  obtain ⟨n0,A,hAN,hAlaw,hAX,hAY,_hVX,_hVY,hAgap⟩ :=
    exists_actual_centered_array i ν ν0 hν hν0 hw (fun n => -θ n) hθ.neg
      (fun n => m n-1) hN hc.1 hc.2
  exact ⟨θ0,hθ0.1,hθ,n0,A,hAN,hAlaw,hAX,hAY,hAgap⟩

end FCAppendix.Affine.Uniform06.PhysicalExposureLimit
