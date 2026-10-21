import FCAppendix.Affine.LowBody.NoisyDeviations
import FCAppendix.Affine.LowBody.NoiseTestCloseness

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

variable {N : ℕ}

theorem noisy_weighted_deviation_nonpos (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (sigma : Kernel (LowValue d) unitInterval)
    [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure (LowValue d×unitInterval)))
    (hopt : ∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
      noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q'))≤
        noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q)))
    (dev : LowValue d×unitInterval→unitInterval) (hd : Measurable dev)
    (a : C(LowValue d×LowValue d,ℝ)) (ha : ∀x,0≤a x) :
    ∫x,a (basePhysicalPoint d ε hε hsmall x)*
      (noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(x.1,dev x))-
        noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,x))
        ∂(pi.1 : Measure (LowValue d×unitInterval))≤0 := by
  let u : LowValue d×unitInterval→ℝ:=fun x=>noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,x)
  have hu : Continuous u := (continuous_noisyExpectedUtility d hξ hξ1 hε hsmall c categories mu).comp
    (continuous_const.prodMk continuous_id)
  have hm : Measurable (fun x=>u (x.1,dev x)):=hu.measurable.comp (measurable_fst.prodMk hd)
  have hae : ∀ᵐx ∂(pi.1 : Measure (LowValue d×unitInterval)),u (x.1,dev x)≤u x := by
    rw [←hdis]
    apply Measure.ae_compProd_of_ae_ae (measurableSet_le hm hu.measurable)
    filter_upwards [hopt] with w hw
    filter_upwards [hw] with q hq
    exact hq (dev (w,q))
  exact integral_nonpos_of_ae (hae.mono (fun x hx=>mul_nonpos_of_nonneg_of_nonpos (ha _) (sub_nonpos.mpr hx)))

theorem noisy_test_error_tendsto_zero {Omega : Type*} [MeasurableSpace Omega] {d : ℝ}
    (a : C(LowValue d×LowValue d,ℝ))
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2)
    (heps0 : Tendsto eps atTop (𝓝 0))
    (M : ℕ→Measure Omega) [∀j,IsProbabilityMeasure (M j)]
    (sample : ℕ→Omega→((LowValue d×unitInterval)×unitInterval))
    (F : ℕ→Omega→ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀j x,|F j x|≤C) :
    Tendsto (fun j=>∫x,
      (a (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) (sample j x))-
        a (basePhysicalPoint d (eps j) (heps j) (hsmall j) (sample j x).1))*F j x ∂M j)
        atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  have hden : 0<C+1 := by linarith
  have hsmallEta : 0<eta/(2*(C+1)) := div_pos heta (by positivity)
  filter_upwards [eventually_noisy_test_close a eps heps hsmall heps0 hsmallEta] with j hj
  rw [Real.dist_eq,sub_zero,←Real.norm_eq_abs]
  have hh:=norm_integral_le_of_norm_le (integrable_const (μ:=M j) ((eta/(2*(C+1)))*C))
    (ae_of_all (M j) (fun x=>by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hj (sample j x)).le (hF j x) (abs_nonneg _) hsmallEta.le))
  have hh' : ‖∫x,
      (a (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) (sample j x))-
        a (basePhysicalPoint d (eps j) (heps j) (hsmall j) (sample j x).1))*F j x ∂M j‖≤
          (eta/(2*(C+1)))*C := by
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  apply hh'.trans_lt
  have heq : (eta/(2*(C+1)))*(2*(C+1))=eta := div_mul_cancel₀ eta (by positivity)
  nlinarith

end FCAppendix.Affine.LowBody
