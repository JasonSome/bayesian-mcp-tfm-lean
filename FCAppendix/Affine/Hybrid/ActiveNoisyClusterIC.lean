import FCAppendix.Affine.Hybrid.ActivePatternBounds
import FCAppendix.Affine.LowBody.NoisyDeviations

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set
open Existence.Distributional
variable {N : ℕ}

lemma integrable_active_noisy_deviation {d vlo vhi L U eps xi : ℝ}
    (hL : 0<L) (heps : 0<eps) (hxi : 0<xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (lowLaw : ProbabilityMeasure (LowBody.LowValue d))
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu)
    (dev : ActiveValue vlo vhi×ActiveBaseBid L U→ActiveBaseBid L U) (hd : Measurable dev) :
    Integrable (fun t=>activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu
      (pi,(t.1,dev t))) (pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)) := by
  let u : C(ActiveValue vlo vhi×ActiveBaseBid L U,ℝ):=
    ⟨fun t=>activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu (pi,t),
      (continuous_activeNoisyExpectedUtility hL heps hxi hxi1 z c categories lowLaw mu).comp
        (continuous_const.prodMk continuous_id)⟩
  apply Integrable.of_bound (u.continuous.measurable.comp (measurable_fst.prodMk hd)).aestronglyMeasurable ‖u‖
  exact ae_of_all _ (fun t=>u.norm_coe_le_norm (t.1,dev t))

theorem active_noisy_integrated_deviation_nonpos {d vlo vhi L U eps xi : ℝ}
    (hL : 0<L) (heps : 0<eps) (hxi : 0<xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (lowLaw : ProbabilityMeasure (LowBody.LowValue d))
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu)
    (sigma : Kernel (ActiveValue vlo vhi) (ActiveBaseBid L U)) [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)))
    (hopt : ∀ᵐv ∂mu,∀ᵐB ∂sigma v,∀B' : ActiveBaseBid L U,
      activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu (pi,(v,B'))≤
        activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu (pi,(v,B)))
    (dev : ActiveValue vlo vhi×ActiveBaseBid L U→ActiveBaseBid L U) (hd : Measurable dev)
    (E : Set (ActiveValue vlo vhi×ActiveBaseBid L U)) :
    ∫t in E,(activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu (pi,(t.1,dev t))-
      activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu (pi,t))
        ∂(pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U))≤0 := by
  let u : ActiveValue vlo vhi×ActiveBaseBid L U→ℝ:=fun t=>
    activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu (pi,t)
  have hu : Continuous u:=(continuous_activeNoisyExpectedUtility hL heps hxi hxi1 z c categories lowLaw mu).comp
    (continuous_const.prodMk continuous_id)
  have hm : Measurable (fun t=>u (t.1,dev t)):=hu.measurable.comp (measurable_fst.prodMk hd)
  have hae : ∀ᵐt ∂(pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)),u (t.1,dev t)≤u t := by
    rw [←hdis]
    apply Measure.ae_compProd_of_ae_ae (measurableSet_le hm hu.measurable)
    filter_upwards [hopt] with v hv
    filter_upwards [hv] with B hB
    exact hB (dev (v,B))
  exact integral_nonpos_of_ae ((ae_restrict_of_ae hae).mono (fun _ hh=>sub_nonpos.mpr hh))

end FCAppendix.Affine.Hybrid
