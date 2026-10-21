import FCAppendix.Affine.LowBody.NoisyDeviationTransport
import FCAppendix.Affine.LowBody.ExactICFromTests
import FCAppendix.Affine.LowBody.ExactAllBidIC
import FCAppendix.Affine.LowBody.LimitBidLaw

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
variable {N : ℕ}

private theorem latent_test_gain_nonpos (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2) (hquarter : ε≤1/4)
    (B : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (sigma : Kernel (LowValue d) unitInterval)
    [IsMarkovKernel sigma] (hdis : mu⊗ₘsigma=(pi.1 : Measure (LowValue d×unitInterval)))
    (hopt : ∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
      noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q'))≤
        noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q)))
    (a : C(LowValue d×LowValue d,ℝ)) (ha : ∀x,0≤a x) :
    latentDeviationTest N d ξ ε hε hquarter B c categories mu pi a-
      latentIncumbentTest N d ξ ε hε hsmall c categories mu pi a≤0 := by
  let u : C(LowValue d×unitInterval,ℝ):=⟨fun x=>
    noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,x),
    (continuous_noisyExpectedUtility d hξ hξ1 hε hsmall c categories mu).comp
      (continuous_const.prodMk continuous_id)⟩
  have hi := integrable_bounded_low_test (pi.1 : Measure (LowValue d×unitInterval)) a
    (basePhysicalPoint d ε hε hsmall) (measurable_basePhysicalPoint d ε hε hsmall)
    u u.continuous.measurable (fun x=>by simpa only [Real.norm_eq_abs] using u.norm_coe_le_norm x)
  have hd := integrable_bounded_low_test (pi.1 : Measure (LowValue d×unitInterval)) a
    (basePhysicalPoint d ε hε hsmall) (measurable_basePhysicalPoint d ε hε hsmall)
    (fun x=>ratioNoisyUtility N d ξ ε hε hquarter B c categories mu pi x.1)
    ((measurable_ratioNoisyUtility d hξ hξ1 hε hquarter B c categories mu pi).comp measurable_fst)
    (fun x=>abs_ratioNoisyUtility_le d hξ hξ1 hε hquarter B c categories mu pi x.1)
  have hae : ∀ᵐx ∂(pi.1 : Measure (LowValue d×unitInterval)),
      ratioNoisyUtility N d ξ ε hε hquarter B c categories mu pi x.1≤u x := by
    rw [←hdis]
    apply Measure.ae_compProd_of_ae_ae (measurableSet_le
      ((measurable_ratioNoisyUtility d hξ hξ1 hε hquarter B c categories mu pi).comp measurable_fst)
      u.continuous.measurable)
    filter_upwards [hopt] with w hw
    filter_upwards [hw] with q hq
    exact hq (choiceAtRatio ε hε hquarter (B/w.1))
  exact sub_nonpos.mpr (integral_mono_ae hd hi
    (hae.mono (fun x hx=>mul_le_mul_of_nonneg_left hx (ha _))))

theorem actual_noisy_limit_fixed_bid_tests {d ξ B : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hB : 0<B)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2) (hquarter : ∀j,eps j≤1/4)
    (heps0 : Tendsto eps atTop (𝓝 0)) (pi : ℕ→Law (A:=unitInterval) mu)
    (pi0 : Law (A:=LowValue d) mu)
    (hopt : ∀j,∃sigma : Kernel (LowValue d) unitInterval,
      IsMarkovKernel sigma ∧ mu⊗ₘsigma=((pi j).1 : Measure (LowValue d×unitInterval)) ∧
      (∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
        noisyExpectedUtility (N:=N) d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j,(w,q'))≤
          noisyExpectedUtility (N:=N) d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j,(w,q))))
    (hlim : Tendsto (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1)
      atTop (𝓝 pi0.1))
    [NullSingletonClass (pi0.1.map measurable_snd.aemeasurable : Measure (LowValue d))]
    (hvalue : ∀ᵐx ∂(pi0.1 : Measure (LowValue d×LowValue d)),0<x.1.1)
    (hpos : ∀ᵐx ∂(pi0.1 : Measure (LowValue d×LowValue d)),0<x.2.1)
    (a : C(LowValue d×LowValue d,ℝ)) (ha : ∀x,0≤a x)
    (hsupport : ∀x : LowValue d×LowValue d,x.1.1≤B→a x=0) :
    ∫x,a x*(exactExpectedPayoff N d ξ c categories
        (pi0.1.map measurable_snd.aemeasurable) (x.1.1,B)-
      exactExpectedPayoff N d ξ c categories
        (pi0.1.map measurable_snd.aemeasurable) (x.1.1,x.2.1))
        ∂(pi0.1 : Measure (LowValue d×LowValue d))≤0 := by
  let physical (j : ℕ):=(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1
  let G (j : ℕ):=implementedBidLaw d (eps j) (heps j) (hsmall j) mu (pi j)
  let G0:=pi0.1.map measurable_snd.aemeasurable
  let e (j : ℕ) : NoiseBox:=⟨eps j,(heps j).le,hquarter j⟩
  have he : Tendsto e atTop (𝓝 zeroNoiseBox) := tendsto_subtype_rng.mpr heps0
  have hG : Tendsto G atTop (𝓝 G0) := by
    have hh:=((ProbabilityMeasure.continuous_map continuous_snd).tendsto pi0.1).comp hlim
    simpa only [G,G0,implementedBidLaw,Function.comp_def] using hh
  have hP:=incumbentTest_tendsto (N:=N) hξ hξ1 c categories a physical pi0.1 G G0 hlim hG hpos
  have hD:=deviationTest_tendsto (N:=N) hξ hξ1 hB c categories a e he physical pi0.1 G G0 hlim hG hvalue
  have hPe:=actual_incumbent_test_error_tendsto_zero (N:=N) hξ hξ1 c categories mu eps heps hsmall heps0 pi a
  have hDe:=actual_deviation_test_error_tendsto_zero (N:=N) hξ hξ1 B c categories mu eps heps hquarter heps0 pi a
  have hLP : Tendsto (fun j=>latentIncumbentTest N d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j) a)
      atTop (𝓝 (incumbentTest N d ξ c categories pi0.1 G0 a)) := by
    simpa only [physical,G,sub_sub_cancel,sub_zero] using hP.sub hPe
  have hLD : Tendsto (fun j=>latentDeviationTest N d ξ (eps j) (heps j) (hquarter j) B c categories mu (pi j) a)
      atTop (𝓝 (deviationTest N d ξ B c categories zeroNoiseBox pi0.1 G0 a)) := by
    simpa only [physical,G,e,sub_sub_cancel,sub_zero] using hD.sub hDe
  have hnonpos (j : ℕ) : latentDeviationTest N d ξ (eps j) (heps j) (hquarter j) B c categories mu (pi j) a-
      latentIncumbentTest N d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j) a≤0 := by
    obtain ⟨sigma,hm,hdis,ho⟩:=hopt j
    letI : IsMarkovKernel sigma:=hm
    exact latent_test_gain_nonpos d hξ hξ1 (heps j) (hsmall j) (hquarter j) B c categories mu (pi j) sigma hdis ho a ha
  have hle : deviationTest N d ξ B c categories zeroNoiseBox pi0.1 G0 a-
      incumbentTest N d ξ c categories pi0.1 G0 a≤0 :=
    le_of_tendsto (hLD.sub hLP) (Eventually.of_forall hnonpos)
  rw [deviationTest_zero_eq_fixed hξ hξ1 hB c categories pi0.1 G0 a hsupport] at hle
  have hdMeas : Measurable (fun x : LowValue d×LowValue d=>
      exactExpectedPayoff N d ξ c categories G0 (x.1.1,B)) :=
    (measurable_exactExpectedPayoff hξ hξ1 c categories G0).comp (by fun_prop)
  have hiMeas : Measurable (fun x : LowValue d×LowValue d=>
      exactExpectedPayoff N d ξ c categories G0 (x.1.1,x.2.1)) :=
    (measurable_exactExpectedPayoff hξ hξ1 c categories G0).comp (by fun_prop)
  have hdBound (x : LowValue d×LowValue d) :
      |exactExpectedPayoff N d ξ c categories G0 (x.1.1,B)|≤|d|+(3+2*|1-ξ|)*|B| := by
    have hw : |x.1.1|≤|d| := by rw [abs_of_nonneg x.1.property.1]; exact x.1.property.2.trans (le_abs_self d)
    exact (abs_exactExpectedPayoff_le hξ hξ1 c categories G0 (x.1.1,B)).trans (by linarith)
  have hdI:=integrable_bounded_low_test (pi0.1 : Measure (LowValue d×LowValue d)) a id measurable_id
    _ hdMeas hdBound
  have hiI:=integrable_bounded_low_test (pi0.1 : Measure (LowValue d×LowValue d)) a id measurable_id
    _ hiMeas (fun x=>abs_exactExpectedPayoff_low_le hξ hξ1 c categories G0 x.1 x.2)
  simp only [id_eq] at hdI hiI
  change (∫x,a x*exactExpectedPayoff N d ξ c categories G0 (x.1.1,B) ∂(pi0.1 : Measure (LowValue d×LowValue d)))-
    (∫x,a x*exactExpectedPayoff N d ξ c categories G0 (x.1.1,x.2.1) ∂(pi0.1 : Measure (LowValue d×LowValue d)))≤0 at hle
  rw [←integral_sub hdI hiI] at hle
  convert hle using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>by ring)

theorem actual_noisy_limit_all_bid_IC {d ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2) (hquarter : ∀j,eps j≤1/4)
    (heps0 : Tendsto eps atTop (𝓝 0)) (pi : ℕ→Law (A:=unitInterval) mu)
    (pi0 : Law (A:=LowValue d) mu)
    (hopt : ∀j,∃sigma : Kernel (LowValue d) unitInterval,
      IsMarkovKernel sigma ∧ mu⊗ₘsigma=((pi j).1 : Measure (LowValue d×unitInterval)) ∧
      (∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
        noisyExpectedUtility (N:=N) d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j,(w,q'))≤
          noisyExpectedUtility (N:=N) d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j,(w,q))))
    (hlim : Tendsto (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1)
      atTop (𝓝 pi0.1))
    [NullSingletonClass (pi0.1.map measurable_snd.aemeasurable : Measure (LowValue d))]
    (hvalue : ∀ᵐx ∂(pi0.1 : Measure (LowValue d×LowValue d)),0<x.1.1)
    (hpos : ∀ᵐx ∂(pi0.1 : Measure (LowValue d×LowValue d)),0<x.2.1) :
    ∀ᵐx ∂(pi0.1 : Measure (LowValue d×LowValue d)),∀b : ℝ,0≤b→
      exactExpectedPayoff N d ξ c categories (pi0.1.map measurable_snd.aemeasurable) (x.1.1,b)≤
        exactExpectedPayoff N d ξ c categories (pi0.1.map measurable_snd.aemeasurable) (x.1.1,x.2.1) := by
  have hξ1 : ξ<1:=by linarith
  apply common_all_bid_IC_of_local_positive_IC hξ hξh c categories
    (pi0.1.map measurable_snd.aemeasurable) (pi0.1 : Measure _) hvalue
  intro B
  apply fixed_positive_bid_IC_of_tests hξ hξ1 B.property c categories
    (pi0.1.map measurable_snd.aemeasurable) pi0.1 hpos
  intro a ha hs
  exact actual_noisy_limit_fixed_bid_tests hξ hξ1 B.property c categories mu eps heps hsmall hquarter
    heps0 pi pi0 hopt hlim hvalue hpos a ha hs

end FCAppendix.Affine.LowBody
