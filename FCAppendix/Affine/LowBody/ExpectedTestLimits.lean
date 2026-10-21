import FCAppendix.Affine.LowBody.TestIntegralIdentities
import FCAppendix.Affine.LowBody.DeviationWeakPayoff

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
variable {N : ℕ}

private theorem integral_ignore_noise {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (f : X→ℝ) (hf : Measurable f) :
    (∫x : X×unitInterval,f x.1 ∂mu.prod (volume : Measure unitInterval))=∫x,f x ∂mu := by
  have hh:=integral_map (μ:=mu.prod (volume : Measure unitInterval))
    (φ:=Prod.fst) measurable_fst.aemeasurable hf.aestronglyMeasurable
  rw [(measurePreserving_fst (μ:=mu) (ν:=(volume : Measure unitInterval))).map_eq] at hh
  exact hh.symm

def incumbentTest (N : ℕ) (d ξ : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (pi : ProbabilityMeasure (LowValue d×LowValue d)) (G : ProbabilityMeasure (LowValue d))
    (a : C(LowValue d×LowValue d,ℝ)) : ℝ :=
  ∫x,a x*exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1) ∂(pi : Measure _)

def deviationTest (N : ℕ) (d ξ B : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (e : NoiseBox) (pi : ProbabilityMeasure (LowValue d×LowValue d))
    (G : ProbabilityMeasure (LowValue d)) (a : C(LowValue d×LowValue d,ℝ)) : ℝ :=
  ∫x : (LowValue d×LowValue d)×unitInterval,
    a x.1*exactExpectedPayoff N d ξ c categories G
      (x.1.1.1,(deviationPhysicalBid d B e x.1.1 x.2).1)
      ∂(pi : Measure (LowValue d×LowValue d)).prod (volume : Measure unitInterval)

theorem incumbentTest_eq_row {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (pi : ProbabilityMeasure (LowValue d×LowValue d)) (G : ProbabilityMeasure (LowValue d))
    (a : C(LowValue d×LowValue d,ℝ)) :
    incumbentTest N d ξ c categories pi G a=
      ∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
        ∫t,a t.1*physicalPatternPayoff d ξ c kind t ∂(productLaw pi (rowLaw N G) : Measure _) := by
  have hm : Measurable (fun x : LowValue d×LowValue d=>
      a x*exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)) :=
    a.continuous.measurable.mul ((measurable_exactExpectedPayoff hξ hξ1 c categories G).comp (by fun_prop))
  have hh:=integral_test_exact_eq_row (N:=N) hξ hξ1 c categories pi G a
    (fun x : (LowValue d×LowValue d)×unitInterval=>x.1.2) (by fun_prop)
  rw [integral_ignore_noise (pi : Measure _) _ hm] at hh
  apply hh.trans
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  have hr : Measurable (fun t : (LowValue d×LowValue d)×(Fin N→LowValue d)=>
      a t.1*physicalPatternPayoff d ξ c kind t) :=
    (a.continuous.measurable.comp measurable_fst).mul
      ((measurable_patternActualPayoff hξ hξ1 c kind).comp (continuous_physicalPatternInput d).measurable)
  exact integral_ignore_noise (productLaw pi (rowLaw N G) : Measure _) _ hr

theorem incumbentTest_tendsto {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (a : C(LowValue d×LowValue d,ℝ))
    (pi : ℕ→ProbabilityMeasure (LowValue d×LowValue d)) (pi0 : ProbabilityMeasure (LowValue d×LowValue d))
    (G : ℕ→ProbabilityMeasure (LowValue d)) (G0 : ProbabilityMeasure (LowValue d))
    [NullSingletonClass (G0 : Measure (LowValue d))]
    (hpi : Tendsto pi atTop (𝓝 pi0)) (hG : Tendsto G atTop (𝓝 G0))
    (hpos : ∀ᵐx ∂(pi0 : Measure (LowValue d×LowValue d)),0<x.2.1) :
    Tendsto (fun j=>incumbentTest N d ξ c categories (pi j) (G j) a) atTop
      (𝓝 (incumbentTest N d ξ c categories pi0 G0 a)) := by
  let M (j : ℕ):=productLaw (pi j) (rowLaw N (G j))
  have hrow : Tendsto (fun j=>rowLaw N (G j)) atTop (𝓝 (rowLaw N G0)) :=
    (continuous_rowLaw N).tendsto G0 |>.comp hG
  have hm : Tendsto M atTop (𝓝 (productLaw pi0 (rowLaw N G0))) := by
    have hh:=(continuous_productLaw.tendsto (pi0,rowLaw N G0)).comp (hpi.prodMk_nhds hrow)
    simpa only [M,Function.comp_def] using hh
  let ar : C((LowValue d×LowValue d)×(Fin N→LowValue d),ℝ):=
    ⟨fun t=>a t.1,a.continuous.comp continuous_fst⟩
  have hk (kind : Fin N→Fin 4) : Tendsto
      (fun j=>(CommonList.iid categories N).mass kind*
        ∫t,ar t*physicalPatternPayoff d ξ c kind t ∂(M j : Measure _)) atTop
      (𝓝 ((CommonList.iid categories N).mass kind*
        ∫t,ar t*physicalPatternPayoff d ξ c kind t ∂(productLaw pi0 (rowLaw N G0) : Measure _))) :=
    tendsto_const_nhds.mul
      (tendsto_integral_physicalPatternTest hξ hξ1 c kind ar pi0 G0 hpos M hm)
  have hh:=tendsto_finsetSum Finset.univ (fun kind _=>hk kind)
  simpa only [incumbentTest_eq_row hξ hξ1 c categories,ar,ContinuousMap.coe_mk,M] using hh

theorem deviationTest_eq_row {d ξ B : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (e : NoiseBox)
    (pi : ProbabilityMeasure (LowValue d×LowValue d)) (G : ProbabilityMeasure (LowValue d))
    (a : C(LowValue d×LowValue d,ℝ)) :
    deviationTest N d ξ B c categories e pi G a=
      ∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
        ∫t : DeviationSample d N,a t.2.1.1*patternActualPayoff d ξ c kind (deviationPatternInput d B t)
          ∂(deviationSampleLaw e (productLaw pi (rowLaw N G)) : Measure _) := by
  let phi : (LowValue d×LowValue d)×unitInterval→LowValue d:=
    fun x=>deviationPhysicalBid d B e x.1.1 x.2
  have hp : Continuous phi := (continuous_deviationPhysicalBid d B).comp
    (show Continuous (fun x : (LowValue d×LowValue d)×unitInterval=>(e,x.1.1,x.2)) by fun_prop)
  have hh:=integral_test_exact_eq_row (N:=N) hξ hξ1 c categories pi G a phi hp
  apply hh.trans
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  have hm : Measurable (fun t : DeviationSample d N=>
      a t.2.1.1*patternActualPayoff d ξ c kind (deviationPatternInput d B t)) :=
    (a.continuous.measurable.comp (by fun_prop)).mul
      ((measurable_patternActualPayoff hξ hξ1 c kind).comp (continuous_deviationPatternInput d B).measurable)
  change _=∫t : DeviationSample d N,
    a t.2.1.1*patternActualPayoff d ξ c kind (deviationPatternInput d B t)
      ∂(Measure.dirac e).prod ((productLaw pi (rowLaw N G) : Measure _).prod (volume : Measure unitInterval))
  rw [Measure.dirac_prod,integral_map measurable_prodMk_left.aemeasurable hm.aestronglyMeasurable]
  rfl

theorem deviationTest_tendsto {d ξ B : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hB : 0<B)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (a : C(LowValue d×LowValue d,ℝ))
    (eps : ℕ→NoiseBox) (heps : Tendsto eps atTop (𝓝 zeroNoiseBox))
    (pi : ℕ→ProbabilityMeasure (LowValue d×LowValue d)) (pi0 : ProbabilityMeasure (LowValue d×LowValue d))
    (G : ℕ→ProbabilityMeasure (LowValue d)) (G0 : ProbabilityMeasure (LowValue d))
    [NullSingletonClass (G0 : Measure (LowValue d))]
    (hpi : Tendsto pi atTop (𝓝 pi0)) (hG : Tendsto G atTop (𝓝 G0))
    (hvalue : ∀ᵐx ∂(pi0 : Measure (LowValue d×LowValue d)),0<x.1.1) :
    Tendsto (fun j=>deviationTest N d ξ B c categories (eps j) (pi j) (G j) a) atTop
      (𝓝 (deviationTest N d ξ B c categories zeroNoiseBox pi0 G0 a)) := by
  let M (j : ℕ):=productLaw (pi j) (rowLaw N (G j))
  have hrow : Tendsto (fun j=>rowLaw N (G j)) atTop (𝓝 (rowLaw N G0)) :=
    (continuous_rowLaw N).tendsto G0 |>.comp hG
  have hm : Tendsto M atTop (𝓝 (productLaw pi0 (rowLaw N G0))) := by
    have hh:=(continuous_productLaw.tendsto (pi0,rowLaw N G0)).comp (hpi.prodMk_nhds hrow)
    simpa only [M,Function.comp_def] using hh
  have hk (kind : Fin N→Fin 4) : Tendsto
      (fun j=>(CommonList.iid categories N).mass kind*
        ∫t : DeviationSample d N,a t.2.1.1*patternActualPayoff d ξ c kind (deviationPatternInput d B t)
          ∂(deviationSampleLaw (eps j) (M j) : Measure _)) atTop
      (𝓝 ((CommonList.iid categories N).mass kind*
        ∫t : DeviationSample d N,a t.2.1.1*patternActualPayoff d ξ c kind (deviationPatternInput d B t)
          ∂(deviationSampleLaw zeroNoiseBox (productLaw pi0 (rowLaw N G0)) : Measure _))) :=
    tendsto_const_nhds.mul (tendsto_integral_deviationPatternTest hξ hξ1 hB c kind a pi0 G0 hvalue eps heps M hm)
  have hh:=tendsto_finsetSum Finset.univ (fun kind _=>hk kind)
  simpa only [deviationTest_eq_row hξ hξ1 c categories,M] using hh

theorem deviationTest_zero_eq_fixed {d ξ B : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hB : 0<B)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (pi : ProbabilityMeasure (LowValue d×LowValue d)) (G : ProbabilityMeasure (LowValue d))
    (a : C(LowValue d×LowValue d,ℝ))
    (hsupport : ∀x : LowValue d×LowValue d,x.1.1≤B→a x=0) :
    deviationTest N d ξ B c categories zeroNoiseBox pi G a=
      ∫x,a x*exactExpectedPayoff N d ξ c categories G (x.1.1,B) ∂(pi : Measure _) := by
  unfold deviationTest
  simp_rw [deviationPhysicalBid_zero d B hB]
  have hm : Measurable (fun x : LowValue d×LowValue d=>
      a x*exactExpectedPayoff N d ξ c categories G (x.1.1,min x.1.1 B)) :=
    a.continuous.measurable.mul ((measurable_exactExpectedPayoff hξ hξ1 c categories G).comp (by fun_prop))
  rw [integral_ignore_noise (pi : Measure _) _ hm]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  by_cases hx : x.1.1≤B
  · rw [hsupport x hx,zero_mul,zero_mul]
  · rw [min_eq_right (le_of_not_ge hx)]

end FCAppendix.Affine.LowBody
