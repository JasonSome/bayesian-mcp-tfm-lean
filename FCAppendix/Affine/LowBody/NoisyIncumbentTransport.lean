import FCAppendix.Affine.LowBody.NoisyExactPayoff
import FCAppendix.Affine.LowBody.ExpectedTestLimits

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
variable {N : ℕ}

theorem abs_exactExpectedPayoff_low_le {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    (w b : LowValue d) :
    |exactExpectedPayoff N d ξ c categories G (w.1,b.1)|≤(4+2*|1-ξ|)*|d| := by
  have hw : |w.1|≤|d| := by rw [abs_of_nonneg w.property.1]; exact w.property.2.trans (le_abs_self d)
  have hb : |b.1|≤|d| := by rw [abs_of_nonneg b.property.1]; exact b.property.2.trans (le_abs_self d)
  exact (abs_exactExpectedPayoff_le hξ hξ1 c categories G (w.1,b.1)).trans
    (by nlinarith [abs_nonneg (1-ξ)])

theorem integrable_bounded_low_test {Omega : Type*} [MeasurableSpace Omega] {d C : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (a : C(LowValue d×LowValue d,ℝ)) (p : Omega→LowValue d×LowValue d) (hp : Measurable p)
    (F : Omega→ℝ) (hF : Measurable F) (hbound : ∀x,|F x|≤C) :
    Integrable (fun x=>a (p x)*F x) mu := by
  apply (integrable_const (‖a‖*C)).mono' ((a.continuous.measurable.comp hp).mul hF).aestronglyMeasurable
  exact ae_of_all _ (fun x=>by
    rw [Real.norm_eq_abs,Pi.mul_apply,Function.comp_apply,abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm (p x))
      (hbound x) (abs_nonneg _) (norm_nonneg _))

theorem measurable_basePhysicalPoint (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2) :
    Measurable (basePhysicalPoint d ε hε hsmall) :=
  (continuous_fst.prodMk ((continuous_noisyBid d ε hε hsmall).comp
    (continuous_id.prodMk continuous_const))).measurable

theorem measurable_noisyPhysicalPoint (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2) :
    Measurable (noisyPhysicalPoint d ε hε hsmall) :=
  (continuous_fst.fst.prodMk (continuous_noisyBid d ε hε hsmall)).measurable

theorem integral_lowNoisyLaw_measurable (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (f : LowValue d×LowValue d→ℝ) (hf : Measurable f) :
    (∫x,f x ∂((lowNoisyLaw d ε hε hsmall mu pi).1 : Measure (LowValue d×LowValue d)))=
      ∫x,f (noisyPhysicalPoint d ε hε hsmall x)
        ∂((pi.1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)) :=
  integral_map (measurable_noisyPhysicalPoint d ε hε hsmall).aemeasurable hf.aestronglyMeasurable

def latentIncumbentTest (N : ℕ) (d ξ ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (a : C(LowValue d×LowValue d,ℝ)) : ℝ :=
  ∫x,a (basePhysicalPoint d ε hε hsmall x)*
    noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,x)
      ∂(pi.1 : Measure (LowValue d×unitInterval))

theorem actual_incumbent_test_error_tendsto_zero {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2)
    (heps0 : Tendsto eps atTop (𝓝 0)) (pi : ℕ→Law (A:=unitInterval) mu)
    (a : C(LowValue d×LowValue d,ℝ)) :
    Tendsto (fun j=>incumbentTest N d ξ c categories
        (lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1
        (implementedBidLaw d (eps j) (heps j) (hsmall j) mu (pi j)) a-
      latentIncumbentTest N d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j) a)
      atTop (𝓝 0) := by
  let M (j : ℕ) : Measure ((LowValue d×unitInterval)×unitInterval):=
    ((pi j).1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)
  letI (j : ℕ) : IsProbabilityMeasure (M j):=inferInstanceAs
    (IsProbabilityMeasure (((pi j).1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)))
  let G (j : ℕ):=implementedBidLaw d (eps j) (heps j) (hsmall j) mu (pi j)
  let F (j : ℕ) (x : (LowValue d×unitInterval)×unitInterval) : ℝ:=
    exactExpectedPayoff N d ξ c categories (G j)
      (x.1.1.1,(noisyBid d (eps j) (heps j) (hsmall j) x).1)
  have hF (j : ℕ) : Measurable (F j) :=
    (measurable_exactExpectedPayoff hξ hξ1 c categories (G j)).comp
      (measurable_fst.fst.subtype_val.prodMk
        (continuous_noisyBid d (eps j) (heps j) (hsmall j)).subtype_val.measurable)
  have hbound (j : ℕ) (x : (LowValue d×unitInterval)×unitInterval) :
      |F j x|≤(4+2*|1-ξ|)*|d| :=
    abs_exactExpectedPayoff_low_le hξ hξ1 c categories (G j) x.1.1
      (noisyBid d (eps j) (heps j) (hsmall j) x)
  have hib (j : ℕ) := integrable_bounded_low_test (M j) a
    (fun x=>basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1)
    ((measurable_basePhysicalPoint d (eps j) (heps j) (hsmall j)).comp measurable_fst) (F j) (hF j) (hbound j)
  have hip (j : ℕ) := integrable_bounded_low_test (M j) a
    (noisyPhysicalPoint d (eps j) (heps j) (hsmall j))
    (measurable_noisyPhysicalPoint d (eps j) (heps j) (hsmall j)) (F j) (hF j) (hbound j)
  have hbase (j : ℕ) : latentIncumbentTest N d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j) a=
      ∫x,a (basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1)*F j x ∂M j := by
    rw [integral_prod _ (hib j)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only [F,G]
    rw [integral_const_mul]
    exact congrArg (fun u : ℝ=>a (basePhysicalPoint d (eps j) (heps j) (hsmall j) x)*u)
      (noisyExpectedUtility_eq_exact_noise d hξ hξ1 (heps j) (hsmall j) c categories mu (pi j) x.1 x.2)
  have hphys (j : ℕ) : incumbentTest N d ξ c categories
      (lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1 (G j) a=
      ∫x,a (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) x)*F j x ∂M j := by
    apply integral_lowNoisyLaw_measurable
    exact a.continuous.measurable.mul ((measurable_exactExpectedPayoff hξ hξ1 c categories (G j)).comp (by fun_prop))
  have herr:=noisy_test_error_tendsto_zero a eps heps hsmall heps0 M (fun _ x=>x) F
    (show 0≤(4+2*|1-ξ|)*|d| by positivity) hbound
  convert herr using 1
  funext j
  rw [hphys,hbase,←integral_sub (hip j) (hib j)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>by ring)

end FCAppendix.Affine.LowBody
