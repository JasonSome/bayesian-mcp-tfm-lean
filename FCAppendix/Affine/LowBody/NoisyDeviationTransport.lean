import FCAppendix.Affine.LowBody.NoisyIncumbentTransport

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
variable {N : ℕ}

def ratioNoisyUtility (N : ℕ) (d ξ ε : ℝ) (hε : 0<ε) (hquarter : ε ≤ 1/4)
    (B : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (w : LowValue d) : ℝ:=
  noisyExpectedUtility (N:=N) d ξ ε hε (by linarith) c categories mu
    (pi,(w,choiceAtRatio ε hε hquarter (B/w.1)))

theorem measurable_ratioNoisyUtility (d : ℝ) {ξ ε : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (hε : 0<ε) (hquarter : ε ≤ 1/4) (B : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu) :
    Measurable (ratioNoisyUtility N d ξ ε hε hquarter B c categories mu pi) := by
  have hu : Continuous (fun x : LowValue d×unitInterval=>
      noisyExpectedUtility (N:=N) d ξ ε hε (by linarith) c categories mu (pi,x)) :=
    (continuous_noisyExpectedUtility d hξ hξ1 hε (by linarith) c categories mu).comp
      (continuous_const.prodMk continuous_id)
  exact hu.measurable.comp (measurable_id.prodMk
    ((continuous_choiceAtRatio ε hε hquarter).measurable.comp
      (measurable_const.div measurable_subtype_coe)))

theorem abs_ratioNoisyUtility_le (d : ℝ) {ξ ε : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (hε : 0<ε) (hquarter : ε ≤ 1/4) (B : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (w : LowValue d) :
    |ratioNoisyUtility N d ξ ε hε hquarter B c categories mu pi w| ≤ (4+2*|1-ξ|)*|d| := by
  unfold ratioNoisyUtility
  rw [noisyExpectedUtility_eq_exact_noise d hξ hξ1 hε (by linarith) c categories mu pi]
  have hbound (z : unitInterval) :
      ‖exactExpectedPayoff N d ξ c categories (implementedBidLaw d ε hε (by linarith) mu pi)
        (w.1,(noisyBid d ε hε (by linarith) ((w,choiceAtRatio ε hε hquarter (B/w.1)),z)).1)‖ ≤
        (4+2*|1-ξ|)*|d| := by
    rw [Real.norm_eq_abs]
    exact abs_exactExpectedPayoff_low_le hξ hξ1 c categories
      (implementedBidLaw d ε hε (by linarith) mu pi) w
      (noisyBid d ε hε (by linarith) ((w,choiceAtRatio ε hε hquarter (B/w.1)),z))
  have hh:=norm_integral_le_of_norm_le_const (μ:=(volume : Measure unitInterval)) (ae_of_all _ hbound)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

def latentDeviationTest (N : ℕ) (d ξ ε : ℝ) (hε : 0<ε) (hquarter : ε ≤ 1/4)
    (B : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (a : C(LowValue d×LowValue d,ℝ)) : ℝ:=
  ∫x,a (basePhysicalPoint d ε hε (by linarith) x)*
    ratioNoisyUtility N d ξ ε hε hquarter B c categories mu pi x.1
      ∂(pi.1 : Measure (LowValue d×unitInterval))

theorem deviationTest_eq_ratioNoisyUtility (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hquarter : ε ≤ 1/4)
    (B : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (a : C(LowValue d×LowValue d,ℝ)) :
    deviationTest N d ξ B c categories ⟨ε,hε.le,hquarter⟩
      (lowNoisyLaw d ε hε (by linarith) mu pi).1
      (implementedBidLaw d ε hε (by linarith) mu pi) a=
      ∫x,a x*ratioNoisyUtility N d ξ ε hε hquarter B c categories mu pi x.1
        ∂((lowNoisyLaw d ε hε (by linarith) mu pi).1 : Measure (LowValue d×LowValue d)) := by
  let G:=implementedBidLaw d ε hε (by linarith) mu pi
  let P:=((lowNoisyLaw d ε hε (by linarith) mu pi).1 : Measure (LowValue d×LowValue d))
  let e : NoiseBox:=⟨ε,hε.le,hquarter⟩
  let F : (LowValue d×LowValue d)×unitInterval→ℝ:=fun x=>
    exactExpectedPayoff N d ξ c categories G (x.1.1.1,(deviationPhysicalBid d B e x.1.1 x.2).1)
  have hF : Measurable F:=(measurable_exactExpectedPayoff hξ hξ1 c categories G).comp
    (measurable_fst.fst.subtype_val.prodMk
      (((continuous_deviationPhysicalBid d B).comp
        (continuous_const.prodMk (continuous_fst.fst.prodMk continuous_snd))).subtype_val.measurable))
  have hbound (x : (LowValue d×LowValue d)×unitInterval) : |F x| ≤ (4+2*|1-ξ|)*|d|:=
    abs_exactExpectedPayoff_low_le hξ hξ1 c categories G x.1.1 (deviationPhysicalBid d B e x.1.1 x.2)
  have hi:=integrable_bounded_low_test (P.prod (volume : Measure unitInterval)) a
    Prod.fst measurable_fst F hF hbound
  change (∫x,a x.1*F x ∂P.prod (volume : Measure unitInterval))=_
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [integral_const_mul]
  congr 1
  unfold ratioNoisyUtility
  rw [noisyExpectedUtility_eq_exact_noise d hξ hξ1 hε (by linarith) c categories mu pi]
  apply integral_congr_ae
  exact ae_of_all _ (fun z=>by
    dsimp only [F,G,e]
    rw [deviationPhysicalBid_choice hε hquarter])

theorem actual_deviation_test_error_tendsto_zero {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (B : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hquarter : ∀j,eps j ≤ 1/4)
    (heps0 : Tendsto eps atTop (𝓝 0)) (pi : ℕ→Law (A:=unitInterval) mu)
    (a : C(LowValue d×LowValue d,ℝ)) :
    Tendsto (fun j=>deviationTest N d ξ B c categories ⟨eps j,(heps j).le,hquarter j⟩
        (lowNoisyLaw d (eps j) (heps j) (by linarith [hquarter j]) mu (pi j)).1
        (implementedBidLaw d (eps j) (heps j) (by linarith [hquarter j]) mu (pi j)) a-
      latentDeviationTest N d ξ (eps j) (heps j) (hquarter j) B c categories mu (pi j) a)
      atTop (𝓝 0) := by
  let hsmall (j : ℕ) : eps j ≤ 1/2:=by linarith [hquarter j]
  let M (j : ℕ) : Measure ((LowValue d×unitInterval)×unitInterval):=
    ((pi j).1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)
  letI (j : ℕ) : IsProbabilityMeasure (M j):=inferInstanceAs
    (IsProbabilityMeasure (((pi j).1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)))
  let F (j : ℕ) (x : (LowValue d×unitInterval)×unitInterval) : ℝ:=
    ratioNoisyUtility N d ξ (eps j) (heps j) (hquarter j) B c categories mu (pi j) x.1.1
  have hF (j : ℕ) : Measurable (F j):=
    (measurable_ratioNoisyUtility d hξ hξ1 (heps j) (hquarter j) B c categories mu (pi j)).comp measurable_fst.fst
  have hbound (j : ℕ) (x : (LowValue d×unitInterval)×unitInterval) :
      |F j x| ≤ (4+2*|1-ξ|)*|d|:=
    abs_ratioNoisyUtility_le d hξ hξ1 (heps j) (hquarter j) B c categories mu (pi j) x.1.1
  have hib (j : ℕ):=integrable_bounded_low_test (M j) a
    (fun x=>basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1)
    ((measurable_basePhysicalPoint d (eps j) (heps j) (hsmall j)).comp measurable_fst) (F j) (hF j) (hbound j)
  have hip (j : ℕ):=integrable_bounded_low_test (M j) a
    (noisyPhysicalPoint d (eps j) (heps j) (hsmall j))
    (measurable_noisyPhysicalPoint d (eps j) (heps j) (hsmall j)) (F j) (hF j) (hbound j)
  have hbase (j : ℕ) : latentDeviationTest N d ξ (eps j) (heps j) (hquarter j) B c categories mu (pi j) a=
      ∫x,a (basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1)*F j x ∂M j:=by
    rw [integral_prod _ (hib j)]
    simp only [F,integral_const,probReal_univ,smul_eq_mul,one_mul]
    rfl
  have hphys (j : ℕ) : deviationTest N d ξ B c categories ⟨eps j,(heps j).le,hquarter j⟩
      (lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1
      (implementedBidLaw d (eps j) (heps j) (hsmall j) mu (pi j)) a=
      ∫x,a (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) x)*F j x ∂M j:=by
    rw [deviationTest_eq_ratioNoisyUtility d hξ hξ1 (heps j) (hquarter j) B c categories mu (pi j)]
    exact integral_lowNoisyLaw_measurable d (eps j) (heps j) (hsmall j) mu (pi j) _
      (a.continuous.measurable.mul ((measurable_ratioNoisyUtility d hξ hξ1 (heps j)
        (hquarter j) B c categories mu (pi j)).comp measurable_fst))
  have herr:=noisy_test_error_tendsto_zero a eps heps hsmall heps0 M (fun _ x=>x) F
    (show 0 ≤ (4+2*|1-ξ|)*|d| by positivity) hbound
  convert herr using 1
  funext j
  rw [hphys,hbase,←integral_sub (hip j) (hib j)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>by ring)

end FCAppendix.Affine.LowBody
