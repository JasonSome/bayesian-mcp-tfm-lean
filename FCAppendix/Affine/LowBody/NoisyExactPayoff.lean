import FCAppendix.Affine.LowBody.ExactPayoffBounds
import FCAppendix.Affine.LowBody.NoisyWeightedIC

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
variable {N : ℕ}

theorem noisyExpectedUtility_eq_exact_noise (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (w : LowValue d) (q : unitInterval) :
    noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q))=
      ∫z : unitInterval,exactExpectedPayoff N d ξ c categories
        (implementedBidLaw d ε hε hsmall mu pi)
        (w.1,(noisyBid d ε hε hsmall ((w,q),z)).1) := by
  let G:=implementedBidLaw d ε hε hsmall mu pi
  let C : ℝ:=(4+2*|1-ξ|)*|d|
  have hc : Continuous (fun t : (Fin N→LowValue d)×unitInterval=>
      (w.1,(noisyBid d ε hε hsmall ((w,q),t.2)).1,t.1)) :=
    continuous_const.prodMk ((((continuous_noisyBid d ε hε hsmall).comp
      (continuous_const.prodMk continuous_snd)).subtype_val).prodMk continuous_fst)
  have hi (kind : Fin N→Fin 4) : Integrable
      (fun t : (Fin N→LowValue d)×unitInterval=>
        patternActualPayoff d ξ c kind (w.1,(noisyBid d ε hε hsmall ((w,q),t.2)).1,t.1))
      ((Measure.pi (fun _ : Fin N=>(G : Measure (LowValue d)))).prod (volume : Measure unitInterval)) := by
    apply (integrable_const C).mono'
      ((measurable_patternActualPayoff hξ hξ1 c kind).comp hc.measurable).aestronglyMeasurable
    exact ae_of_all _ (fun t=>by
      rw [Real.norm_eq_abs]
      exact abs_physicalPatternPayoff_le hξ hξ1 c kind ((w,noisyBid d ε hε hsmall ((w,q),t.2)),t.1))
  have he (kind : Fin N→Fin 4) :
      (∫r,patternSmoothedPayoff d ξ ε c kind ((w,q),r)
        ∂(rowLaw N G : Measure (Fin N→LowValue d)))=
      ∫z : unitInterval,patternExpectedPayoff d ξ c kind G
        (w.1,(noisyBid d ε hε hsmall ((w,q),z)).1) := by
    rw [rowLaw_eq_measure_pi]
    have heq (r : Fin N→LowValue d) :
        patternSmoothedPayoff d ξ ε c kind ((w,q),r)=
        ∫z : unitInterval,patternActualPayoff d ξ c kind
          (w.1,(noisyBid d ε hε hsmall ((w,q),z)).1,r) := by
      rw [patternSmoothedPayoff_eq_integral_patternActualPayoff]
      exact (integral_subtype measurableSet_Icc (fun z : ℝ=>
        patternActualPayoff d ξ c kind (w.1,w.1*bidRatio ε q*(1+ε*z),r))).symm
    simp_rw [heq]
    exact integral_integral_swap (hi kind)
  have hiz (kind : Fin N→Fin 4) : Integrable (fun z : unitInterval=>
      patternExpectedPayoff d ξ c kind G (w.1,(noisyBid d ε hε hsmall ((w,q),z)).1)) volume := by
    have hm : Measurable (fun z : unitInterval=>patternExpectedPayoff d ξ c kind G
        (w.1,(noisyBid d ε hε hsmall ((w,q),z)).1)) :=
      (measurable_patternExpectedPayoff hξ hξ1 c kind G).comp
        (measurable_const.prodMk (((continuous_noisyBid d ε hε hsmall).comp
          (continuous_const.prodMk continuous_id)).subtype_val.measurable))
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun z=>by
      rw [Real.norm_eq_abs]
      have hh:=abs_patternExpectedPayoff_le hξ hξ1 c kind G
        (w.1,(noisyBid d ε hε hsmall ((w,q),z)).1)
      have hw : |w.1|≤|d| := (abs_of_nonneg w.property.1).trans_le (w.property.2.trans (le_abs_self d))
      have hb : |(noisyBid d ε hε hsmall ((w,q),z)).1|≤|d| :=
        (abs_of_nonneg (noisyBid d ε hε hsmall ((w,q),z)).property.1).trans_le
          ((noisyBid d ε hε hsmall ((w,q),z)).property.2.trans (le_abs_self d))
      exact hh.trans (by dsimp [C]; nlinarith [abs_nonneg (1-ξ)]))
  change (∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
    ∫r,patternSmoothedPayoff d ξ ε c kind ((w,q),r) ∂(rowLaw N G : Measure _))=
      ∫z : unitInterval,∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
        patternExpectedPayoff d ξ c kind G (w.1,(noisyBid d ε hε hsmall ((w,q),z)).1)
  rw [integral_finsetSum _ (fun kind _=>(hiz kind).const_mul _)]
  apply Finset.sum_congr rfl
  intro kind _
  rw [he,integral_const_mul]

end FCAppendix.Affine.LowBody
