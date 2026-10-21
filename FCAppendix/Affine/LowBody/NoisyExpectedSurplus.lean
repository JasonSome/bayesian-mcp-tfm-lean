import FCAppendix.Affine.LowBody.NoisySurplus
import FCAppendix.Affine.LowBody.ArrivalUnderflow

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional
open scoped BigOperators
variable {N : ℕ}

theorem integrable_patternSmoothedPayoff (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (kind : Fin N→Fin 4) (w : LowValue d) (q : unitInterval)
    (ν : ProbabilityMeasure (Fin N→LowValue d)) :
    Integrable (fun b=>patternSmoothedPayoff d ξ ε c kind ((w,q),b)) (ν : Measure _) := by
  have hc : Continuous (fun b : Fin N→LowValue d=>patternSmoothedPayoff d ξ ε c kind ((w,q),b)) :=
    (continuous_patternSmoothedPayoff d hξ hξ1 hε hsmall c kind).comp
      (continuous_const.prodMk continuous_id)
  exact (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,hc⟩).integrable _

theorem noisyExpectedUtility_le_surplus (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (w : LowValue d) (q : unitInterval) :
    noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q))≤
      w.1-w.1*bidRatio ε q := by
  change (CommonList.iid categories N).expect _≤_
  apply FiniteLaw.expect_le_const
  intro kind
  have hi:=integrable_patternSmoothedPayoff d hξ (by linarith) hε hsmall c kind w q
    (rowLaw N (implementedBidLaw d ε hε hsmall mu pi))
  have hh:=integral_mono_ae hi (integrable_const (w.1-w.1*bidRatio ε q))
    (ae_of_all _ (fun b=>patternSmoothedPayoff_le_surplus d hξ hξh hε hsmall c kind w q b))
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

theorem noisyExpectedUtility_comparison_lower (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hε : 0<ε) (hsmall : ε≤1/4)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (w : LowValue d) (hw : 0<w.1) :
    w.1/2*((CommonList.iid categories N).prob (LocalUnderflow c 0)-
      (CommonList.iid categories N).prob (BothUnderflow c))≤
      noisyExpectedUtility (N:=N) d ξ ε hε (by linarith) c categories mu (pi,(w,quarterChoice)) := by
  let ν:=rowLaw N (implementedBidLaw d ε hε (by linarith) mu pi)
  have hh : (CommonList.iid categories N).expect (fun kind=>w.1/2*
      ((if LocalUnderflow c 0 kind then (1:ℝ) else 0)-(if BothUnderflow c kind then 1 else 0)))≤
      noisyExpectedUtility (N:=N) d ξ ε hε (by linarith) c categories mu (pi,(w,quarterChoice)) := by
    apply FiniteLaw.expect_mono
    intro kind
    have hi:=integrable_patternSmoothedPayoff d hξ (by linarith) hε (by linarith) c kind w quarterChoice ν
    have ht:=integral_mono_ae (integrable_const (w.1/2*((if LocalUnderflow c 0 kind then (1:ℝ) else 0)-
      (if BothUnderflow c kind then 1 else 0)))) hi
      (ae_of_all _ (fun b=>patternSmoothedPayoff_comparison_lower d hξ hξh hε hsmall c kind w hw b))
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ht
  rw [FiniteLaw.expect_const_mul,FiniteLaw.expect_sub,
    ←FiniteLaw.prob_eq_expect,←FiniteLaw.prob_eq_expect] at hh
  exact hh

theorem noisy_supported_surplus (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hε : 0<ε) (hsmall : ε≤1/4)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (w : LowValue d) (hw : 0<w.1) (q : unitInterval)
    (hopt : noisyExpectedUtility (N:=N) d ξ ε hε (by linarith) c categories mu (pi,(w,quarterChoice))≤
      noisyExpectedUtility (N:=N) d ξ ε hε (by linarith) c categories mu (pi,(w,q)))
    (hjoint : (CommonList.iid categories N).prob (BothUnderflow c)≤
      (CommonList.iid categories N).prob (LocalUnderflow c 0)/4) :
    w.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤w.1-w.1*bidRatio ε q := by
  have hlo:=noisyExpectedUtility_comparison_lower (N:=N) d hξ hξh hε hsmall c categories mu pi w hw
  have hhi:=noisyExpectedUtility_le_surplus (N:=N) d hξ hξh hε (by linarith) c categories mu pi w q
  have hnon:=(CommonList.iid categories N).prob_nonneg (LocalUnderflow c 0)
  have hdif : (CommonList.iid categories N).prob (LocalUnderflow c 0)/2≤
      (CommonList.iid categories N).prob (LocalUnderflow c 0)-
        (CommonList.iid categories N).prob (BothUnderflow c) := by linarith
  have hm:=mul_le_mul_of_nonneg_left hdif (show 0≤w.1/2 by positivity)
  linarith [hlo.trans (hopt.trans hhi)]

end FCAppendix.Affine.LowBody
