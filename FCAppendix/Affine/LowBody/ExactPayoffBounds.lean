import FCAppendix.Affine.LowBody.ExpectedPayoffContinuity
import FCAppendix.Affine.LowBody.ResidualOutcomes

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

variable {N : ℕ}

theorem patternActualPayoff_eq_patternPayoff (d ξ : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (t : ℝ×ℝ×(Fin N→LowValue d)) :
    patternActualPayoff d ξ c kind t=
      patternPayoff ξ c kind t.1 (actualPatternBids kind d t.2.1 t.2.2) := by
  rfl

theorem measurable_patternExpectedPayoff {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (G : ProbabilityMeasure (LowValue d)) :
    Measurable (patternExpectedPayoff d ξ c kind G) := by
  have hm : Measurable (fun t : (ℝ×ℝ)×(Fin N→LowValue d)=>
      patternActualPayoff d ξ c kind (t.1.1,t.1.2,t.2)) :=
    (measurable_patternActualPayoff hξ hξ1 c kind).comp (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_exactExpectedPayoff {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d)) :
    Measurable (exactExpectedPayoff N d ξ c categories G) := by
  apply Finset.measurable_sum
  intro kind _
  exact measurable_const.mul (measurable_patternExpectedPayoff hξ hξ1 c kind G)

theorem abs_patternExpectedPayoff_le {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (G : ProbabilityMeasure (LowValue d)) (t : ℝ×ℝ) :
    |patternExpectedPayoff d ξ c kind G t|≤|t.1|+(3+2*|1-ξ|)*|t.2| := by
  have hh:=norm_integral_le_of_norm_le
    (integrable_const (μ:=Measure.pi (fun _ : Fin N=>(G : Measure (LowValue d))))
      (|t.1|+(3+2*|1-ξ|)*|t.2|))
    (ae_of_all _ (fun r=>by
      rw [Real.norm_eq_abs]
      exact abs_patternActualPayoff_le hξ hξ1 c kind (t.1,t.2,r)))
  simpa only [patternExpectedPayoff,Real.norm_eq_abs,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

theorem abs_exactExpectedPayoff_le {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d)) (t : ℝ×ℝ) :
    |exactExpectedPayoff N d ξ c categories G t|≤|t.1|+(3+2*|1-ξ|)*|t.2| := by
  rw [abs_le]
  exact ⟨(CommonList.iid categories N).const_le_expect (fun kind=>
    (abs_le.mp (abs_patternExpectedPayoff_le hξ hξ1 c kind G t)).1),
    (CommonList.iid categories N).expect_le_const (fun kind=>
      (abs_le.mp (abs_patternExpectedPayoff_le hξ hξ1 c kind G t)).2)⟩

theorem patternActualPayoff_ge_neg_two_bid {d ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (kind : Fin N→Fin 4) {w b : ℝ} (hw : 0≤w) (hb : 0≤b)
    (r : Fin N→LowValue d) : -2*b≤patternActualPayoff d ξ c kind (w,b,r) := by
  rw [patternActualPayoff_eq_patternPayoff,patternPayoff_outcomes]
  have hout:=pattern_outcomes_bounds hξ (by linarith : ξ<1) c kind (actualPatternBids kind d b r)
  change -2*b≤(w-b)*patternServed ξ c kind (actualPatternBids kind d b r)-
    (1-2*ξ)*b*patternDuplicate ξ c kind (actualPatternBids kind d b r)
  have hwS:=mul_nonneg hw hout.1
  have hbS:=mul_le_mul_of_nonneg_left hout.2.1 hb
  have hk : 0≤(1-2*ξ)*b:=mul_nonneg (by linarith) hb
  have hkd:=mul_le_mul_of_nonneg_left hout.2.2.2 hk
  have hkb : (1-2*ξ)*b≤b:=by nlinarith
  nlinarith

theorem exactExpectedPayoff_ge_neg_two_bid {d ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    {w b : ℝ} (hw : 0≤w) (hb : 0≤b) :
    -2*b≤exactExpectedPayoff N d ξ c categories G (w,b) := by
  apply (CommonList.iid categories N).const_le_expect
  intro kind
  have hm : Measurable (fun r : Fin N→LowValue d=>patternActualPayoff d ξ c kind (w,b,r)) :=
    (measurable_patternActualPayoff hξ (by linarith : ξ<1) c kind).comp (by fun_prop)
  have hi : Integrable (fun r : Fin N→LowValue d=>patternActualPayoff d ξ c kind (w,b,r))
      (Measure.pi (fun _ : Fin N=>(G : Measure (LowValue d)))) :=
    (integrable_const (|w|+(3+2*|1-ξ|)*|b|)).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun r=>by simpa only [Real.norm_eq_abs] using
        abs_patternActualPayoff_le hξ (by linarith : ξ<1) c kind (w,b,r)))
  have hh:=integral_mono (integrable_const (-2*b)) hi
    (fun r=>patternActualPayoff_ge_neg_two_bid hξ hξh c kind hw hb r)
  simpa only [patternExpectedPayoff,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

theorem exactExpectedPayoff_nonpos_of_value_le_bid {d ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    {w b : ℝ} (hwb : w≤b) (hb : 0≤b) :
    exactExpectedPayoff N d ξ c categories G (w,b)≤0 := by
  apply (CommonList.iid categories N).expect_le_const
  intro kind
  apply integral_nonpos
  intro r
  change patternActualPayoff d ξ c kind (w,b,r)≤0
  rw [patternActualPayoff_eq_patternPayoff,patternPayoff_outcomes]
  have hout:=pattern_outcomes_bounds hξ (by linarith : ξ<1) c kind (actualPatternBids kind d b r)
  change (w-b)*patternServed ξ c kind (actualPatternBids kind d b r)-
    (1-2*ξ)*b*patternDuplicate ξ c kind (actualPatternBids kind d b r)≤0
  exact sub_nonpos.mpr ((mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hwb) hout.1).trans
    (mul_nonneg (mul_nonneg (by linarith) hb) hout.2.2.1))

end FCAppendix.Affine.LowBody
