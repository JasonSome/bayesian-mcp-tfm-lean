import FCAppendix.Affine.LowBody.ExactPayoffBounds
import FCAppendix.Affine.LowBody.DeviationNoiseBox

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
variable {N : ℕ}

private theorem low_abs_le {d : ℝ} (x : LowValue d) : |x.1|≤|d| := by
  rw [abs_of_nonneg x.property.1]
  exact x.property.2.trans (le_abs_self d)

theorem integral_test_exact_eq_row {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (pi : ProbabilityMeasure (LowValue d×LowValue d)) (G : ProbabilityMeasure (LowValue d))
    (a : C(LowValue d×LowValue d,ℝ))
    (phi : (LowValue d×LowValue d)×unitInterval→LowValue d) (hphi : Continuous phi) :
    (∫x : (LowValue d×LowValue d)×unitInterval,
      a x.1*exactExpectedPayoff N d ξ c categories G (x.1.1.1,(phi x).1)
        ∂(pi : Measure _).prod (volume : Measure unitInterval))=
    ∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
      ∫t : ((LowValue d×LowValue d)×(Fin N→LowValue d))×unitInterval,
        a t.1.1*patternActualPayoff d ξ c kind (t.1.1.1.1,(phi (t.1.1,t.2)).1,t.1.2)
          ∂(productLaw pi (rowLaw N G) : Measure _).prod (volume : Measure unitInterval) := by
  let C : ℝ:=(4+2*|1-ξ|)*|d|
  let R : Measure (Fin N→LowValue d):=Measure.pi (fun _ : Fin N=>(G : Measure (LowValue d)))
  let F (kind : Fin N→Fin 4) (t : ((LowValue d×LowValue d)×(Fin N→LowValue d))×unitInterval) : ℝ:=
    a t.1.1*patternActualPayoff d ξ c kind (t.1.1.1.1,(phi (t.1.1,t.2)).1,t.1.2)
  have hraw (kind : Fin N→Fin 4) : Measurable
      (fun t : ((LowValue d×LowValue d)×(Fin N→LowValue d))×unitInterval=>
        patternActualPayoff d ξ c kind (t.1.1.1.1,(phi (t.1.1,t.2)).1,t.1.2)) := by
    apply (measurable_patternActualPayoff hξ hξ1 c kind).comp
    exact (by fun_prop : Measurable (fun t : ((LowValue d×LowValue d)×(Fin N→LowValue d))×unitInterval=>
      (t.1.1.1.1,(phi (t.1.1,t.2)).1,t.1.2)))
  have hi (kind : Fin N→Fin 4) : Integrable (F kind)
      (((pi : Measure (LowValue d×LowValue d)).prod R).prod (volume : Measure unitInterval)) := by
    apply (integrable_const (‖a‖*C)).mono'
      (((a.continuous.measurable.comp (by fun_prop)).mul (hraw kind)).aestronglyMeasurable)
    exact ae_of_all _ (fun t=>by
      rw [Real.norm_eq_abs,Pi.mul_apply,Function.comp_apply,abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm t.1.1)
        (abs_physicalPatternPayoff_le hξ hξ1 c kind ((t.1.1.1,phi (t.1.1,t.2)),t.1.2))
        (abs_nonneg _) (norm_nonneg _))
  have hip (kind : Fin N→Fin 4) : Integrable (fun x : (LowValue d×LowValue d)×unitInterval=>
      a x.1*patternExpectedPayoff d ξ c kind G (x.1.1.1,(phi x).1))
      ((pi : Measure (LowValue d×LowValue d)).prod (volume : Measure unitInterval)) := by
    have hm : Measurable (fun x : (LowValue d×LowValue d)×unitInterval=>
        a x.1*patternExpectedPayoff d ξ c kind G (x.1.1.1,(phi x).1)) :=
      (a.continuous.measurable.comp measurable_fst).mul
        ((measurable_patternExpectedPayoff hξ hξ1 c kind G).comp (by fun_prop))
    apply (integrable_const (‖a‖*C)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun x=>by
      rw [Real.norm_eq_abs,abs_mul]
      apply mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm x.1) ?_
        (abs_nonneg _) (norm_nonneg _)
      exact (abs_patternExpectedPayoff_le hξ hξ1 c kind G (x.1.1.1,(phi x).1)).trans
        (by dsimp [C]; nlinarith [low_abs_le x.1.1,low_abs_le (phi x),abs_nonneg (1-ξ)]))
  have he (kind : Fin N→Fin 4) :
      (∫t,F kind t ∂((pi : Measure (LowValue d×LowValue d)).prod R).prod (volume : Measure unitInterval))=
      ∫x : (LowValue d×LowValue d)×unitInterval,
        a x.1*patternExpectedPayoff d ξ c kind G (x.1.1.1,(phi x).1)
          ∂(pi : Measure _).prod (volume : Measure unitInterval) := by
    rw [integral_prod _ (hi kind),integral_prod _ (hi kind).integral_prod_left,
      integral_prod _ (hip kind)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    have hix : Integrable (fun t : (Fin N→LowValue d)×unitInterval=>
        patternActualPayoff d ξ c kind (x.1.1,(phi (x,t.2)).1,t.1))
        (R.prod (volume : Measure unitInterval)) := by
      have hm : Measurable (fun t : (Fin N→LowValue d)×unitInterval=>
          patternActualPayoff d ξ c kind (x.1.1,(phi (x,t.2)).1,t.1)) :=
        (measurable_patternActualPayoff hξ hξ1 c kind).comp (by fun_prop)
      apply (integrable_const C).mono' hm.aestronglyMeasurable
      exact ae_of_all _ (fun t=>by
        rw [Real.norm_eq_abs]
        exact abs_physicalPatternPayoff_le hξ hξ1 c kind ((x.1,phi (x,t.2)),t.1))
    dsimp only [F]
    simp_rw [integral_const_mul]
    exact congrArg (fun v : ℝ=>a x*v) (integral_integral_swap hix)
  have hsum (x : (LowValue d×LowValue d)×unitInterval) :
      a x.1*exactExpectedPayoff N d ξ c categories G (x.1.1.1,(phi x).1)=
      ∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
        (a x.1*patternExpectedPayoff d ξ c kind G (x.1.1.1,(phi x).1)) := by
    unfold exactExpectedPayoff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kind _
    ring
  simp_rw [hsum]
  rw [integral_finsetSum _ (fun kind _=>(hip kind).const_mul _)]
  apply Finset.sum_congr rfl
  intro kind _
  rw [integral_const_mul,←he]
  change _=(CommonList.iid categories N).mass kind*
    ∫t,F kind t ∂((pi : Measure (LowValue d×LowValue d)).prod (rowLaw N G : Measure _)).prod
      (volume : Measure unitInterval)
  rw [rowLaw_eq_measure_pi]

end FCAppendix.Affine.LowBody
