import FCAppendix.Affine.LowBody.ExactPayoffBounds

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
variable {N : ℕ}

theorem actualPatternBids_mask {d b : ℝ} (c : ℕ) (kind : Fin N→Fin 4)
    (r : Fin N→LowValue d) :
    ∀i,i∉(patternTemplate c kind).support→actualPatternBids kind d b r i=0 := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · intro hi
    exact False.elim (hi (focal_mem_patternTemplate c kind))
  · intro hi
    have hj : kind j≠0 := by
      intro he
      apply hi
      simp [patternTemplate,patternRow,rowLowList,he]
    simp only [actualPatternBids,Fin.cons_succ,if_neg hj]

theorem integrable_patternActualPayoff {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (G : ProbabilityMeasure (LowValue d)) (w b : ℝ) :
    Integrable (fun r : Fin N→LowValue d=>patternActualPayoff d ξ c kind (w,b,r))
      (Measure.pi (fun _ : Fin N=>(G : Measure (LowValue d)))) := by
  have hm : Measurable (fun r : Fin N→LowValue d=>patternActualPayoff d ξ c kind (w,b,r)) :=
    (measurable_patternActualPayoff hξ hξ1 c kind).comp (by fun_prop)
  exact (integrable_const (|w|+(3+2*|1-ξ|)*|b|)).mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun r=>by simpa only [Real.norm_eq_abs] using
      abs_patternActualPayoff_le hξ hξ1 c kind (w,b,r)))

theorem patternExpectedPayoff_half_bid_lower {d ξ w : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hw : 0<w)
    (c : ℕ) (kind : Fin N→Fin 4) (G : ProbabilityMeasure (LowValue d)) :
    w/2*((if LocalUnderflow c 0 kind then 1 else 0)-(if BothUnderflow c kind then 1 else 0))≤
      patternExpectedPayoff d ξ c kind G (w,w/2) := by
  have hi:=integrable_patternActualPayoff hξ (by linarith : ξ<1) c kind G w (w/2)
  have hh:=integral_mono (integrable_const
    (w/2*((if LocalUnderflow c 0 kind then 1 else 0)-(if BothUnderflow c kind then 1 else 0)))) hi
    (fun r=>show w/2*((if LocalUnderflow c 0 kind then 1 else 0)-
      (if BothUnderflow c kind then 1 else 0))≤patternActualPayoff d ξ c kind (w,w/2,r) from by
      rw [patternActualPayoff_eq_patternPayoff]
      apply patternPayoff_comparison_lower hξ hξh c kind (actualPatternBids kind d (w/2) r)
      · simpa only [actualPatternBids,Fin.cons_zero] using half_pos hw
      · simp only [actualPatternBids,Fin.cons_zero,le_refl]
      · exact actualPatternBids_mask c kind r)
  simpa only [patternExpectedPayoff,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

theorem exactExpectedPayoff_half_bid_lower {d ξ w : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hw : 0<w) (c : ℕ)
    (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d)) :
    w/2*((CommonList.iid categories N).prob (LocalUnderflow c 0)-
      (CommonList.iid categories N).prob (BothUnderflow c))≤
      exactExpectedPayoff N d ξ c categories G (w,w/2) := by
  let row:=CommonList.iid categories N
  calc
    _=row.expect (fun kind=>w/2*((if LocalUnderflow c 0 kind then 1 else 0)-
        (if BothUnderflow c kind then 1 else 0))) := by
      rw [row.expect_const_mul,row.expect_sub,←row.prob_eq_expect,←row.prob_eq_expect]
    _≤row.expect (fun kind=>patternExpectedPayoff d ξ c kind G (w,w/2)) :=
      row.expect_mono (fun kind=>patternExpectedPayoff_half_bid_lower hξ hξh hw c kind G)
    _=exactExpectedPayoff N d ξ c categories G (w,w/2):=rfl

theorem exact_reference_gt_joint_underflow_cost {d ξ w : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hw : 0<w) (c : ℕ)
    (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    (hell : 0<(CommonList.iid categories N).prob (LocalUnderflow c 0))
    (hjoint : (CommonList.iid categories N).prob (BothUnderflow c)≤
      (CommonList.iid categories N).prob (LocalUnderflow c 0)/4) :
    w*(CommonList.iid categories N).prob (BothUnderflow c)<
      exactExpectedPayoff N d ξ c categories G (w,w/2) := by
  have hh:=exactExpectedPayoff_half_bid_lower (N:=N) hξ hξh hw c categories G
  have hg : 0<w*((CommonList.iid categories N).prob (LocalUnderflow c 0)-
      3*(CommonList.iid categories N).prob (BothUnderflow c)):=
    mul_pos hw (by linarith)
  nlinarith

end FCAppendix.Affine.LowBody
