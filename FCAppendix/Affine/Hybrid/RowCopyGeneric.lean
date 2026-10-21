import FCAppendix.Affine.Hybrid.NativeResidualPayoff
import FCAppendix.Affine.LowBody.NoisyExpectedLoss

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
variable {N : ℕ}

def rowCopyGeneric (κ b : ℝ) (omega : Fin N→RowRival) : Prop:=
  ∀P Q : Finset (Fin (N+1))×Finset (Fin (N+1)),
    CompleteInformation.potential κ (rowBids b omega) P.1 P.2=
      CompleteInformation.potential κ (rowBids b omega) Q.1 Q.2 →
    focalCopy P 0=focalCopy Q 0

lemma measurableSet_rowCopyGeneric (κ b : ℝ) :
    MeasurableSet {omega : Fin N→RowRival|rowCopyGeneric κ b omega}:=by
  simp only [rowCopyGeneric,setOf_forall]
  apply MeasurableSet.iInter
  intro P
  apply MeasurableSet.iInter
  intro Q
  by_cases hc:focalCopy P 0=focalCopy Q 0
  · simp only [hc,implies_true,setOf_true]
    exact MeasurableSet.univ
  · simp only [hc,imp_false]
    have hb:Measurable (fun omega : Fin N→RowRival=>rowBids b omega):=
      measurable_rowBids.comp (measurable_const.prodMk measurable_id)
    exact (measurableSet_eq_fun ((continuous_potential κ P).measurable.comp hb)
      ((continuous_potential κ Q).measurable.comp hb)).compl

theorem ae_iid_rowCopyGeneric {d κ b : ℝ} (hκ:0<κ) (hb:b≠0)
    (s a h : ℝ) (hs:0 ≤ s) (ha:0 ≤ a) (hh:0 ≤ h) (hsum:s+a+h=1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    ∀ᵐomega ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h (realLowLaw mu)),
      rowCopyGeneric κ b omega:=by
  let F:(Fin N→Fin 4)×(Fin N→LowValue d)→(Fin N→RowRival):=
    fun p j=>lowRowPoint (p.1 j,p.2 j)
  have hm:Measurable F:=measurable_pi_lambda _ (fun j=>measurable_lowRowPoint.comp
    (((measurable_pi_apply j).comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)))
  rw [←lowRowProfile_law s a h hs ha hh hsum mu N]
  apply (ae_map_iff hm.aemeasurable (measurableSet_rowCopyGeneric κ b)).mpr
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_rowCopyGeneric κ b).preimage hm)).mpr
  apply ae_of_all
  intro kind
  filter_upwards [ae_pattern_ties_same_focalCopy hκ hb mu kind] with r hr
  have he:rowBids b (F (kind,r))=actualPatternBids kind d b r:=by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · by_cases hj:kind j=0 <;> simp [F,rowBids,lowRowPoint,actualPatternBids,hj]
  unfold rowCopyGeneric
  rw [he]
  exact hr

end FCAppendix.Affine.Hybrid.NativeContinuation
