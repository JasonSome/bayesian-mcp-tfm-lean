import FCAppendix.Affine.UniformFinite.ActualContinuation
import FCAppendix.Affine.UniformFinite.ProductPayoff

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory Classical
open Uniform07 (Row)
open scoped BigOperators
open Existence.PayOnceBounded (positiveSupport mem_positiveSupport)

section Marginal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMarginal_eq_exposure {xi z U : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (hz : 0< z) (hguard : (1-xi)*U≤ z) (c : ℕ) (b : ι→ℝ)
    (_hb : ∀a,0≤ b a) (hbU : ∀a,b a≤ U)
    (hclear : (∑a,ClippedResidual.exposure xi z (b a))=(c:ℝ)) :
    EqualCapacity.positiveMarginal xi c b=fun a=> ClippedResidual.exposure xi z (b a) := by
  let S := positiveSupport b
  let p : ι→ℝ := fun a=> ClippedResidual.exposure xi z (b a)
  have hp0 (a : ι) : 0≤ p a := ClippedResidual.exposure_nonneg hxi hz
  have hp1 (a : ι) : p a≤1 := ClippedResidual.exposure_le_one _ _ _
  have hzero (a : ι) (ha : a∉S) : p a=0 := by
    have hn : ¬0< b a := by simpa only [S,mem_positiveSupport] using ha
    exact ClippedResidual.exposure_zero ((le_of_not_gt hn).trans hz.le)
  have hsum : (∑a : S,p a)=(c:ℝ) := by
    calc
      _ = ∑a∈S,p a := Finset.sum_attach S p
      _ = ∑a,p a := Finset.sum_subset (Finset.subset_univ S) (fun a _ ha=> hzero a ha)
      _ = (c:ℝ) := hclear
  have hcle : c≤ Fintype.card S := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun a (_ : a∈(Finset.univ : Finset S))=> hp1 a)
    rw [hsum] at h
    exact_mod_cast (show (c:ℝ)≤ Fintype.card S by simpa using h)
  have hthreshold := ClippedResidual.exposure_threshold hxi hxi1 hz hguard
    (fun a : S=> b a) (fun a=> hbU a)
  have hkernel : EqualCapacity.IsKernel xi c (fun a : S=> b a) (fun a : S=> p a) := by
    refine ⟨fun a=> hp0 a,fun a=> hp1 a,?_,z,hz.le,hthreshold⟩
    rw [Nat.min_eq_left hcle]
    exact hsum
  have hu := EqualCapacity.isKernel_unique hxi c (fun a : S=> b a)
    (fun a=>(mem_positiveSupport b a).mp a.2)
    (EqualCapacity.kernelMarginal xi c (fun a : S=> b a)) (fun a : S=> p a)
    (EqualCapacity.kernelMarginal_spec hxi hxi1 c (fun a : S=> b a)
      (fun a=>(mem_positiveSupport b a).mp a.2)) hkernel
  funext a
  by_cases ha : a∈S
  · change EqualCapacity.onSupport xi c S b a=p a
    rw [EqualCapacity.onSupport,dif_pos ha]
    exact congrFun hu ⟨a,ha⟩
  · change EqualCapacity.onSupport xi c S b a=p a
    rw [EqualCapacity.onSupport_outside xi c S b a ha,hzero a ha]

end Marginal

theorem equalLaw_eq_conditionalCompletion {M : ℕ} (i : Row)
    (row : Source.CountRow M) (b : Fin M→ℝ) {z : ℝ}
    (hz : 0< z) (hguard : (1-Uniform05.xi i)*Uniform05.cap i≤ z)
    (hb : ∀a∈row.lower,0≤ b a) (hbU : ∀a∈row.lower,b a≤ Uniform05.cap i)
    (hclear : (∑a,ClippedResidual.exposure (Uniform05.xi i) z (Source.lowerBids row b a))=
      (Source.small row : ℝ)) :
    equalLaw i row b=Literal.conditionalCompletion (Uniform05.xi i) z
      (Source.lowerBids row b) ∅ := by
  have hl0 (a : Fin M) : 0≤ Source.lowerBids row b a := by
    by_cases ha : a∈row.lower <;> simp only [Source.lowerBids,ha,if_true,if_false]
    · exact hb a ha
    · exact le_rfl
  have hlU (a : Fin M) : Source.lowerBids row b a≤ Uniform05.cap i := by
    by_cases ha : a∈row.lower
    · simpa [Source.lowerBids,ha] using hbU a ha
    · simp [Source.lowerBids,ha,(Uniform05.cap_pos i).le]
  have hp := positiveMarginal_eq_exposure (Uniform05.xi_range i).1 (Uniform05.xi_range i).2
    hz hguard (Source.small row) (Source.lowerBids row b) hl0 hlU hclear
  unfold equalLaw equalLottery Literal.conditionalCompletion Literal.largeCompletion Literal.completion
  rw [hp]
  have he : ClippedResidual.smallMarginal (Uniform05.xi i) z (Source.lowerBids row b) ∅=
      fun a=> ClippedResidual.exposure (Uniform05.xi i) z (Source.lowerBids row b a) := by
    funext a
    simp [ClippedResidual.smallMarginal]
  rw [he]
  have hm (P : FiniteLaw (Finset (Fin M))) : P.map (fun S=>(∅ : Finset (Fin M))∪S)=P := by
    apply FiniteLaw.ext_expect
    intro f
    rw [FiniteLaw.expect_map]
    simp only [Finset.empty_union]
  rw [hm]

theorem rowPayoff_equal_of_clearing {M : ℕ} [NeZero M] (i : Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M) (v : ℝ)
    (b : Fin M→ℝ) (focal : Fin M) (hfocal : focal∈row.lower)
    (heq : Source.residual row 0=Source.residual row 1) {z : ℝ}
    (hz : 0< z) (hguard : (1-Uniform05.xi i)*Uniform05.cap i≤ z)
    (hb : ∀a∈row.lower,0≤ b a) (hbU : ∀a∈row.lower,b a≤ Uniform05.cap i)
    (hclear : (∑a,ClippedResidual.exposure (Uniform05.xi i) z (Source.lowerBids row b a))=
      (Source.small row : ℝ)) :
    rowPayoff i G row v b focal=productPayoff (Uniform05.xi i) v z (b focal) := by
  have hrem : ClippedResidual.remainingDemand (Uniform05.xi i)
      (Source.lowerBids row b) ∅ z=(Source.small row : ℝ) := by
    simpa [ClippedResidual.remainingDemand,ClippedResidual.smallMarginal] using hclear
  have hs := Literal.conditional_first_copy (Uniform05.xi_range i).1 hz
    (Source.lowerBids row b) ∅ (Source.small row) hrem focal
  have hd := Literal.conditional_duplicate_copy (Uniform05.xi_range i).1 hz
    (Source.lowerBids row b) ∅ (Source.small row) hrem focal
  simp only [Finset.notMem_empty,if_false,Source.lowerBids_of_mem row b hfocal] at hs hd
  rw [rowPayoff_success_duplicate]
  unfold successProbability duplicateProbability
  rw [continuation_equal i G row b heq,
    equalLaw_eq_conditionalCompletion i row b hz hguard hb hbU hclear,hs,hd]
  unfold productPayoff Uniform05.xi
  ring

end FCAppendix.Affine.UniformFinite
