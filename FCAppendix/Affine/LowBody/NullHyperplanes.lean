import FCAppendix.Affine.LowBody.NoisyRow
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem ae_affine_subtype_ne {d : ℝ} (mu : Measure (LowValue d))
    [NullSingletonClass mu] (a b t : ℝ) (ha : a≠0) :
    ∀ᵐx ∂mu,a*x.1+b≠t := by
  by_cases he : ∃x : LowValue d,a*x.1+b=t
  · obtain ⟨x,hx⟩:=he
    filter_upwards [mu.ae_ne x] with y hy heq
    apply hy
    apply Subtype.ext
    have hh : a*((y:ℝ)-(x:ℝ))=0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left ha)
  · exact ae_of_all _ (fun x hx=>he ⟨x,hx⟩)

theorem ae_iid_linear_ne {N : ℕ} {d : ℝ} (mu : Measure (LowValue d))
    [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (a : Fin N→ℝ) (j : Fin N) (hj : a j≠0) (t : ℝ) :
    ∀ᵐx ∂Measure.pi (fun _ : Fin N=>mu),(∑i,a i*(x i).1)≠t := by
  cases N with
  | zero => exact Fin.elim0 j
  | succ M =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1)=>LowValue d) j
    let f : (Fin (M+1)→LowValue d)→ℝ:=fun x=>∑i,a i*(x i).1
    have hfm : Measurable f := by dsimp [f]; fun_prop
    have hS : MeasurableSet {y : LowValue d×(Fin M→LowValue d) | f (e.symm y)≠t} :=
      (measurableSet_eq_fun (hfm.comp e.symm.measurable) measurable_const).compl
    have he (x : LowValue d) (r : Fin M→LowValue d) :
        f (e.symm (x,r))=a j*x.1+∑k,a (j.succAbove k)*(r k).1 := by
      dsimp only [f]
      rw [Fin.sum_univ_succAbove _ j]
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    have hprod : ∀ᵐy ∂mu.prod (Measure.pi (fun _ : Fin M=>mu)),f (e.symm y)≠t := by
      apply (Measure.ae_prod_iff_ae_ae hS).mpr
      apply (Measure.ae_ae_comm hS).mpr
      apply ae_of_all
      intro r
      filter_upwards [ae_affine_subtype_ne mu (a j) (∑k,a (j.succAbove k)*(r k).1) t hj] with x hx
      rwa [he]
    have hp:=measurePreserving_piFinSuccAbove (fun _ : Fin (M+1)=>mu) j
    have hh:=hp.quasiMeasurePreserving.ae hprod
    simpa only [e,MeasurableEquiv.symm_apply_apply] using hh

def actualPatternBids {N : ℕ} (kind : Fin N→Fin 4) (d b : ℝ)
    (r : Fin N→LowValue d) : Fin (N+1)→ℝ :=
  Fin.cons b (fun j=>if kind j=0 then (r j).1 else 0)

@[fun_prop] theorem continuous_actualPatternBids {N : ℕ} (kind : Fin N→Fin 4) (d : ℝ) :
    Continuous (fun t : ℝ×(Fin N→LowValue d)=>actualPatternBids kind d t.1 t.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_fst
  · by_cases hj : kind j=0
    · simp only [actualPatternBids,Fin.cons_succ,if_pos hj]
      fun_prop
    · simp only [actualPatternBids,Fin.cons_succ,if_neg hj]
      fun_prop

theorem pattern_potential_difference {N : ℕ} (kind : Fin N→Fin 4) (d κ b : ℝ)
    (r : Fin N→LowValue d) (P Q : Finset (Fin (N+1))×Finset (Fin (N+1))) :
    CompleteInformation.potential κ (actualPatternBids kind d b r) P.1 P.2-
      CompleteInformation.potential κ (actualPatternBids kind d b r) Q.1 Q.2=
    (copyCoefficient κ P 0-copyCoefficient κ Q 0)*b+
      ∑j,(if kind j=0 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0)*(r j).1 := by
  rw [potential_eq_copyCoefficient,potential_eq_copyCoefficient,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [actualPatternBids,Fin.cons_zero,Fin.cons_succ]
  have hS : (∑j,copyCoefficient κ P j.succ*(if kind j=0 then (r j).1 else 0))-
      ∑j,copyCoefficient κ Q j.succ*(if kind j=0 then (r j).1 else 0)=
      ∑j,(if kind j=0 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0)*(r j).1 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  linear_combination hS

theorem ae_pattern_ties_same_focalCopy {N : ℕ} {d κ b : ℝ} (hκ : 0<κ) (hb : b≠0)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (kind : Fin N→Fin 4) :
    ∀ᵐr ∂Measure.pi (fun _ : Fin N=>mu),∀P Q : Finset (Fin (N+1))×Finset (Fin (N+1)),
      CompleteInformation.potential κ (actualPatternBids kind d b r) P.1 P.2=
        CompleteInformation.potential κ (actualPatternBids kind d b r) Q.1 Q.2 →
      focalCopy P 0=focalCopy Q 0 := by
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro Q
  by_cases hcopy : focalCopy P 0=focalCopy Q 0
  · exact ae_of_all _ (fun _ _=>hcopy)
  · let a : Fin N→ℝ:=fun j=>if kind j=0 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0
    have hzero : copyCoefficient κ P 0-copyCoefficient κ Q 0≠0 :=
      sub_ne_zero.mpr (copyCoefficient_ne_of_focalCopy_ne hκ P Q 0 hcopy)
    by_cases ha : ∃j,a j≠0
    · obtain ⟨j,hj⟩:=ha
      filter_upwards [ae_iid_linear_ne mu a j hj (-(copyCoefficient κ P 0-copyCoefficient κ Q 0)*b)] with r hr heq
      apply False.elim (hr ?_)
      have hh:=pattern_potential_difference kind d κ b r P Q
      rw [heq,sub_self] at hh
      change 0=(copyCoefficient κ P 0-copyCoefficient κ Q 0)*b+∑j,a j*(r j).1 at hh
      linarith
    · have ha0 : ∀j,a j=0 := by simpa only [not_exists,not_not] using ha
      apply ae_of_all
      intro r heq
      have hh:=pattern_potential_difference kind d κ b r P Q
      rw [heq,sub_self] at hh
      change 0=(copyCoefficient κ P 0-copyCoefficient κ Q 0)*b+∑j,a j*(r j).1 at hh
      simp only [ha0,zero_mul,Finset.sum_const_zero,add_zero] at hh
      exact False.elim ((mul_ne_zero hzero hb) hh.symm)

end FCAppendix.Affine.LowBody
