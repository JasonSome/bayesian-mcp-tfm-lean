import FCAppendix.Affine.LowBody.PureTemplate
import FCAppendix.Affine.LowBody.PureCrossing

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma potential_update_focal (κ : ℝ) (b : ι→ℝ) (i : ι) (x : ℝ)
    (P : Finset ι × Finset ι) :
    CompleteInformation.potential κ (Function.update b i x) P.1 P.2=
      CompleteInformation.potential κ b P.1 P.2+copyCoefficient κ P i*(x-b i) := by
  rw [potential_eq_copyCoefficient,potential_eq_copyCoefficient]
  rw [←Finset.add_sum_erase Finset.univ (fun j=>copyCoefficient κ P j*Function.update b i x j)
    (Finset.mem_univ i),
    ←Finset.add_sum_erase Finset.univ (fun j=>copyCoefficient κ P j*b j) (Finset.mem_univ i)]
  have he : (∑j∈Finset.univ.erase i,copyCoefficient κ P j*Function.update b i x j)=
      ∑j∈Finset.univ.erase i,copyCoefficient κ P j*b j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,Function.update_self]
  ring

omit [Fintype ι] in
lemma focalCopy_mono_of_coefficient {κ : ℝ} (hκ : 0<κ)
    (P Q : Finset ι × Finset ι) (i : ι)
    (h : copyCoefficient κ P i≤copyCoefficient κ Q i) : focalCopy P i≤focalCopy Q i := by
  rw [copyCoefficient_eq,copyCoefficient_eq] at h
  generalize focalCopy P i=x at *
  generalize focalCopy Q i=y at *
  fin_cases x <;> fin_cases y <;> simp_all [Fin.ext_iff] <;> linarith

namespace PureTemplate

theorem focalCopy_selection_mono (T : PureTemplate ι) {κ : ℝ} (hκ : 0<κ)
    (b : ι→ℝ) (i : ι) (x : ℝ) (hx : b i<x) :
    focalCopy (T.selection κ b) i≤focalCopy (T.selection κ (Function.update b i x)) i := by
  let P:=T.selection κ b
  let Q:=T.selection κ (Function.update b i x)
  have hP:=T.selection_feasible κ b
  have hQ:=T.selection_feasible κ (Function.update b i x)
  have hm0:=T.selection_max κ b Q hQ
  have hm1:=T.selection_max κ (Function.update b i x) P hP
  rw [potential_update_focal,potential_update_focal] at hm1
  have hcoeff : copyCoefficient κ P i≤copyCoefficient κ Q i := by
    dsimp only [P,Q] at *
    nlinarith
  exact focalCopy_mono_of_coefficient hκ P Q i hcoeff

end PureTemplate

omit [Fintype ι] in

theorem purePayoff_loss_le_duplicate {κ w : ℝ}
    (b : ι→ℝ) (i : ι) (hbw : b i≤w)
    (P Q : Finset ι × Finset ι) (hcopy : focalCopy P i≤focalCopy Q i) :
    purePayoff κ w b P i-purePayoff κ w b Q i≤
      if focalCopy P i≠2 ∧ focalCopy Q i=2 then (2*κ-1)*b i else 0 := by
  unfold purePayoff
  generalize focalCopy P i=x at *
  generalize focalCopy Q i=y at *
  fin_cases x <;> fin_cases y <;> simp_all [Fin.ext_iff] <;> nlinarith

end FCAppendix.Affine.LowBody
