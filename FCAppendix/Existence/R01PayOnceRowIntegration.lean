import FCAppendix.Existence.R01PayOnceFloor
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace FCAppendix.Existence.Distributional
open MeasureTheory ProbabilityTheory Set

theorem rowLaw_eq_pi {X : Type*} [MeasurableSpace X] (N : ℕ) (mu : ProbabilityMeasure X) :
    (rowLaw N mu : Measure (Fin N → X))=Measure.pi (fun _ : Fin N => (mu : Measure X)) := by
  induction N with
  | zero =>
    change Measure.dirac (fun i : Fin 0 => Fin.elim0 i)=_
    rw [Measure.pi_of_empty]
    congr 1
  | succ N ih =>
    change (((mu : Measure X).prod (rowLaw N mu : Measure (Fin N → X))).map
      (fun p : X × (Fin N → X) => Fin.cons (α := fun _ : Fin (N+1) => X) p.1 p.2)) = _
    rw [ih]
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => (mu : Measure X)) 0).symm
    convert hmp.map_eq using 1
    congr 1
    funext p
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [MeasurableEquiv.piFinSuccAbove]

end FCAppendix.Existence.Distributional
