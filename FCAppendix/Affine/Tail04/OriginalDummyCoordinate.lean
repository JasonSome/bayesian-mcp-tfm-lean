import FCAppendix.Affine.Tail04.OriginalActiveCrossingCarrier

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalDummyCoordinate
open MeasureTheory Set Classical
open OriginalActiveCrossingCarrier

variable {X : Type*} [MeasurableSpace X] {H : ℕ}

lemma restore_zero (x : X) (row : Fin H→ X) : restore (0 : Fin (H+1)) x row=Fin.cons (α:=fun _ : Fin (H+1) => X) x row := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact restore_self 0 x row
  · have h := congrArg (fun p : X×(Fin H→ X) => p.2 k)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (H+1) => X) 0).apply_symm_apply (x,row))
    change restore (0 : Fin (H+1)) x row ((0 : Fin (H+1)).succAbove k)=row k at h
    simpa only [Fin.succAbove_zero,Fin.cons_succ] using h

theorem integral_update_zero (ρ : Measure X) [IsProbabilityMeasure ρ]
    (x : X) (f : (Fin (H+1)→ X)→ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ row,‖f row‖≤ C) :
    (∫ row,f (Function.update row 0 x) ∂Measure.pi (fun _ : Fin (H+1) => ρ))=
      ∫ row,f (Fin.cons (α:=fun _ : Fin (H+1) => X) x row) ∂Measure.pi (fun _ : Fin H => ρ) := by
  have hm : Measurable (fun row : Fin (H+1)→ X => Function.update row 0 x) :=
    Resample.measurable_update_pair 0 |>.comp (measurable_const.prodMk measurable_id)
  change (∫ row,(f ∘ (fun row : Fin (H+1)→X => Function.update row 0 x)) row
    ∂Measure.pi (fun _ : Fin (H+1) => ρ))=_
  rw [integral_delete ρ 0 _ (hf.comp hm) C (fun row => hC _)]
  simp only [Function.comp_def]
  simp_rw [restore_zero]
  have he (y : X) (row : Fin H→ X) : Function.update (Fin.cons (α:=fun _ : Fin (H+1) => X) y row) 0 x=Fin.cons (α:=fun _ : Fin (H+1) => X) x row := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simpa only [Fin.cons_succ] using Function.update_of_ne (Fin.succ_ne_zero k) x
        (Fin.cons (α:=fun _ : Fin (H+1) => X) y row)
  simp_rw [he]
  simp

theorem integral_cons_tail (ρ : Measure X) [IsProbabilityMeasure ρ]
    (x : X) (f : (Fin (H+1)→ X)→ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ row,‖f row‖≤ C) :
    (∫ row,f (Fin.cons x (fun j => row j.succ))
      ∂Measure.pi (fun _ : Fin (H+1) => ρ))=
        ∫ row,f (Fin.cons (α:=fun _ : Fin (H+1) => X) x row) ∂Measure.pi (fun _ : Fin H => ρ) := by
  have he (row : Fin (H+1)→ X) : Fin.cons x (fun j => row j.succ)=Function.update row 0 x := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  simp_rw [he]
  exact integral_update_zero ρ x f hf C hC

end FCAppendix.Affine.Tail04.OriginalDummyCoordinate
