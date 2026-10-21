import FCAppendix.Affine.LowBody.LiteralCarrierBounds
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set
variable {A : Type*} [MeasurableSpace A] {N : ℕ}

lemma measurePreserving_cons_iid (rho : Measure RowRival) [IsProbabilityMeasure rho] :
    MeasurePreserving (fun p : RowRival×(Fin N→RowRival)=>Fin.cons p.1 p.2)
      (rho.prod (Measure.pi (fun _ : Fin N=>rho)))
      (Measure.pi (fun _ : Fin (N+1)=>rho)) := by
  have hp:=(measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>rho) 0).symm
  convert hp using 1
  funext p
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

lemma measurePreserving_carrierRow (Gamma : Measure A) [IsFiniteMeasure Gamma]
    (rho : Measure RowRival) [IsProbabilityMeasure rho] :
    MeasurePreserving
      (fun q : (Fin N→RowRival)×(A×RowRival)=>(q.2.1,(Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival)))
      ((Measure.pi (fun _ : Fin N=>rho)).prod (Gamma.prod rho))
      (Gamma.prod (Measure.pi (fun _ : Fin (N+1)=>rho))) := by
  let nu:=Measure.pi (fun _ : Fin N=>rho)
  have hrot:=(measurePreserving_prodAssoc Gamma rho nu).comp
    (Measure.measurePreserving_swap (μ:=nu) (ν:=Gamma.prod rho))
  exact ((MeasurePreserving.id Gamma).prod (measurePreserving_cons_iid rho)).comp hrot

theorem integral_carrierRow (Gamma : Measure A) [IsFiniteMeasure Gamma]
    (rho : Measure RowRival) [IsProbabilityMeasure rho]
    (f : A×(Fin (N+1)→RowRival)→ℝ) (hf : Measurable f)
    (hi : Integrable f (Gamma.prod (Measure.pi (fun _ : Fin (N+1)=>rho)))) :
    (∫q : (Fin N→RowRival)×(A×RowRival),f (q.2.1,Fin.cons q.2.2 q.1)
      ∂(Measure.pi (fun _ : Fin N=>rho)).prod (Gamma.prod rho))=
      ∫t,∫omega,f (t,omega) ∂Measure.pi (fun _ : Fin (N+1)=>rho) ∂Gamma := by
  have hp:=measurePreserving_carrierRow (N:=N) Gamma rho
  calc
    _=∫p,f p ∂Gamma.prod (Measure.pi (fun _ : Fin (N+1)=>rho)) := by
      rw [←hp.map_eq]
      exact (integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _=_:=integral_prod _ hi

theorem integral_carrierRow_of_cons_integrable (Gamma : Measure A) [IsFiniteMeasure Gamma]
    (rho : Measure RowRival) [IsProbabilityMeasure rho]
    (f : A×(Fin (N+1)→RowRival)→ℝ) (hf : Measurable f)
    (hi : Integrable (fun q : (Fin N→RowRival)×(A×RowRival)=>f (q.2.1,Fin.cons q.2.2 q.1))
      ((Measure.pi (fun _ : Fin N=>rho)).prod (Gamma.prod rho))) :
    (∫q : (Fin N→RowRival)×(A×RowRival),f (q.2.1,Fin.cons q.2.2 q.1)
      ∂(Measure.pi (fun _ : Fin N=>rho)).prod (Gamma.prod rho))=
      ∫t,∫omega,f (t,omega) ∂Measure.pi (fun _ : Fin (N+1)=>rho) ∂Gamma := by
  have hp:=measurePreserving_carrierRow (N:=N) Gamma rho
  apply integral_carrierRow Gamma rho f hf
  rw [←hp.map_eq]
  exact (integrable_map_measure hf.aestronglyMeasurable hp.measurable.aemeasurable).mpr hi

end FCAppendix.Affine.LowBody
