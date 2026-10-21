import FCAppendix.Affine.Tail04.OrderedNativePayoffPartialLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffPartialReduction
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeHighSeedProduct NativeHighExperiment NativePartialExperiment
open EqualPrivateSignal EqualPrivateUpper PrivateRowSorting NativePartialProductReduction
open OrderedNativePayoffPartialExperiment

section OneSide
variable {m c : ℕ} (K : NativeLocalPolicy.Data m c)
  (ρ : ProbabilityMeasure (Ici K.E.H ⊕ Icc K.E.R K.E.Rp))
  (A : ℕ) (H0 H1 own other : Fin (m+1)) (physical : Fin 2) (Q : PublicScenario.Data) (side low : Bool)
  (hcard : own.val=(ownH H0 H1 side).val+1)
  (v : ℝ) (price : Icc K.E.R K.E.Rp) (b : Fin A → Icc (1:ℝ) K.E.U) (publicSeed : unitInterval)

def insertedValue (x : RawPayload K H0 H1) : ℝ :=
  let p := ownPayload K H0 H1 side x
  value K A own other physical Q low (Fin.cast hcard.symm 0) v price b
    ((Fin.cons (α:=fun _=>Ici K.E.H⊕Icc K.E.R K.E.Rp) (Sum.inr price) p.1) ∘ Fin.cast hcard) publicSeed p.2

lemma measurable_value_row_seed (j' : Fin own.val) : Measurable
    (fun x : Row own.val K.E.R K.E.Rp K.E.H×unitInterval =>
      value K A own other physical Q low j' v price b x.1 publicSeed x.2) := by
  have hi := measurable_inclusion K A own other physical Q low j'
  have hp : Measurable (fun x : Row own.val K.E.R K.E.Rp K.E.H×unitInterval =>
      (b,(x.1,(publicSeed,x.2)))) :=
    measurable_const.prodMk (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hh := hi.comp hp
  exact (measurable_const (a:=v-(price:ℝ))).mul hh

lemma measurable_insertedValue : Measurable
    (insertedValue K A H0 H1 own other physical Q side low hcard v price b publicSeed) := by
  have hp := measurable_ownPayload K H0 H1 side
  have hr : Measurable (fun x : RawPayload K H0 H1 =>
      (Fin.cons (α:=fun _=>Ici K.E.H⊕Icc K.E.R K.E.Rp) (Sum.inr price) (ownPayload K H0 H1 side x).1) ∘ Fin.cast hcard) := by
    apply measurable_pi_lambda
    intro k
    dsimp only [Function.comp_apply]
    generalize Fin.cast hcard k=q
    refine Fin.cases measurable_const (fun l => (measurable_pi_apply l).comp hp.fst) q
  have hout := measurable_value_row_seed K A own other physical Q low v price b publicSeed (Fin.cast hcard.symm 0)
  have hin : Measurable (fun x : RawPayload K H0 H1 =>
      ((Fin.cons (α:=fun _=>Ici K.E.H⊕Icc K.E.R K.E.Rp) (Sum.inr price)
        (ownPayload K H0 H1 side x).1) ∘ Fin.cast hcard,(ownPayload K H0 H1 side x).2)) :=
    hr.prodMk hp.snd
  have hc := hout.comp hin
  exact hc

theorem payload_integral :
    (∫ x,insertedValue K A H0 H1 own other physical Q side low hcard v price b publicSeed x
      ∂rawPayloadLaw K ρ H0 H1)=
      ∫ row,∫ u : unitInterval,
        value K A own other physical Q low (Fin.cast hcard.symm 0) v price b
          (Function.update row (Fin.cast hcard.symm 0) (Sum.inr price)) publicSeed u
            ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure (originalIid K.E own.val ρ)) := by
  let f : Row own.val K.E.R K.E.Rp K.E.H×unitInterval → ℝ := fun x =>
    value K A own other physical Q low (Fin.cast hcard.symm 0) v price b x.1 publicSeed x.2
  have hf : Measurable f := measurable_value_row_seed K A own other physical Q low v price b publicSeed (Fin.cast hcard.symm 0)
  have hb (x) : ‖f x‖≤|v|+K.E.Rp := value_bound K A own other physical Q low (Fin.cast hcard.symm 0) v price b x.1 publicSeed x.2
  let ins : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H →
      Row own.val K.E.R K.E.Rp K.E.H := fun row =>
    (Fin.cons (α:=fun _=>Ici K.E.H⊕Icc K.E.R K.E.Rp) (Sum.inr price) row) ∘ Fin.cast hcard
  have hins : Measurable ins := by
    apply measurable_pi_lambda
    intro k
    dsimp only [ins,Function.comp_apply]
    generalize Fin.cast hcard k=q
    refine Fin.cases measurable_const (fun l => measurable_pi_apply l) q
  let upd := fun row : Row own.val K.E.R K.E.Rp K.E.H =>
    Function.update row (Fin.cast hcard.symm 0) (Sum.inr price)
  have hupd : Measurable upd := measurable_update_left
  have hi := integrable_bounded ((ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)).prod (volume : Measure unitInterval))
    (fun x => f (ins x.1,x.2)) (hf.comp (hins.prodMap measurable_id)) (|v|+K.E.Rp)
      (fun x => hb (ins x.1,x.2))
  calc
    _=∫ x : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×unitInterval,
        f (ins x.1,x.2) ∂(ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)).prod volume :=
      (ownPayload_preserves K ρ H0 H1 side).integral_comp_ae_real hi.aestronglyMeasurable
    _=∫ row,∫ u : unitInterval,f (ins row,u) ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)) := integral_prod _ hi
    _=∫ u : unitInterval,∫ row,f (ins row,u) ∂(ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)) :=
      integral_swap_bounded (ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)) volume _ (hf.comp (hins.prodMap measurable_id)) _
        (fun x => hb (ins x.1,x.2))
    _=∫ u : unitInterval,∫ row,f (upd row,u) ∂(ProbabilityMeasure.toMeasure (originalIid K.E own.val ρ)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun u =>
        (integral_update_cast hcard (ProbabilityMeasure.toMeasure ρ) (Sum.inr price)
          (fun row => f (row,u)) (hf.comp (measurable_id.prodMk measurable_const))
          (|v|+K.E.Rp) (fun row => hb (row,u))).symm
    _=_ := (integral_swap_bounded (ProbabilityMeasure.toMeasure (originalIid K.E own.val ρ)) volume _ (hf.comp (hupd.prodMap measurable_id)) _
      (fun x => hb (upd x.1,x.2))).symm

end OneSide
end FCAppendix.Affine.Tail04.OrderedNativePayoffPartialReduction
