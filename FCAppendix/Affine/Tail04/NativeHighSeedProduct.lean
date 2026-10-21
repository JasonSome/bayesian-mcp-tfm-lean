import FCAppendix.Affine.Tail04.NativeSamplerCountLaw
import FCAppendix.Affine.Tail04.NoisyNativeFiberProduct

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeHighSeedProduct
open MeasureTheory ProbabilityTheory Set Classical
open NativeLocalPolicy

def highPair (s : Fin 2 → Seed) : unitInterval×unitInterval := ((s 0).1,(s 1).1)

lemma measurable_highPair : Measurable highPair :=
  (measurable_fst.comp (measurable_pi_apply 0)).prodMk
    (measurable_fst.comp (measurable_pi_apply 1))

theorem highPair_preserves : MeasurePreserving highPair
    (Measure.pi (fun _ : Fin 2 => seedLaw))
    ((volume : Measure unitInterval).prod volume) := by
  let p : (Fin 2 → Seed) → Fin 2 → unitInterval := fun s j => (s j).1
  have hp : Measurable p := measurable_pi_lambda _
    (fun j => measurable_fst.comp (measurable_pi_apply j))
  have hm : (Measure.pi (fun _ : Fin 2 => seedLaw)).map p=
      Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)) := by
    rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
    simp only [seedLaw,(measurePreserving_fst (μ:=(volume : Measure unitInterval))
      (ν:=(volume : Measure unitInterval))).map_eq]
  exact (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure unitInterval))).comp ⟨hp,hm⟩

def highRoute (z : (Fin 2 → Seed)×Equiv.Perm (Fin 2)) :
    (unitInterval×unitInterval)×Equiv.Perm (Fin 2) := (highPair z.1,z.2)

theorem highRoute_preserves : MeasurePreserving highRoute
    ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (Game.permLaw 2))
    (((volume : Measure unitInterval).prod volume).prod (Game.permLaw 2)) :=
  highPair_preserves.prod (MeasurePreserving.id _)

theorem highOnly_preserves : MeasurePreserving (highPair ∘ Prod.fst)
    ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (Game.permLaw 2))
    ((volume : Measure unitInterval).prod volume) :=
  highPair_preserves.comp (measurePreserving_fst (μ:=Measure.pi (fun _ : Fin 2 => seedLaw))
    (ν:=Game.permLaw 2))

section Cross
variable {X Y U V : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace U] [MeasurableSpace V]

def crossPair (z : (X×Y)×(U×V)) : (X×U)×(Y×V) := ((z.1.1,z.2.1),(z.1.2,z.2.2))

lemma measurable_crossPair : Measurable (crossPair (X:=X) (Y:=Y) (U:=U) (V:=V)) :=
  (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
    (measurable_fst.snd.prodMk measurable_snd.snd)

theorem crossPair_preserves (μ : Measure X) (ν : Measure Y) (α : Measure U) (β : Measure V)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite α] [SigmaFinite β] :
    MeasurePreserving crossPair ((μ.prod ν).prod (α.prod β)) ((μ.prod α).prod (ν.prod β)) := by
  let mid : Y×(U×V) → U×(Y×V) := fun z => (z.2.1,(z.1,z.2.2))
  have hm : MeasurePreserving mid (ν.prod (α.prod β)) (α.prod (ν.prod β)) :=
    (measurePreserving_prodAssoc α ν β).comp
      (((Measure.measurePreserving_swap (μ:=ν) (ν:=α)).prod (MeasurePreserving.id β)).comp
        (measurePreserving_prodAssoc ν α β).symm)
  exact (measurePreserving_prodAssoc μ α (ν.prod β)).symm.comp
    (((MeasurePreserving.id μ).prod hm).comp (measurePreserving_prodAssoc μ ν (α.prod β)))

end Cross

section PrivateRows
variable {m c : ℕ} (D : NativeLocalPolicy.Data m c) (H0 H1 : Fin (m+1))

def pairRows (z :
    (EqualPrivateUpper.Row H0.val D.E.R D.E.Rp D.E.H×
      EqualPrivateUpper.Row H1.val D.E.R D.E.Rp D.E.H)×
      ((Fin 2 → Seed)×Equiv.Perm (Fin 2))) :
    (EqualPrivateUpper.Row H0.val D.E.R D.E.Rp D.E.H×unitInterval)×
      (EqualPrivateUpper.Row H1.val D.E.R D.E.Rp D.E.H×unitInterval) :=
  ((z.1.1,(z.2.1 0).1),(z.1.2,(z.2.1 1).1))

theorem pairRows_preserves : MeasurePreserving (pairRows D H0 H1)
    (((D.originalPrivateRow H0 : Measure _).prod (D.originalPrivateRow H1 : Measure _)).prod
      ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (Game.permLaw 2)))
    (NativeSamplerCountLaw.pairLaw D H0 H1) :=
  (crossPair_preserves (ProbabilityMeasure.toMeasure (D.originalPrivateRow H0))
    (ProbabilityMeasure.toMeasure (D.originalPrivateRow H1))
    (volume : Measure unitInterval) (volume : Measure unitInterval)).comp
      ((MeasurePreserving.id _).prod highOnly_preserves)

end PrivateRows
end FCAppendix.Affine.Tail04.NativeHighSeedProduct
