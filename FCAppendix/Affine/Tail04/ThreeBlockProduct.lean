import FCAppendix.Affine.Tail04.PrivateConditionalRows

noncomputable section
namespace FCAppendix.Affine.Tail04.ThreeBlockProduct
open MeasureTheory ProbabilityTheory Set Classical
open PrivateConditionalRows

section Projection
variable {I X Y : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]

def project (n : ℕ) (e : Fin n ≃ I) (f : X → Y) (x : I → X) : Fin n → Y :=
  fun j => f (x (e j))

omit [Fintype I] in
lemma measurable_project (n : ℕ) (e : Fin n ≃ I) (f : X → Y) (hf : Measurable f) :
    Measurable (project n e f) :=
  measurable_pi_lambda _ (fun j => hf.comp (measurable_pi_apply (e j)))

theorem project_law (ν : I → Measure X) [∀ i,IsProbabilityMeasure (ν i)]
    (n : ℕ) (e : Fin n ≃ I) (f : X → Y) (hf : Measurable f)
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (hρ : ∀ j,(ν (e j)).map f=ρ) :
    (Measure.pi ν).map (project n e f)=Measure.pi (fun _ : Fin n => ρ) := by
  let r : (I → X) → Fin n → X := fun x j => x (e j)
  have hr : Measurable r := measurable_pi_lambda _ (fun j => measurable_pi_apply (e j))
  have he : (Measure.pi ν).map r=Measure.pi (fun j : Fin n => ν (e j)) := by
    have h := (measurePreserving_piCongrLeft (fun j : Fin n => ν (e j)) e.symm).map_eq
    simp only [Equiv.apply_symm_apply] at h
    convert! h using 1
    congr 1
    funext x j
    simp [r,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']
  have hf' : Measurable (fun x : Fin n → X => fun j => f (x j)) :=
    measurable_pi_lambda _ (fun j => hf.comp (measurable_pi_apply j))
  calc
    _=((Measure.pi ν).map r).map (fun x : Fin n → X => fun j => f (x j)) :=
      (Measure.map_map hf' hr).symm
    _=_ := by rw [he,Measure.pi_map_pi (fun _ => hf.aemeasurable)];simp only [hρ]
end Projection

section Three
variable {I X A B C : Type*} [Fintype I] [MeasurableSpace X]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (p : I → Prop) (q : {i : I // ¬p i} → Prop)
    (a b c : ℕ) (ea : Fin a ≃ Subtype p)
    (eb : Fin b ≃ Subtype q) (ec : Fin c ≃ {i : {i : I // ¬p i} // ¬q i})
    (fa : X → A) (fb : X → B) (fc : X → C)

def rows (x : I → X) : (Fin a → A) × (Fin b → B) × (Fin c → C) :=
  (fun j => fa (x (ea j)),
    (fun j => fb (x ((eb j).val.val)),fun j => fc (x ((ec j).val.val))))

omit [Fintype I] in
lemma measurable_rows (ha : Measurable fa) (hb : Measurable fb) (hc : Measurable fc) :
    Measurable (rows p q a b c ea eb ec fa fb fc) :=
  (measurable_pi_lambda _ (fun j => ha.comp (measurable_pi_apply ((ea j).val)))).prodMk
    ((measurable_pi_lambda _ (fun j => hb.comp (measurable_pi_apply ((eb j).val.val)))).prodMk
      (measurable_pi_lambda _ (fun j => hc.comp (measurable_pi_apply ((ec j).val.val)))))

theorem rows_law (ν : I → Measure X) [∀ i,IsProbabilityMeasure (ν i)]
    (ha : Measurable fa) (hb : Measurable fb) (hc : Measurable fc)
    (ρa : Measure A) (ρb : Measure B) (ρc : Measure C)
    [IsProbabilityMeasure ρa] [IsProbabilityMeasure ρb] [IsProbabilityMeasure ρc]
    (hρa : ∀ j,(ν (ea j)).map fa=ρa)
    (hρb : ∀ j,(ν ((eb j).val.val)).map fb=ρb)
    (hρc : ∀ j,(ν ((ec j).val.val)).map fc=ρc) :
    (Measure.pi ν).map (rows p q a b c ea eb ec fa fb fc)=
      (Measure.pi (fun _ : Fin a => ρa)).prod
        ((Measure.pi (fun _ : Fin b => ρb)).prod (Measure.pi (fun _ : Fin c => ρc))) := by
  let νr : {i : I // ¬p i} → Measure X := fun i => ν i
  let νs : {i : {i : I // ¬p i} // ¬q i} → Measure X := fun i => ν i.val.val
  let splitA := blockSplit p a ea fa
  let splitB := blockSplit q b eb fb
  let finish : ({i : I // ¬p i} → X) → (Fin b → B) × (Fin c → C) :=
    fun x => ((splitB x).1,project c ec fc (splitB x).2)
  have hsplitA : Measurable splitA := measurable_blockSplit p a ea fa ha
  have hsplitB : Measurable splitB := measurable_blockSplit q b eb fb hb
  have hfinish : Measurable finish :=
    hsplitB.fst.prodMk ((measurable_project c ec fc hc).comp hsplitB.snd)
  have hA := blockSplit_law ν p a ea fa ha ρa hρa
  have hB := blockSplit_law νr q b eb fb hb ρb hρb
  have hC := project_law νs c ec fc hc ρc hρc
  have hf : (Measure.pi νr).map finish=
      (Measure.pi (fun _ : Fin b => ρb)).prod (Measure.pi (fun _ : Fin c => ρc)) := by
    calc
      _=((Measure.pi νr).map splitB).map (Prod.map id (project c ec fc)) := by
        rw [Measure.map_map (measurable_id.prodMap (measurable_project c ec fc hc)) hsplitB]
        rfl
      _=_ := by
        rw [hB,←Measure.map_prod_map _ _ measurable_id (measurable_project c ec fc hc),
          Measure.map_id,hC]
  calc
    _=((Measure.pi ν).map splitA).map (Prod.map id finish) := by
      rw [Measure.map_map (measurable_id.prodMap hfinish) hsplitA]
      rfl
    _=_ := by
      rw [hA,←Measure.map_prod_map _ _ measurable_id hfinish,Measure.map_id,hf]

end Three
end FCAppendix.Affine.Tail04.ThreeBlockProduct
